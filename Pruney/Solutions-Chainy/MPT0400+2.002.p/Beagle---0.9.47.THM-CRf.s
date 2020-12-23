%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:38 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   35 (  44 expanded)
%              Number of leaves         :   16 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :   58 (  90 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k2_xboole_0 > #nlpp > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_setfam_1(A,B)
          & r1_setfam_1(B,C) )
       => r1_setfam_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_setfam_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_18,plain,(
    r1_setfam_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_1'(A_6,B_7),A_6)
      | r1_setfam_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    r1_setfam_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ! [A_6,B_7,C_16] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_16),B_7)
      | ~ r2_hidden(C_16,A_6)
      | ~ r1_setfam_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_23,plain,(
    ! [C_28,A_29,B_30] :
      ( r1_tarski(C_28,'#skF_2'(A_29,B_30,C_28))
      | ~ r2_hidden(C_28,A_29)
      | ~ r1_setfam_1(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_37,plain,(
    ! [C_28,A_29,B_30] :
      ( k2_xboole_0(C_28,'#skF_2'(A_29,B_30,C_28)) = '#skF_2'(A_29,B_30,C_28)
      | ~ r2_hidden(C_28,A_29)
      | ~ r1_setfam_1(A_29,B_30) ) ),
    inference(resolution,[status(thm)],[c_23,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_57,plain,(
    ! [A_41,A_42,B_43,B_44] :
      ( r1_tarski(A_41,'#skF_2'(A_42,B_43,k2_xboole_0(A_41,B_44)))
      | ~ r2_hidden(k2_xboole_0(A_41,B_44),A_42)
      | ~ r1_setfam_1(A_42,B_43) ) ),
    inference(resolution,[status(thm)],[c_23,c_2])).

tff(c_10,plain,(
    ! [A_6,B_7,D_15] :
      ( ~ r1_tarski('#skF_1'(A_6,B_7),D_15)
      | ~ r2_hidden(D_15,B_7)
      | r1_setfam_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_171,plain,(
    ! [B_66,A_70,B_68,A_67,B_69] :
      ( ~ r2_hidden('#skF_2'(A_67,B_66,k2_xboole_0('#skF_1'(A_70,B_69),B_68)),B_69)
      | r1_setfam_1(A_70,B_69)
      | ~ r2_hidden(k2_xboole_0('#skF_1'(A_70,B_69),B_68),A_67)
      | ~ r1_setfam_1(A_67,B_66) ) ),
    inference(resolution,[status(thm)],[c_57,c_10])).

tff(c_185,plain,(
    ! [A_71,B_72,B_73,A_74] :
      ( r1_setfam_1(A_71,B_72)
      | ~ r2_hidden(k2_xboole_0('#skF_1'(A_71,B_72),B_73),A_74)
      | ~ r1_setfam_1(A_74,B_72) ) ),
    inference(resolution,[status(thm)],[c_8,c_171])).

tff(c_219,plain,(
    ! [A_82,B_83,A_81,B_80,A_84] :
      ( r1_setfam_1(A_82,B_83)
      | ~ r2_hidden('#skF_2'(A_81,B_80,'#skF_1'(A_82,B_83)),A_84)
      | ~ r1_setfam_1(A_84,B_83)
      | ~ r2_hidden('#skF_1'(A_82,B_83),A_81)
      | ~ r1_setfam_1(A_81,B_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_185])).

tff(c_225,plain,(
    ! [A_85,B_86,B_87,A_88] :
      ( r1_setfam_1(A_85,B_86)
      | ~ r1_setfam_1(B_87,B_86)
      | ~ r2_hidden('#skF_1'(A_85,B_86),A_88)
      | ~ r1_setfam_1(A_88,B_87) ) ),
    inference(resolution,[status(thm)],[c_8,c_219])).

tff(c_232,plain,(
    ! [A_89,A_90] :
      ( r1_setfam_1(A_89,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_89,'#skF_5'),A_90)
      | ~ r1_setfam_1(A_90,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_225])).

tff(c_238,plain,(
    ! [A_91] :
      ( ~ r1_setfam_1(A_91,'#skF_4')
      | r1_setfam_1(A_91,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_12,c_232])).

tff(c_14,plain,(
    ~ r1_setfam_1('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_243,plain,(
    ~ r1_setfam_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_238,c_14])).

tff(c_248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_243])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:22:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.24  
% 2.07/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.24  %$ r2_hidden > r1_tarski > r1_setfam_1 > k2_xboole_0 > #nlpp > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 2.07/1.24  
% 2.07/1.24  %Foreground sorts:
% 2.07/1.24  
% 2.07/1.24  
% 2.07/1.24  %Background operators:
% 2.07/1.24  
% 2.07/1.24  
% 2.07/1.24  %Foreground operators:
% 2.07/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.24  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.07/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.24  tff('#skF_5', type, '#skF_5': $i).
% 2.07/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.07/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.07/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.07/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.07/1.24  
% 2.07/1.25  tff(f_52, negated_conjecture, ~(![A, B, C]: ((r1_setfam_1(A, B) & r1_setfam_1(B, C)) => r1_setfam_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_setfam_1)).
% 2.07/1.25  tff(f_45, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 2.07/1.25  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.07/1.25  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.07/1.25  tff(c_18, plain, (r1_setfam_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.07/1.25  tff(c_12, plain, (![A_6, B_7]: (r2_hidden('#skF_1'(A_6, B_7), A_6) | r1_setfam_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.07/1.25  tff(c_16, plain, (r1_setfam_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.07/1.25  tff(c_8, plain, (![A_6, B_7, C_16]: (r2_hidden('#skF_2'(A_6, B_7, C_16), B_7) | ~r2_hidden(C_16, A_6) | ~r1_setfam_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.07/1.25  tff(c_23, plain, (![C_28, A_29, B_30]: (r1_tarski(C_28, '#skF_2'(A_29, B_30, C_28)) | ~r2_hidden(C_28, A_29) | ~r1_setfam_1(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.07/1.25  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.07/1.25  tff(c_37, plain, (![C_28, A_29, B_30]: (k2_xboole_0(C_28, '#skF_2'(A_29, B_30, C_28))='#skF_2'(A_29, B_30, C_28) | ~r2_hidden(C_28, A_29) | ~r1_setfam_1(A_29, B_30))), inference(resolution, [status(thm)], [c_23, c_4])).
% 2.07/1.25  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.07/1.25  tff(c_57, plain, (![A_41, A_42, B_43, B_44]: (r1_tarski(A_41, '#skF_2'(A_42, B_43, k2_xboole_0(A_41, B_44))) | ~r2_hidden(k2_xboole_0(A_41, B_44), A_42) | ~r1_setfam_1(A_42, B_43))), inference(resolution, [status(thm)], [c_23, c_2])).
% 2.07/1.25  tff(c_10, plain, (![A_6, B_7, D_15]: (~r1_tarski('#skF_1'(A_6, B_7), D_15) | ~r2_hidden(D_15, B_7) | r1_setfam_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.07/1.25  tff(c_171, plain, (![B_66, A_70, B_68, A_67, B_69]: (~r2_hidden('#skF_2'(A_67, B_66, k2_xboole_0('#skF_1'(A_70, B_69), B_68)), B_69) | r1_setfam_1(A_70, B_69) | ~r2_hidden(k2_xboole_0('#skF_1'(A_70, B_69), B_68), A_67) | ~r1_setfam_1(A_67, B_66))), inference(resolution, [status(thm)], [c_57, c_10])).
% 2.07/1.25  tff(c_185, plain, (![A_71, B_72, B_73, A_74]: (r1_setfam_1(A_71, B_72) | ~r2_hidden(k2_xboole_0('#skF_1'(A_71, B_72), B_73), A_74) | ~r1_setfam_1(A_74, B_72))), inference(resolution, [status(thm)], [c_8, c_171])).
% 2.07/1.25  tff(c_219, plain, (![A_82, B_83, A_81, B_80, A_84]: (r1_setfam_1(A_82, B_83) | ~r2_hidden('#skF_2'(A_81, B_80, '#skF_1'(A_82, B_83)), A_84) | ~r1_setfam_1(A_84, B_83) | ~r2_hidden('#skF_1'(A_82, B_83), A_81) | ~r1_setfam_1(A_81, B_80))), inference(superposition, [status(thm), theory('equality')], [c_37, c_185])).
% 2.07/1.25  tff(c_225, plain, (![A_85, B_86, B_87, A_88]: (r1_setfam_1(A_85, B_86) | ~r1_setfam_1(B_87, B_86) | ~r2_hidden('#skF_1'(A_85, B_86), A_88) | ~r1_setfam_1(A_88, B_87))), inference(resolution, [status(thm)], [c_8, c_219])).
% 2.07/1.25  tff(c_232, plain, (![A_89, A_90]: (r1_setfam_1(A_89, '#skF_5') | ~r2_hidden('#skF_1'(A_89, '#skF_5'), A_90) | ~r1_setfam_1(A_90, '#skF_4'))), inference(resolution, [status(thm)], [c_16, c_225])).
% 2.07/1.25  tff(c_238, plain, (![A_91]: (~r1_setfam_1(A_91, '#skF_4') | r1_setfam_1(A_91, '#skF_5'))), inference(resolution, [status(thm)], [c_12, c_232])).
% 2.07/1.25  tff(c_14, plain, (~r1_setfam_1('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.07/1.25  tff(c_243, plain, (~r1_setfam_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_238, c_14])).
% 2.07/1.25  tff(c_248, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_243])).
% 2.07/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.25  
% 2.07/1.25  Inference rules
% 2.07/1.25  ----------------------
% 2.07/1.25  #Ref     : 0
% 2.07/1.25  #Sup     : 50
% 2.07/1.25  #Fact    : 0
% 2.07/1.25  #Define  : 0
% 2.07/1.25  #Split   : 0
% 2.07/1.25  #Chain   : 0
% 2.07/1.25  #Close   : 0
% 2.07/1.25  
% 2.07/1.25  Ordering : KBO
% 2.07/1.25  
% 2.07/1.25  Simplification rules
% 2.07/1.25  ----------------------
% 2.07/1.25  #Subsume      : 0
% 2.07/1.25  #Demod        : 1
% 2.07/1.25  #Tautology    : 5
% 2.07/1.25  #SimpNegUnit  : 0
% 2.07/1.25  #BackRed      : 0
% 2.07/1.25  
% 2.07/1.25  #Partial instantiations: 0
% 2.07/1.25  #Strategies tried      : 1
% 2.07/1.25  
% 2.07/1.25  Timing (in seconds)
% 2.07/1.25  ----------------------
% 2.07/1.25  Preprocessing        : 0.26
% 2.07/1.25  Parsing              : 0.15
% 2.07/1.25  CNF conversion       : 0.02
% 2.07/1.25  Main loop            : 0.23
% 2.07/1.25  Inferencing          : 0.11
% 2.07/1.25  Reduction            : 0.05
% 2.07/1.25  Demodulation         : 0.03
% 2.07/1.25  BG Simplification    : 0.02
% 2.07/1.25  Subsumption          : 0.05
% 2.07/1.25  Abstraction          : 0.01
% 2.07/1.25  MUC search           : 0.00
% 2.07/1.25  Cooper               : 0.00
% 2.07/1.25  Total                : 0.51
% 2.07/1.26  Index Insertion      : 0.00
% 2.07/1.26  Index Deletion       : 0.00
% 2.07/1.26  Index Matching       : 0.00
% 2.07/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
