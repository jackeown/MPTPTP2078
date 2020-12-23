%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:49 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   38 (  43 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   62 (  84 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > #nlpp > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_56,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r2_hidden('#skF_2'(A_3,B_4),A_3)
      | B_4 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_105,plain,(
    ! [A_49,B_50] :
      ( r2_hidden('#skF_1'(A_49,B_50),B_50)
      | r2_hidden('#skF_2'(A_49,B_50),A_49)
      | B_50 = A_49 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_59,plain,(
    ! [A_35,B_36,C_37] :
      ( ~ r1_xboole_0(A_35,B_36)
      | ~ r2_hidden(C_37,B_36)
      | ~ r2_hidden(C_37,A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_65,plain,(
    ! [C_37,A_11] :
      ( ~ r2_hidden(C_37,k1_xboole_0)
      | ~ r2_hidden(C_37,A_11) ) ),
    inference(resolution,[status(thm)],[c_18,c_59])).

tff(c_188,plain,(
    ! [B_55,A_56] :
      ( ~ r2_hidden('#skF_2'(k1_xboole_0,B_55),A_56)
      | r2_hidden('#skF_1'(k1_xboole_0,B_55),B_55)
      | k1_xboole_0 = B_55 ) ),
    inference(resolution,[status(thm)],[c_105,c_65])).

tff(c_196,plain,(
    ! [B_4] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_4),B_4)
      | k1_xboole_0 = B_4 ) ),
    inference(resolution,[status(thm)],[c_10,c_188])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_3'(A_6,B_7),A_6)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_3'(A_6,B_7),B_7)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_87,plain,(
    ! [D_42,A_43,B_44] :
      ( ~ r2_hidden(D_42,'#skF_4'(A_43,B_44))
      | ~ r2_hidden(D_42,B_44)
      | ~ r2_hidden(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_197,plain,(
    ! [A_57,A_58,B_59] :
      ( ~ r2_hidden('#skF_3'(A_57,'#skF_4'(A_58,B_59)),B_59)
      | ~ r2_hidden(A_58,B_59)
      | r1_xboole_0(A_57,'#skF_4'(A_58,B_59)) ) ),
    inference(resolution,[status(thm)],[c_14,c_87])).

tff(c_226,plain,(
    ! [A_61,A_62] :
      ( ~ r2_hidden(A_61,A_62)
      | r1_xboole_0(A_62,'#skF_4'(A_61,A_62)) ) ),
    inference(resolution,[status(thm)],[c_16,c_197])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_234,plain,(
    ! [A_65,A_66] :
      ( r1_xboole_0('#skF_4'(A_65,A_66),A_66)
      | ~ r2_hidden(A_65,A_66) ) ),
    inference(resolution,[status(thm)],[c_226,c_2])).

tff(c_50,plain,(
    ! [A_30,B_31] :
      ( r2_hidden('#skF_4'(A_30,B_31),B_31)
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24,plain,(
    ! [B_20] :
      ( ~ r1_xboole_0(B_20,'#skF_5')
      | ~ r2_hidden(B_20,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_55,plain,(
    ! [A_30] :
      ( ~ r1_xboole_0('#skF_4'(A_30,'#skF_5'),'#skF_5')
      | ~ r2_hidden(A_30,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_24])).

tff(c_246,plain,(
    ! [A_67] : ~ r2_hidden(A_67,'#skF_5') ),
    inference(resolution,[status(thm)],[c_234,c_55])).

tff(c_250,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_196,c_246])).

tff(c_280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_250])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n010.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 20:08:44 EST 2020
% 0.21/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.35  
% 2.17/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.35  %$ r2_hidden > r1_xboole_0 > #nlpp > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 2.17/1.35  
% 2.17/1.35  %Foreground sorts:
% 2.17/1.35  
% 2.17/1.35  
% 2.17/1.35  %Background operators:
% 2.17/1.35  
% 2.17/1.35  
% 2.17/1.35  %Foreground operators:
% 2.17/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.35  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.17/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.17/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.17/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.17/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.17/1.35  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.17/1.35  
% 2.17/1.36  tff(f_80, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_mcart_1)).
% 2.17/1.36  tff(f_36, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 2.17/1.36  tff(f_56, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.17/1.36  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.17/1.36  tff(f_69, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 2.17/1.36  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.17/1.36  tff(c_26, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.17/1.36  tff(c_10, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r2_hidden('#skF_2'(A_3, B_4), A_3) | B_4=A_3)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.17/1.36  tff(c_105, plain, (![A_49, B_50]: (r2_hidden('#skF_1'(A_49, B_50), B_50) | r2_hidden('#skF_2'(A_49, B_50), A_49) | B_50=A_49)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.17/1.36  tff(c_18, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.17/1.36  tff(c_59, plain, (![A_35, B_36, C_37]: (~r1_xboole_0(A_35, B_36) | ~r2_hidden(C_37, B_36) | ~r2_hidden(C_37, A_35))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.17/1.36  tff(c_65, plain, (![C_37, A_11]: (~r2_hidden(C_37, k1_xboole_0) | ~r2_hidden(C_37, A_11))), inference(resolution, [status(thm)], [c_18, c_59])).
% 2.17/1.36  tff(c_188, plain, (![B_55, A_56]: (~r2_hidden('#skF_2'(k1_xboole_0, B_55), A_56) | r2_hidden('#skF_1'(k1_xboole_0, B_55), B_55) | k1_xboole_0=B_55)), inference(resolution, [status(thm)], [c_105, c_65])).
% 2.17/1.36  tff(c_196, plain, (![B_4]: (r2_hidden('#skF_1'(k1_xboole_0, B_4), B_4) | k1_xboole_0=B_4)), inference(resolution, [status(thm)], [c_10, c_188])).
% 2.17/1.36  tff(c_16, plain, (![A_6, B_7]: (r2_hidden('#skF_3'(A_6, B_7), A_6) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.17/1.36  tff(c_14, plain, (![A_6, B_7]: (r2_hidden('#skF_3'(A_6, B_7), B_7) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.17/1.36  tff(c_87, plain, (![D_42, A_43, B_44]: (~r2_hidden(D_42, '#skF_4'(A_43, B_44)) | ~r2_hidden(D_42, B_44) | ~r2_hidden(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.17/1.36  tff(c_197, plain, (![A_57, A_58, B_59]: (~r2_hidden('#skF_3'(A_57, '#skF_4'(A_58, B_59)), B_59) | ~r2_hidden(A_58, B_59) | r1_xboole_0(A_57, '#skF_4'(A_58, B_59)))), inference(resolution, [status(thm)], [c_14, c_87])).
% 2.17/1.36  tff(c_226, plain, (![A_61, A_62]: (~r2_hidden(A_61, A_62) | r1_xboole_0(A_62, '#skF_4'(A_61, A_62)))), inference(resolution, [status(thm)], [c_16, c_197])).
% 2.17/1.36  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.17/1.36  tff(c_234, plain, (![A_65, A_66]: (r1_xboole_0('#skF_4'(A_65, A_66), A_66) | ~r2_hidden(A_65, A_66))), inference(resolution, [status(thm)], [c_226, c_2])).
% 2.17/1.36  tff(c_50, plain, (![A_30, B_31]: (r2_hidden('#skF_4'(A_30, B_31), B_31) | ~r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.17/1.36  tff(c_24, plain, (![B_20]: (~r1_xboole_0(B_20, '#skF_5') | ~r2_hidden(B_20, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.17/1.36  tff(c_55, plain, (![A_30]: (~r1_xboole_0('#skF_4'(A_30, '#skF_5'), '#skF_5') | ~r2_hidden(A_30, '#skF_5'))), inference(resolution, [status(thm)], [c_50, c_24])).
% 2.17/1.36  tff(c_246, plain, (![A_67]: (~r2_hidden(A_67, '#skF_5'))), inference(resolution, [status(thm)], [c_234, c_55])).
% 2.17/1.36  tff(c_250, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_196, c_246])).
% 2.17/1.36  tff(c_280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_250])).
% 2.17/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.36  
% 2.17/1.36  Inference rules
% 2.17/1.36  ----------------------
% 2.17/1.36  #Ref     : 0
% 2.17/1.36  #Sup     : 47
% 2.17/1.36  #Fact    : 0
% 2.17/1.36  #Define  : 0
% 2.17/1.36  #Split   : 1
% 2.17/1.36  #Chain   : 0
% 2.17/1.36  #Close   : 0
% 2.17/1.36  
% 2.17/1.36  Ordering : KBO
% 2.17/1.36  
% 2.17/1.36  Simplification rules
% 2.17/1.36  ----------------------
% 2.17/1.36  #Subsume      : 10
% 2.17/1.36  #Demod        : 3
% 2.17/1.36  #Tautology    : 9
% 2.17/1.36  #SimpNegUnit  : 3
% 2.17/1.36  #BackRed      : 0
% 2.17/1.36  
% 2.17/1.36  #Partial instantiations: 0
% 2.17/1.36  #Strategies tried      : 1
% 2.17/1.36  
% 2.17/1.36  Timing (in seconds)
% 2.17/1.36  ----------------------
% 2.17/1.37  Preprocessing        : 0.33
% 2.17/1.37  Parsing              : 0.17
% 2.17/1.37  CNF conversion       : 0.02
% 2.17/1.37  Main loop            : 0.21
% 2.17/1.37  Inferencing          : 0.09
% 2.17/1.37  Reduction            : 0.05
% 2.17/1.37  Demodulation         : 0.03
% 2.17/1.37  BG Simplification    : 0.02
% 2.17/1.37  Subsumption          : 0.05
% 2.17/1.37  Abstraction          : 0.01
% 2.17/1.37  MUC search           : 0.00
% 2.17/1.37  Cooper               : 0.00
% 2.17/1.37  Total                : 0.56
% 2.17/1.37  Index Insertion      : 0.00
% 2.17/1.37  Index Deletion       : 0.00
% 2.17/1.37  Index Matching       : 0.00
% 2.17/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
