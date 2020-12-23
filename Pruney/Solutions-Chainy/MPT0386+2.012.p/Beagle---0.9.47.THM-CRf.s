%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:10 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   43 (  54 expanded)
%              Number of leaves         :   23 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   60 (  82 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_50,axiom,(
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

tff(f_77,axiom,(
    ! [A,B] :
      ( ( A != k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => r2_hidden(C,D) ) ) ) )
      & ( A = k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

tff(c_44,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_71,plain,(
    ! [A_48,B_49] :
      ( r2_hidden('#skF_1'(A_48,B_49),A_48)
      | r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_77,plain,(
    ! [A_50] : r1_tarski(A_50,A_50) ),
    inference(resolution,[status(thm)],[c_71,c_4])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = k1_xboole_0
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_81,plain,(
    ! [A_50] : k4_xboole_0(A_50,A_50) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_77,c_16])).

tff(c_46,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( r1_xboole_0(A_13,B_14)
      | k4_xboole_0(A_13,B_14) != A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_89,plain,(
    ! [A_52,B_53,C_54] :
      ( ~ r1_xboole_0(A_52,B_53)
      | ~ r2_hidden(C_54,B_53)
      | ~ r2_hidden(C_54,A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_117,plain,(
    ! [C_61,B_62,A_63] :
      ( ~ r2_hidden(C_61,B_62)
      | ~ r2_hidden(C_61,A_63)
      | k4_xboole_0(A_63,B_62) != A_63 ) ),
    inference(resolution,[status(thm)],[c_20,c_89])).

tff(c_133,plain,(
    ! [A_64] :
      ( ~ r2_hidden('#skF_7',A_64)
      | k4_xboole_0(A_64,'#skF_8') != A_64 ) ),
    inference(resolution,[status(thm)],[c_46,c_117])).

tff(c_139,plain,(
    k4_xboole_0('#skF_8','#skF_8') != '#skF_8' ),
    inference(resolution,[status(thm)],[c_46,c_133])).

tff(c_142,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_139])).

tff(c_180,plain,(
    ! [C_70,D_71,A_72] :
      ( r2_hidden(C_70,D_71)
      | ~ r2_hidden(D_71,A_72)
      | ~ r2_hidden(C_70,k1_setfam_1(A_72))
      | k1_xboole_0 = A_72 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_190,plain,(
    ! [C_70] :
      ( r2_hidden(C_70,'#skF_7')
      | ~ r2_hidden(C_70,k1_setfam_1('#skF_8'))
      | k1_xboole_0 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_46,c_180])).

tff(c_198,plain,(
    ! [C_73] :
      ( r2_hidden(C_73,'#skF_7')
      | ~ r2_hidden(C_73,k1_setfam_1('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_190])).

tff(c_241,plain,(
    ! [B_76] :
      ( r2_hidden('#skF_1'(k1_setfam_1('#skF_8'),B_76),'#skF_7')
      | r1_tarski(k1_setfam_1('#skF_8'),B_76) ) ),
    inference(resolution,[status(thm)],[c_6,c_198])).

tff(c_251,plain,(
    r1_tarski(k1_setfam_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_241,c_4])).

tff(c_258,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_44,c_251])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:33:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.26  
% 2.06/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.26  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 2.06/1.26  
% 2.06/1.26  %Foreground sorts:
% 2.06/1.26  
% 2.06/1.26  
% 2.06/1.26  %Background operators:
% 2.06/1.26  
% 2.06/1.26  
% 2.06/1.26  %Foreground operators:
% 2.06/1.26  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.06/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.06/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.26  tff('#skF_7', type, '#skF_7': $i).
% 2.06/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.06/1.26  tff('#skF_8', type, '#skF_8': $i).
% 2.06/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.26  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.06/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.06/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.06/1.26  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.06/1.26  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.06/1.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.06/1.26  
% 2.06/1.27  tff(f_82, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.06/1.27  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.06/1.27  tff(f_54, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.06/1.27  tff(f_58, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.06/1.27  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.06/1.27  tff(f_77, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_setfam_1)).
% 2.06/1.27  tff(c_44, plain, (~r1_tarski(k1_setfam_1('#skF_8'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.06/1.27  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.06/1.27  tff(c_71, plain, (![A_48, B_49]: (r2_hidden('#skF_1'(A_48, B_49), A_48) | r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.06/1.27  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.06/1.27  tff(c_77, plain, (![A_50]: (r1_tarski(A_50, A_50))), inference(resolution, [status(thm)], [c_71, c_4])).
% 2.06/1.27  tff(c_16, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=k1_xboole_0 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.06/1.27  tff(c_81, plain, (![A_50]: (k4_xboole_0(A_50, A_50)=k1_xboole_0)), inference(resolution, [status(thm)], [c_77, c_16])).
% 2.06/1.27  tff(c_46, plain, (r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.06/1.27  tff(c_20, plain, (![A_13, B_14]: (r1_xboole_0(A_13, B_14) | k4_xboole_0(A_13, B_14)!=A_13)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.06/1.27  tff(c_89, plain, (![A_52, B_53, C_54]: (~r1_xboole_0(A_52, B_53) | ~r2_hidden(C_54, B_53) | ~r2_hidden(C_54, A_52))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.06/1.27  tff(c_117, plain, (![C_61, B_62, A_63]: (~r2_hidden(C_61, B_62) | ~r2_hidden(C_61, A_63) | k4_xboole_0(A_63, B_62)!=A_63)), inference(resolution, [status(thm)], [c_20, c_89])).
% 2.06/1.27  tff(c_133, plain, (![A_64]: (~r2_hidden('#skF_7', A_64) | k4_xboole_0(A_64, '#skF_8')!=A_64)), inference(resolution, [status(thm)], [c_46, c_117])).
% 2.06/1.27  tff(c_139, plain, (k4_xboole_0('#skF_8', '#skF_8')!='#skF_8'), inference(resolution, [status(thm)], [c_46, c_133])).
% 2.06/1.27  tff(c_142, plain, (k1_xboole_0!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_81, c_139])).
% 2.06/1.27  tff(c_180, plain, (![C_70, D_71, A_72]: (r2_hidden(C_70, D_71) | ~r2_hidden(D_71, A_72) | ~r2_hidden(C_70, k1_setfam_1(A_72)) | k1_xboole_0=A_72)), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.06/1.27  tff(c_190, plain, (![C_70]: (r2_hidden(C_70, '#skF_7') | ~r2_hidden(C_70, k1_setfam_1('#skF_8')) | k1_xboole_0='#skF_8')), inference(resolution, [status(thm)], [c_46, c_180])).
% 2.06/1.27  tff(c_198, plain, (![C_73]: (r2_hidden(C_73, '#skF_7') | ~r2_hidden(C_73, k1_setfam_1('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_142, c_190])).
% 2.06/1.27  tff(c_241, plain, (![B_76]: (r2_hidden('#skF_1'(k1_setfam_1('#skF_8'), B_76), '#skF_7') | r1_tarski(k1_setfam_1('#skF_8'), B_76))), inference(resolution, [status(thm)], [c_6, c_198])).
% 2.06/1.27  tff(c_251, plain, (r1_tarski(k1_setfam_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_241, c_4])).
% 2.06/1.27  tff(c_258, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_44, c_251])).
% 2.06/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.27  
% 2.06/1.27  Inference rules
% 2.06/1.27  ----------------------
% 2.06/1.27  #Ref     : 0
% 2.06/1.27  #Sup     : 49
% 2.06/1.27  #Fact    : 0
% 2.06/1.27  #Define  : 0
% 2.06/1.28  #Split   : 1
% 2.06/1.28  #Chain   : 0
% 2.06/1.28  #Close   : 0
% 2.06/1.28  
% 2.06/1.28  Ordering : KBO
% 2.06/1.28  
% 2.06/1.28  Simplification rules
% 2.06/1.28  ----------------------
% 2.06/1.28  #Subsume      : 5
% 2.06/1.28  #Demod        : 6
% 2.06/1.28  #Tautology    : 7
% 2.06/1.28  #SimpNegUnit  : 2
% 2.06/1.28  #BackRed      : 0
% 2.06/1.28  
% 2.06/1.28  #Partial instantiations: 0
% 2.06/1.28  #Strategies tried      : 1
% 2.06/1.28  
% 2.06/1.28  Timing (in seconds)
% 2.06/1.28  ----------------------
% 2.06/1.28  Preprocessing        : 0.31
% 2.06/1.28  Parsing              : 0.16
% 2.06/1.28  CNF conversion       : 0.03
% 2.06/1.28  Main loop            : 0.22
% 2.06/1.28  Inferencing          : 0.08
% 2.06/1.28  Reduction            : 0.06
% 2.06/1.28  Demodulation         : 0.04
% 2.06/1.28  BG Simplification    : 0.02
% 2.06/1.28  Subsumption          : 0.05
% 2.06/1.28  Abstraction          : 0.01
% 2.06/1.28  MUC search           : 0.00
% 2.06/1.28  Cooper               : 0.00
% 2.06/1.28  Total                : 0.55
% 2.06/1.28  Index Insertion      : 0.00
% 2.06/1.28  Index Deletion       : 0.00
% 2.06/1.28  Index Matching       : 0.00
% 2.06/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
