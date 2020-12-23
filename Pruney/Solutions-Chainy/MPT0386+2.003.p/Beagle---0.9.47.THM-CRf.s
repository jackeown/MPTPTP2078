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
% DateTime   : Thu Dec  3 09:57:09 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   44 (  55 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   55 (  84 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_73,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(c_44,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_46,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_55,plain,(
    ! [B_36,A_37] :
      ( ~ r2_hidden(B_36,A_37)
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_46,c_55])).

tff(c_181,plain,(
    ! [C_66,D_67,A_68] :
      ( r2_hidden(C_66,D_67)
      | ~ r2_hidden(D_67,A_68)
      | ~ r2_hidden(C_66,k1_setfam_1(A_68))
      | k1_xboole_0 = A_68 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_196,plain,(
    ! [C_66] :
      ( r2_hidden(C_66,'#skF_7')
      | ~ r2_hidden(C_66,k1_setfam_1('#skF_8'))
      | k1_xboole_0 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_46,c_181])).

tff(c_197,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_18,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_72,plain,(
    ! [B_41,A_42] :
      ( ~ r1_xboole_0(B_41,A_42)
      | ~ r1_tarski(B_41,A_42)
      | v1_xboole_0(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_77,plain,(
    ! [A_43] :
      ( ~ r1_tarski(A_43,k1_xboole_0)
      | v1_xboole_0(A_43) ) ),
    inference(resolution,[status(thm)],[c_18,c_72])).

tff(c_82,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_77])).

tff(c_200,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_82])).

tff(c_205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_200])).

tff(c_208,plain,(
    ! [C_69] :
      ( r2_hidden(C_69,'#skF_7')
      | ~ r2_hidden(C_69,k1_setfam_1('#skF_8')) ) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_306,plain,(
    ! [B_75] :
      ( r2_hidden('#skF_2'(k1_setfam_1('#skF_8'),B_75),'#skF_7')
      | r1_tarski(k1_setfam_1('#skF_8'),B_75) ) ),
    inference(resolution,[status(thm)],[c_10,c_208])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_314,plain,(
    r1_tarski(k1_setfam_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_306,c_8])).

tff(c_323,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_44,c_314])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:54:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.34  
% 2.11/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.34  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_5 > #skF_4
% 2.11/1.34  
% 2.11/1.34  %Foreground sorts:
% 2.11/1.34  
% 2.11/1.34  
% 2.11/1.34  %Background operators:
% 2.11/1.34  
% 2.11/1.34  
% 2.11/1.34  %Foreground operators:
% 2.11/1.34  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.11/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.11/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.34  tff('#skF_7', type, '#skF_7': $i).
% 2.11/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.11/1.34  tff('#skF_8', type, '#skF_8': $i).
% 2.11/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.11/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.11/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.11/1.34  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.11/1.34  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.11/1.34  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.11/1.34  
% 2.44/1.35  tff(f_78, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.44/1.35  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.44/1.35  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.44/1.35  tff(f_73, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_setfam_1)).
% 2.44/1.35  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.44/1.35  tff(f_46, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.44/1.35  tff(f_54, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.44/1.35  tff(c_44, plain, (~r1_tarski(k1_setfam_1('#skF_8'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.44/1.35  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.44/1.35  tff(c_46, plain, (r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.44/1.35  tff(c_55, plain, (![B_36, A_37]: (~r2_hidden(B_36, A_37) | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.44/1.35  tff(c_59, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_46, c_55])).
% 2.44/1.35  tff(c_181, plain, (![C_66, D_67, A_68]: (r2_hidden(C_66, D_67) | ~r2_hidden(D_67, A_68) | ~r2_hidden(C_66, k1_setfam_1(A_68)) | k1_xboole_0=A_68)), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.44/1.35  tff(c_196, plain, (![C_66]: (r2_hidden(C_66, '#skF_7') | ~r2_hidden(C_66, k1_setfam_1('#skF_8')) | k1_xboole_0='#skF_8')), inference(resolution, [status(thm)], [c_46, c_181])).
% 2.44/1.35  tff(c_197, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_196])).
% 2.44/1.35  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.44/1.35  tff(c_18, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.44/1.35  tff(c_72, plain, (![B_41, A_42]: (~r1_xboole_0(B_41, A_42) | ~r1_tarski(B_41, A_42) | v1_xboole_0(B_41))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.44/1.35  tff(c_77, plain, (![A_43]: (~r1_tarski(A_43, k1_xboole_0) | v1_xboole_0(A_43))), inference(resolution, [status(thm)], [c_18, c_72])).
% 2.44/1.35  tff(c_82, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_77])).
% 2.44/1.35  tff(c_200, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_197, c_82])).
% 2.44/1.35  tff(c_205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_200])).
% 2.44/1.35  tff(c_208, plain, (![C_69]: (r2_hidden(C_69, '#skF_7') | ~r2_hidden(C_69, k1_setfam_1('#skF_8')))), inference(splitRight, [status(thm)], [c_196])).
% 2.44/1.35  tff(c_306, plain, (![B_75]: (r2_hidden('#skF_2'(k1_setfam_1('#skF_8'), B_75), '#skF_7') | r1_tarski(k1_setfam_1('#skF_8'), B_75))), inference(resolution, [status(thm)], [c_10, c_208])).
% 2.44/1.35  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.44/1.35  tff(c_314, plain, (r1_tarski(k1_setfam_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_306, c_8])).
% 2.44/1.35  tff(c_323, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_44, c_314])).
% 2.44/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.35  
% 2.44/1.35  Inference rules
% 2.44/1.35  ----------------------
% 2.44/1.35  #Ref     : 0
% 2.44/1.35  #Sup     : 59
% 2.44/1.35  #Fact    : 0
% 2.44/1.35  #Define  : 0
% 2.44/1.35  #Split   : 2
% 2.44/1.35  #Chain   : 0
% 2.44/1.35  #Close   : 0
% 2.44/1.35  
% 2.44/1.35  Ordering : KBO
% 2.44/1.35  
% 2.44/1.35  Simplification rules
% 2.44/1.35  ----------------------
% 2.44/1.35  #Subsume      : 8
% 2.44/1.35  #Demod        : 13
% 2.44/1.35  #Tautology    : 14
% 2.44/1.35  #SimpNegUnit  : 3
% 2.44/1.35  #BackRed      : 6
% 2.44/1.35  
% 2.44/1.35  #Partial instantiations: 0
% 2.44/1.35  #Strategies tried      : 1
% 2.44/1.35  
% 2.44/1.35  Timing (in seconds)
% 2.44/1.35  ----------------------
% 2.44/1.35  Preprocessing        : 0.28
% 2.44/1.35  Parsing              : 0.14
% 2.44/1.35  CNF conversion       : 0.02
% 2.44/1.35  Main loop            : 0.25
% 2.44/1.35  Inferencing          : 0.09
% 2.44/1.35  Reduction            : 0.06
% 2.44/1.35  Demodulation         : 0.05
% 2.44/1.35  BG Simplification    : 0.02
% 2.44/1.35  Subsumption          : 0.07
% 2.44/1.36  Abstraction          : 0.01
% 2.44/1.36  MUC search           : 0.00
% 2.44/1.36  Cooper               : 0.00
% 2.44/1.36  Total                : 0.56
% 2.44/1.36  Index Insertion      : 0.00
% 2.44/1.36  Index Deletion       : 0.00
% 2.44/1.36  Index Matching       : 0.00
% 2.44/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
