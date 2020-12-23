%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:11 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   42 (  62 expanded)
%              Number of leaves         :   21 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   50 (  92 expanded)
%              Number of equality atoms :   13 (  34 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( A != B
       => ( r1_xboole_0(k2_zfmisc_1(k1_tarski(A),C),k2_zfmisc_1(k1_tarski(B),D))
          & r1_xboole_0(k2_zfmisc_1(C,k1_tarski(A)),k2_zfmisc_1(D,k1_tarski(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_zfmisc_1)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,B)
        & ~ r2_hidden(C,B)
        & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_34,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_131,plain,(
    ! [A_57,C_58,B_59] :
      ( r1_xboole_0(k2_tarski(A_57,C_58),B_59)
      | r2_hidden(C_58,B_59)
      | r2_hidden(A_57,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_136,plain,(
    ! [A_63,B_64] :
      ( r1_xboole_0(k1_tarski(A_63),B_64)
      | r2_hidden(A_63,B_64)
      | r2_hidden(A_63,B_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_131])).

tff(c_121,plain,(
    ! [C_49,D_50,A_51,B_52] :
      ( ~ r1_xboole_0(C_49,D_50)
      | r1_xboole_0(k2_zfmisc_1(A_51,C_49),k2_zfmisc_1(B_52,D_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_103,plain,(
    ! [A_44,C_45,B_46] :
      ( r1_xboole_0(k2_tarski(A_44,C_45),B_46)
      | r2_hidden(C_45,B_46)
      | r2_hidden(A_44,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_107,plain,(
    ! [A_47,B_48] :
      ( r1_xboole_0(k1_tarski(A_47),B_48)
      | r2_hidden(A_47,B_48)
      | r2_hidden(A_47,B_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_103])).

tff(c_98,plain,(
    ! [A_40,B_41,C_42,D_43] :
      ( ~ r1_xboole_0(A_40,B_41)
      | r1_xboole_0(k2_zfmisc_1(A_40,C_42),k2_zfmisc_1(B_41,D_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_32,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1('#skF_5',k1_tarski('#skF_3')),k2_zfmisc_1('#skF_6',k1_tarski('#skF_4')))
    | ~ r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_5'),k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_92,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_5'),k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_102,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_98,c_92])).

tff(c_111,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_107,c_102])).

tff(c_72,plain,(
    ! [D_31,B_32,A_33] :
      ( D_31 = B_32
      | D_31 = A_33
      | ~ r2_hidden(D_31,k2_tarski(A_33,B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_81,plain,(
    ! [D_31,A_7] :
      ( D_31 = A_7
      | D_31 = A_7
      | ~ r2_hidden(D_31,k1_tarski(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_72])).

tff(c_114,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_111,c_81])).

tff(c_118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_34,c_114])).

tff(c_119,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_5',k1_tarski('#skF_3')),k2_zfmisc_1('#skF_6',k1_tarski('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_125,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_121,c_119])).

tff(c_140,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_136,c_125])).

tff(c_143,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_140,c_81])).

tff(c_147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_34,c_143])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:46:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.20  
% 1.96/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.20  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 1.96/1.20  
% 1.96/1.20  %Foreground sorts:
% 1.96/1.20  
% 1.96/1.20  
% 1.96/1.20  %Background operators:
% 1.96/1.20  
% 1.96/1.20  
% 1.96/1.20  %Foreground operators:
% 1.96/1.20  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.96/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.96/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.96/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.96/1.20  tff('#skF_5', type, '#skF_5': $i).
% 1.96/1.20  tff('#skF_6', type, '#skF_6': $i).
% 1.96/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.96/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.96/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.96/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.96/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.96/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.20  
% 1.96/1.21  tff(f_64, negated_conjecture, ~(![A, B, C, D]: (~(A = B) => (r1_xboole_0(k2_zfmisc_1(k1_tarski(A), C), k2_zfmisc_1(k1_tarski(B), D)) & r1_xboole_0(k2_zfmisc_1(C, k1_tarski(A)), k2_zfmisc_1(D, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t131_zfmisc_1)).
% 1.96/1.21  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.96/1.21  tff(f_56, axiom, (![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 1.96/1.21  tff(f_46, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 1.96/1.21  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.96/1.21  tff(c_34, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.96/1.21  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.96/1.21  tff(c_131, plain, (![A_57, C_58, B_59]: (r1_xboole_0(k2_tarski(A_57, C_58), B_59) | r2_hidden(C_58, B_59) | r2_hidden(A_57, B_59))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.96/1.21  tff(c_136, plain, (![A_63, B_64]: (r1_xboole_0(k1_tarski(A_63), B_64) | r2_hidden(A_63, B_64) | r2_hidden(A_63, B_64))), inference(superposition, [status(thm), theory('equality')], [c_20, c_131])).
% 1.96/1.21  tff(c_121, plain, (![C_49, D_50, A_51, B_52]: (~r1_xboole_0(C_49, D_50) | r1_xboole_0(k2_zfmisc_1(A_51, C_49), k2_zfmisc_1(B_52, D_50)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.96/1.21  tff(c_103, plain, (![A_44, C_45, B_46]: (r1_xboole_0(k2_tarski(A_44, C_45), B_46) | r2_hidden(C_45, B_46) | r2_hidden(A_44, B_46))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.96/1.21  tff(c_107, plain, (![A_47, B_48]: (r1_xboole_0(k1_tarski(A_47), B_48) | r2_hidden(A_47, B_48) | r2_hidden(A_47, B_48))), inference(superposition, [status(thm), theory('equality')], [c_20, c_103])).
% 1.96/1.21  tff(c_98, plain, (![A_40, B_41, C_42, D_43]: (~r1_xboole_0(A_40, B_41) | r1_xboole_0(k2_zfmisc_1(A_40, C_42), k2_zfmisc_1(B_41, D_43)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.96/1.21  tff(c_32, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_5', k1_tarski('#skF_3')), k2_zfmisc_1('#skF_6', k1_tarski('#skF_4'))) | ~r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_5'), k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.96/1.21  tff(c_92, plain, (~r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_5'), k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_6'))), inference(splitLeft, [status(thm)], [c_32])).
% 1.96/1.21  tff(c_102, plain, (~r1_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_98, c_92])).
% 1.96/1.21  tff(c_111, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_107, c_102])).
% 1.96/1.21  tff(c_72, plain, (![D_31, B_32, A_33]: (D_31=B_32 | D_31=A_33 | ~r2_hidden(D_31, k2_tarski(A_33, B_32)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.96/1.21  tff(c_81, plain, (![D_31, A_7]: (D_31=A_7 | D_31=A_7 | ~r2_hidden(D_31, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_72])).
% 1.96/1.21  tff(c_114, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_111, c_81])).
% 1.96/1.21  tff(c_118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_34, c_114])).
% 1.96/1.21  tff(c_119, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_5', k1_tarski('#skF_3')), k2_zfmisc_1('#skF_6', k1_tarski('#skF_4')))), inference(splitRight, [status(thm)], [c_32])).
% 1.96/1.21  tff(c_125, plain, (~r1_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_121, c_119])).
% 1.96/1.21  tff(c_140, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_136, c_125])).
% 1.96/1.21  tff(c_143, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_140, c_81])).
% 1.96/1.21  tff(c_147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_34, c_143])).
% 1.96/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.21  
% 1.96/1.21  Inference rules
% 1.96/1.21  ----------------------
% 1.96/1.21  #Ref     : 0
% 1.96/1.21  #Sup     : 22
% 1.96/1.21  #Fact    : 0
% 1.96/1.21  #Define  : 0
% 1.96/1.21  #Split   : 1
% 1.96/1.21  #Chain   : 0
% 1.96/1.21  #Close   : 0
% 1.96/1.21  
% 1.96/1.21  Ordering : KBO
% 1.96/1.21  
% 1.96/1.21  Simplification rules
% 1.96/1.21  ----------------------
% 1.96/1.21  #Subsume      : 0
% 1.96/1.21  #Demod        : 1
% 1.96/1.21  #Tautology    : 10
% 1.96/1.21  #SimpNegUnit  : 2
% 1.96/1.21  #BackRed      : 0
% 1.96/1.21  
% 1.96/1.21  #Partial instantiations: 0
% 1.96/1.21  #Strategies tried      : 1
% 1.96/1.21  
% 1.96/1.21  Timing (in seconds)
% 1.96/1.21  ----------------------
% 1.96/1.21  Preprocessing        : 0.31
% 1.96/1.21  Parsing              : 0.16
% 1.96/1.22  CNF conversion       : 0.02
% 1.96/1.22  Main loop            : 0.15
% 1.96/1.22  Inferencing          : 0.06
% 1.96/1.22  Reduction            : 0.04
% 1.96/1.22  Demodulation         : 0.03
% 1.96/1.22  BG Simplification    : 0.01
% 1.96/1.22  Subsumption          : 0.03
% 1.96/1.22  Abstraction          : 0.01
% 1.96/1.22  MUC search           : 0.00
% 1.96/1.22  Cooper               : 0.00
% 1.96/1.22  Total                : 0.49
% 1.96/1.22  Index Insertion      : 0.00
% 1.96/1.22  Index Deletion       : 0.00
% 1.96/1.22  Index Matching       : 0.00
% 1.96/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
