%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:45 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   46 (  49 expanded)
%              Number of leaves         :   25 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   59 (  72 expanded)
%              Number of equality atoms :   20 (  21 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_91,axiom,(
    ! [A] : A != k1_ordinal1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_43,axiom,(
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

tff(f_86,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(f_88,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_32,plain,(
    ! [A_27] : k1_ordinal1(A_27) != A_27 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( r2_hidden('#skF_2'(A_16,B_17),A_16)
      | k1_xboole_0 = A_16
      | k1_tarski(B_17) = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_130,plain,(
    ! [D_62,A_63,B_64] :
      ( ~ r2_hidden(D_62,'#skF_3'(A_63,B_64))
      | ~ r2_hidden(D_62,B_64)
      | ~ r2_hidden(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_162,plain,(
    ! [A_73,B_74,B_75] :
      ( ~ r2_hidden('#skF_1'('#skF_3'(A_73,B_74),B_75),B_74)
      | ~ r2_hidden(A_73,B_74)
      | r1_xboole_0('#skF_3'(A_73,B_74),B_75) ) ),
    inference(resolution,[status(thm)],[c_6,c_130])).

tff(c_168,plain,(
    ! [A_76,B_77] :
      ( ~ r2_hidden(A_76,B_77)
      | r1_xboole_0('#skF_3'(A_76,B_77),B_77) ) ),
    inference(resolution,[status(thm)],[c_4,c_162])).

tff(c_89,plain,(
    ! [A_42,B_43] :
      ( r2_hidden('#skF_3'(A_42,B_43),B_43)
      | ~ r2_hidden(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_34,plain,(
    ! [B_29] :
      ( ~ r1_xboole_0(B_29,'#skF_4')
      | ~ r2_hidden(B_29,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_94,plain,(
    ! [A_42] :
      ( ~ r1_xboole_0('#skF_3'(A_42,'#skF_4'),'#skF_4')
      | ~ r2_hidden(A_42,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_89,c_34])).

tff(c_177,plain,(
    ! [A_78] : ~ r2_hidden(A_78,'#skF_4') ),
    inference(resolution,[status(thm)],[c_168,c_94])).

tff(c_181,plain,(
    ! [B_17] :
      ( k1_xboole_0 = '#skF_4'
      | k1_tarski(B_17) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_24,c_177])).

tff(c_196,plain,(
    ! [B_17] : k1_tarski(B_17) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_181])).

tff(c_30,plain,(
    ! [A_26] : k2_xboole_0(A_26,k1_tarski(A_26)) = k1_ordinal1(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_230,plain,(
    ! [A_83] : k2_xboole_0(A_83,'#skF_4') = k1_ordinal1(A_83) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_30])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_59,plain,(
    ! [A_35,B_36] :
      ( k2_xboole_0(A_35,B_36) = B_36
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_63,plain,(
    ! [B_7] : k2_xboole_0(B_7,B_7) = B_7 ),
    inference(resolution,[status(thm)],[c_12,c_59])).

tff(c_237,plain,(
    k1_ordinal1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_63])).

tff(c_247,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_237])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:30:50 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.21  
% 2.15/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.22  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.15/1.22  
% 2.15/1.22  %Foreground sorts:
% 2.15/1.22  
% 2.15/1.22  
% 2.15/1.22  %Background operators:
% 2.15/1.22  
% 2.15/1.22  
% 2.15/1.22  %Foreground operators:
% 2.15/1.22  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.15/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.15/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.22  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.15/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.15/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.15/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.15/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.22  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.15/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.15/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.15/1.22  
% 2.15/1.23  tff(f_91, axiom, (![A]: ~(A = k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_ordinal1)).
% 2.15/1.23  tff(f_102, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_mcart_1)).
% 2.15/1.23  tff(f_73, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 2.15/1.23  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.15/1.23  tff(f_86, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 2.15/1.23  tff(f_88, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 2.15/1.23  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.15/1.23  tff(f_53, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.15/1.23  tff(c_32, plain, (![A_27]: (k1_ordinal1(A_27)!=A_27)), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.15/1.23  tff(c_36, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.15/1.23  tff(c_24, plain, (![A_16, B_17]: (r2_hidden('#skF_2'(A_16, B_17), A_16) | k1_xboole_0=A_16 | k1_tarski(B_17)=A_16)), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.15/1.23  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.15/1.23  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.15/1.23  tff(c_130, plain, (![D_62, A_63, B_64]: (~r2_hidden(D_62, '#skF_3'(A_63, B_64)) | ~r2_hidden(D_62, B_64) | ~r2_hidden(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.15/1.23  tff(c_162, plain, (![A_73, B_74, B_75]: (~r2_hidden('#skF_1'('#skF_3'(A_73, B_74), B_75), B_74) | ~r2_hidden(A_73, B_74) | r1_xboole_0('#skF_3'(A_73, B_74), B_75))), inference(resolution, [status(thm)], [c_6, c_130])).
% 2.15/1.23  tff(c_168, plain, (![A_76, B_77]: (~r2_hidden(A_76, B_77) | r1_xboole_0('#skF_3'(A_76, B_77), B_77))), inference(resolution, [status(thm)], [c_4, c_162])).
% 2.15/1.23  tff(c_89, plain, (![A_42, B_43]: (r2_hidden('#skF_3'(A_42, B_43), B_43) | ~r2_hidden(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.15/1.23  tff(c_34, plain, (![B_29]: (~r1_xboole_0(B_29, '#skF_4') | ~r2_hidden(B_29, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.15/1.23  tff(c_94, plain, (![A_42]: (~r1_xboole_0('#skF_3'(A_42, '#skF_4'), '#skF_4') | ~r2_hidden(A_42, '#skF_4'))), inference(resolution, [status(thm)], [c_89, c_34])).
% 2.15/1.23  tff(c_177, plain, (![A_78]: (~r2_hidden(A_78, '#skF_4'))), inference(resolution, [status(thm)], [c_168, c_94])).
% 2.15/1.23  tff(c_181, plain, (![B_17]: (k1_xboole_0='#skF_4' | k1_tarski(B_17)='#skF_4')), inference(resolution, [status(thm)], [c_24, c_177])).
% 2.15/1.23  tff(c_196, plain, (![B_17]: (k1_tarski(B_17)='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_36, c_181])).
% 2.15/1.23  tff(c_30, plain, (![A_26]: (k2_xboole_0(A_26, k1_tarski(A_26))=k1_ordinal1(A_26))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.15/1.23  tff(c_230, plain, (![A_83]: (k2_xboole_0(A_83, '#skF_4')=k1_ordinal1(A_83))), inference(demodulation, [status(thm), theory('equality')], [c_196, c_30])).
% 2.15/1.23  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.15/1.23  tff(c_59, plain, (![A_35, B_36]: (k2_xboole_0(A_35, B_36)=B_36 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.15/1.23  tff(c_63, plain, (![B_7]: (k2_xboole_0(B_7, B_7)=B_7)), inference(resolution, [status(thm)], [c_12, c_59])).
% 2.15/1.23  tff(c_237, plain, (k1_ordinal1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_230, c_63])).
% 2.15/1.23  tff(c_247, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_237])).
% 2.15/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.23  
% 2.15/1.23  Inference rules
% 2.15/1.23  ----------------------
% 2.15/1.23  #Ref     : 0
% 2.15/1.23  #Sup     : 39
% 2.15/1.23  #Fact    : 0
% 2.15/1.23  #Define  : 0
% 2.15/1.23  #Split   : 0
% 2.15/1.23  #Chain   : 0
% 2.15/1.23  #Close   : 0
% 2.15/1.23  
% 2.15/1.23  Ordering : KBO
% 2.15/1.23  
% 2.15/1.23  Simplification rules
% 2.15/1.23  ----------------------
% 2.15/1.23  #Subsume      : 7
% 2.15/1.23  #Demod        : 10
% 2.15/1.23  #Tautology    : 20
% 2.15/1.23  #SimpNegUnit  : 3
% 2.15/1.23  #BackRed      : 4
% 2.15/1.23  
% 2.15/1.23  #Partial instantiations: 0
% 2.15/1.23  #Strategies tried      : 1
% 2.15/1.23  
% 2.15/1.23  Timing (in seconds)
% 2.15/1.23  ----------------------
% 2.27/1.23  Preprocessing        : 0.30
% 2.27/1.23  Parsing              : 0.16
% 2.27/1.23  CNF conversion       : 0.02
% 2.27/1.23  Main loop            : 0.17
% 2.27/1.23  Inferencing          : 0.07
% 2.27/1.23  Reduction            : 0.05
% 2.27/1.23  Demodulation         : 0.03
% 2.27/1.23  BG Simplification    : 0.01
% 2.27/1.23  Subsumption          : 0.03
% 2.27/1.23  Abstraction          : 0.01
% 2.27/1.23  MUC search           : 0.00
% 2.27/1.23  Cooper               : 0.00
% 2.27/1.23  Total                : 0.50
% 2.27/1.23  Index Insertion      : 0.00
% 2.27/1.23  Index Deletion       : 0.00
% 2.27/1.23  Index Matching       : 0.00
% 2.27/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
