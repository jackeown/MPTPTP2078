%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:45 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.35s
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

tff(f_95,axiom,(
    ! [A] : A != k1_ordinal1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_ordinal1)).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

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

tff(f_90,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(f_92,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_34,plain,(
    ! [A_29] : k1_ordinal1(A_29) != A_29 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_26,plain,(
    ! [A_18,B_19] :
      ( r2_hidden('#skF_2'(A_18,B_19),A_18)
      | k1_xboole_0 = A_18
      | k1_tarski(B_19) = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_133,plain,(
    ! [D_66,A_67,B_68] :
      ( ~ r2_hidden(D_66,'#skF_3'(A_67,B_68))
      | ~ r2_hidden(D_66,B_68)
      | ~ r2_hidden(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_167,plain,(
    ! [A_74,B_75,B_76] :
      ( ~ r2_hidden('#skF_1'('#skF_3'(A_74,B_75),B_76),B_75)
      | ~ r2_hidden(A_74,B_75)
      | r1_xboole_0('#skF_3'(A_74,B_75),B_76) ) ),
    inference(resolution,[status(thm)],[c_8,c_133])).

tff(c_173,plain,(
    ! [A_77,B_78] :
      ( ~ r2_hidden(A_77,B_78)
      | r1_xboole_0('#skF_3'(A_77,B_78),B_78) ) ),
    inference(resolution,[status(thm)],[c_6,c_167])).

tff(c_91,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_3'(A_46,B_47),B_47)
      | ~ r2_hidden(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_36,plain,(
    ! [B_31] :
      ( ~ r1_xboole_0(B_31,'#skF_4')
      | ~ r2_hidden(B_31,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_96,plain,(
    ! [A_46] :
      ( ~ r1_xboole_0('#skF_3'(A_46,'#skF_4'),'#skF_4')
      | ~ r2_hidden(A_46,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_91,c_36])).

tff(c_185,plain,(
    ! [A_79] : ~ r2_hidden(A_79,'#skF_4') ),
    inference(resolution,[status(thm)],[c_173,c_96])).

tff(c_189,plain,(
    ! [B_19] :
      ( k1_xboole_0 = '#skF_4'
      | k1_tarski(B_19) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_26,c_185])).

tff(c_204,plain,(
    ! [B_19] : k1_tarski(B_19) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_189])).

tff(c_32,plain,(
    ! [A_28] : k2_xboole_0(A_28,k1_tarski(A_28)) = k1_ordinal1(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_248,plain,(
    ! [A_84] : k2_xboole_0(A_84,'#skF_4') = k1_ordinal1(A_84) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_32])).

tff(c_14,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_71,plain,(
    ! [A_41,B_42] :
      ( k2_xboole_0(A_41,B_42) = B_42
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_75,plain,(
    ! [B_9] : k2_xboole_0(B_9,B_9) = B_9 ),
    inference(resolution,[status(thm)],[c_14,c_71])).

tff(c_255,plain,(
    k1_ordinal1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_75])).

tff(c_265,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_255])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:14:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.23  
% 2.17/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.23  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.35/1.23  
% 2.35/1.23  %Foreground sorts:
% 2.35/1.23  
% 2.35/1.23  
% 2.35/1.23  %Background operators:
% 2.35/1.23  
% 2.35/1.23  
% 2.35/1.23  %Foreground operators:
% 2.35/1.23  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.35/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.35/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.35/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.35/1.23  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.35/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.35/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.35/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.35/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.35/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.35/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.35/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.35/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.35/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.35/1.23  
% 2.35/1.24  tff(f_95, axiom, (![A]: ~(A = k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_ordinal1)).
% 2.35/1.24  tff(f_106, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 2.35/1.24  tff(f_77, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 2.35/1.24  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.35/1.24  tff(f_90, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 2.35/1.24  tff(f_92, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 2.35/1.24  tff(f_53, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.35/1.24  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.35/1.24  tff(c_34, plain, (![A_29]: (k1_ordinal1(A_29)!=A_29)), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.35/1.24  tff(c_38, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.35/1.24  tff(c_26, plain, (![A_18, B_19]: (r2_hidden('#skF_2'(A_18, B_19), A_18) | k1_xboole_0=A_18 | k1_tarski(B_19)=A_18)), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.35/1.24  tff(c_6, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.35/1.24  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.35/1.24  tff(c_133, plain, (![D_66, A_67, B_68]: (~r2_hidden(D_66, '#skF_3'(A_67, B_68)) | ~r2_hidden(D_66, B_68) | ~r2_hidden(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.35/1.24  tff(c_167, plain, (![A_74, B_75, B_76]: (~r2_hidden('#skF_1'('#skF_3'(A_74, B_75), B_76), B_75) | ~r2_hidden(A_74, B_75) | r1_xboole_0('#skF_3'(A_74, B_75), B_76))), inference(resolution, [status(thm)], [c_8, c_133])).
% 2.35/1.24  tff(c_173, plain, (![A_77, B_78]: (~r2_hidden(A_77, B_78) | r1_xboole_0('#skF_3'(A_77, B_78), B_78))), inference(resolution, [status(thm)], [c_6, c_167])).
% 2.35/1.24  tff(c_91, plain, (![A_46, B_47]: (r2_hidden('#skF_3'(A_46, B_47), B_47) | ~r2_hidden(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.35/1.24  tff(c_36, plain, (![B_31]: (~r1_xboole_0(B_31, '#skF_4') | ~r2_hidden(B_31, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.35/1.24  tff(c_96, plain, (![A_46]: (~r1_xboole_0('#skF_3'(A_46, '#skF_4'), '#skF_4') | ~r2_hidden(A_46, '#skF_4'))), inference(resolution, [status(thm)], [c_91, c_36])).
% 2.35/1.24  tff(c_185, plain, (![A_79]: (~r2_hidden(A_79, '#skF_4'))), inference(resolution, [status(thm)], [c_173, c_96])).
% 2.35/1.24  tff(c_189, plain, (![B_19]: (k1_xboole_0='#skF_4' | k1_tarski(B_19)='#skF_4')), inference(resolution, [status(thm)], [c_26, c_185])).
% 2.35/1.24  tff(c_204, plain, (![B_19]: (k1_tarski(B_19)='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_38, c_189])).
% 2.35/1.24  tff(c_32, plain, (![A_28]: (k2_xboole_0(A_28, k1_tarski(A_28))=k1_ordinal1(A_28))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.35/1.24  tff(c_248, plain, (![A_84]: (k2_xboole_0(A_84, '#skF_4')=k1_ordinal1(A_84))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_32])).
% 2.35/1.24  tff(c_14, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.35/1.24  tff(c_71, plain, (![A_41, B_42]: (k2_xboole_0(A_41, B_42)=B_42 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.35/1.24  tff(c_75, plain, (![B_9]: (k2_xboole_0(B_9, B_9)=B_9)), inference(resolution, [status(thm)], [c_14, c_71])).
% 2.35/1.24  tff(c_255, plain, (k1_ordinal1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_248, c_75])).
% 2.35/1.24  tff(c_265, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_255])).
% 2.35/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.24  
% 2.35/1.24  Inference rules
% 2.35/1.24  ----------------------
% 2.35/1.24  #Ref     : 0
% 2.35/1.24  #Sup     : 43
% 2.35/1.24  #Fact    : 0
% 2.35/1.24  #Define  : 0
% 2.35/1.24  #Split   : 0
% 2.35/1.24  #Chain   : 0
% 2.35/1.24  #Close   : 0
% 2.35/1.24  
% 2.35/1.24  Ordering : KBO
% 2.35/1.24  
% 2.35/1.24  Simplification rules
% 2.35/1.24  ----------------------
% 2.35/1.24  #Subsume      : 8
% 2.35/1.24  #Demod        : 13
% 2.35/1.24  #Tautology    : 22
% 2.35/1.24  #SimpNegUnit  : 3
% 2.35/1.24  #BackRed      : 5
% 2.35/1.24  
% 2.35/1.24  #Partial instantiations: 0
% 2.35/1.24  #Strategies tried      : 1
% 2.35/1.24  
% 2.35/1.24  Timing (in seconds)
% 2.35/1.24  ----------------------
% 2.39/1.24  Preprocessing        : 0.31
% 2.39/1.24  Parsing              : 0.16
% 2.39/1.24  CNF conversion       : 0.02
% 2.39/1.24  Main loop            : 0.17
% 2.39/1.24  Inferencing          : 0.07
% 2.39/1.24  Reduction            : 0.05
% 2.39/1.24  Demodulation         : 0.03
% 2.39/1.24  BG Simplification    : 0.01
% 2.39/1.24  Subsumption          : 0.03
% 2.39/1.24  Abstraction          : 0.01
% 2.39/1.24  MUC search           : 0.00
% 2.39/1.24  Cooper               : 0.00
% 2.39/1.24  Total                : 0.51
% 2.39/1.25  Index Insertion      : 0.00
% 2.39/1.25  Index Deletion       : 0.00
% 2.39/1.25  Index Matching       : 0.00
% 2.39/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
