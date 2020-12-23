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
% DateTime   : Thu Dec  3 10:08:50 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   27 (  30 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   39 (  52 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

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

tff(f_64,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(c_16,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

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

tff(c_48,plain,(
    ! [D_31,A_32,B_33] :
      ( ~ r2_hidden(D_31,'#skF_3'(A_32,B_33))
      | ~ r2_hidden(D_31,B_33)
      | ~ r2_hidden(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_81,plain,(
    ! [A_44,B_45,B_46] :
      ( ~ r2_hidden('#skF_1'('#skF_3'(A_44,B_45),B_46),B_45)
      | ~ r2_hidden(A_44,B_45)
      | r1_xboole_0('#skF_3'(A_44,B_45),B_46) ) ),
    inference(resolution,[status(thm)],[c_6,c_48])).

tff(c_87,plain,(
    ! [A_47,B_48] :
      ( ~ r2_hidden(A_47,B_48)
      | r1_xboole_0('#skF_3'(A_47,B_48),B_48) ) ),
    inference(resolution,[status(thm)],[c_4,c_81])).

tff(c_26,plain,(
    ! [A_19,B_20] :
      ( r2_hidden('#skF_3'(A_19,B_20),B_20)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_14,plain,(
    ! [B_16] :
      ( ~ r1_xboole_0(B_16,'#skF_4')
      | ~ r2_hidden(B_16,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_31,plain,(
    ! [A_19] :
      ( ~ r1_xboole_0('#skF_3'(A_19,'#skF_4'),'#skF_4')
      | ~ r2_hidden(A_19,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_14])).

tff(c_96,plain,(
    ! [A_49] : ~ r2_hidden(A_49,'#skF_4') ),
    inference(resolution,[status(thm)],[c_87,c_31])).

tff(c_112,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8,c_96])).

tff(c_119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_112])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:36:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.20  
% 1.79/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.20  %$ r2_hidden > r1_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.79/1.20  
% 1.79/1.20  %Foreground sorts:
% 1.79/1.20  
% 1.79/1.20  
% 1.79/1.20  %Background operators:
% 1.79/1.20  
% 1.79/1.20  
% 1.79/1.20  %Foreground operators:
% 1.79/1.20  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.79/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.79/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.79/1.20  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.79/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.79/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.79/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.79/1.20  
% 1.79/1.21  tff(f_75, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_mcart_1)).
% 1.79/1.21  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.79/1.21  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.79/1.21  tff(f_64, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 1.79/1.21  tff(c_16, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.79/1.21  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.79/1.21  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.79/1.21  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.79/1.21  tff(c_48, plain, (![D_31, A_32, B_33]: (~r2_hidden(D_31, '#skF_3'(A_32, B_33)) | ~r2_hidden(D_31, B_33) | ~r2_hidden(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.79/1.21  tff(c_81, plain, (![A_44, B_45, B_46]: (~r2_hidden('#skF_1'('#skF_3'(A_44, B_45), B_46), B_45) | ~r2_hidden(A_44, B_45) | r1_xboole_0('#skF_3'(A_44, B_45), B_46))), inference(resolution, [status(thm)], [c_6, c_48])).
% 1.79/1.21  tff(c_87, plain, (![A_47, B_48]: (~r2_hidden(A_47, B_48) | r1_xboole_0('#skF_3'(A_47, B_48), B_48))), inference(resolution, [status(thm)], [c_4, c_81])).
% 1.79/1.21  tff(c_26, plain, (![A_19, B_20]: (r2_hidden('#skF_3'(A_19, B_20), B_20) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.79/1.21  tff(c_14, plain, (![B_16]: (~r1_xboole_0(B_16, '#skF_4') | ~r2_hidden(B_16, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.79/1.21  tff(c_31, plain, (![A_19]: (~r1_xboole_0('#skF_3'(A_19, '#skF_4'), '#skF_4') | ~r2_hidden(A_19, '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_14])).
% 1.79/1.21  tff(c_96, plain, (![A_49]: (~r2_hidden(A_49, '#skF_4'))), inference(resolution, [status(thm)], [c_87, c_31])).
% 1.79/1.21  tff(c_112, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_8, c_96])).
% 1.79/1.21  tff(c_119, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_112])).
% 1.79/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.21  
% 1.79/1.21  Inference rules
% 1.79/1.21  ----------------------
% 1.79/1.21  #Ref     : 0
% 1.79/1.21  #Sup     : 17
% 1.79/1.21  #Fact    : 0
% 1.79/1.21  #Define  : 0
% 1.79/1.21  #Split   : 0
% 1.79/1.21  #Chain   : 0
% 1.79/1.21  #Close   : 0
% 1.79/1.21  
% 1.79/1.21  Ordering : KBO
% 1.79/1.21  
% 1.79/1.21  Simplification rules
% 1.79/1.21  ----------------------
% 1.79/1.21  #Subsume      : 5
% 1.79/1.21  #Demod        : 0
% 1.79/1.21  #Tautology    : 0
% 1.79/1.21  #SimpNegUnit  : 2
% 1.79/1.21  #BackRed      : 0
% 1.79/1.21  
% 1.79/1.21  #Partial instantiations: 0
% 1.79/1.21  #Strategies tried      : 1
% 1.79/1.21  
% 1.79/1.21  Timing (in seconds)
% 1.79/1.21  ----------------------
% 1.90/1.21  Preprocessing        : 0.27
% 1.90/1.21  Parsing              : 0.15
% 1.90/1.21  CNF conversion       : 0.02
% 1.90/1.21  Main loop            : 0.12
% 1.90/1.21  Inferencing          : 0.06
% 1.90/1.21  Reduction            : 0.02
% 1.90/1.21  Demodulation         : 0.01
% 1.90/1.21  BG Simplification    : 0.01
% 1.90/1.21  Subsumption          : 0.02
% 1.90/1.21  Abstraction          : 0.01
% 1.90/1.21  MUC search           : 0.00
% 1.90/1.21  Cooper               : 0.00
% 1.90/1.21  Total                : 0.41
% 1.90/1.21  Index Insertion      : 0.00
% 1.90/1.21  Index Deletion       : 0.00
% 1.90/1.21  Index Matching       : 0.00
% 1.90/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
