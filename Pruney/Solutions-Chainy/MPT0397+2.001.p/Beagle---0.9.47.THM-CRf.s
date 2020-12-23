%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:31 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   35 (  39 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :   58 (  72 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_setfam_1 > r2_hidden > r1_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r2_setfam_1,type,(
    r2_setfam_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_setfam_1(B,A)
       => ( A = k1_xboole_0
          | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_setfam_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(B,C) )
     => ( A = k1_xboole_0
        | r1_tarski(B,k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,B)
            & ! [D] :
                ~ ( r2_hidden(D,A)
                  & r1_tarski(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_setfam_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_22,plain,(
    r2_setfam_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16,plain,(
    ! [A_18,B_19] :
      ( r2_hidden('#skF_3'(A_18,B_19),A_18)
      | r1_tarski(B_19,k1_setfam_1(A_18))
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [A_4,B_5,C_14] :
      ( r2_hidden('#skF_2'(A_4,B_5,C_14),A_4)
      | ~ r2_hidden(C_14,B_5)
      | ~ r2_setfam_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_setfam_1(B_17),A_16)
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_57,plain,(
    ! [A_41,B_42,C_43] :
      ( r1_tarski('#skF_2'(A_41,B_42,C_43),C_43)
      | ~ r2_hidden(C_43,B_42)
      | ~ r2_setfam_1(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_97,plain,(
    ! [A_59,C_60,A_61,B_62] :
      ( r1_tarski(A_59,C_60)
      | ~ r1_tarski(A_59,'#skF_2'(A_61,B_62,C_60))
      | ~ r2_hidden(C_60,B_62)
      | ~ r2_setfam_1(A_61,B_62) ) ),
    inference(resolution,[status(thm)],[c_57,c_2])).

tff(c_108,plain,(
    ! [B_63,C_64,B_65,A_66] :
      ( r1_tarski(k1_setfam_1(B_63),C_64)
      | ~ r2_hidden(C_64,B_65)
      | ~ r2_setfam_1(A_66,B_65)
      | ~ r2_hidden('#skF_2'(A_66,B_65,C_64),B_63) ) ),
    inference(resolution,[status(thm)],[c_12,c_97])).

tff(c_113,plain,(
    ! [A_67,C_68,B_69] :
      ( r1_tarski(k1_setfam_1(A_67),C_68)
      | ~ r2_hidden(C_68,B_69)
      | ~ r2_setfam_1(A_67,B_69) ) ),
    inference(resolution,[status(thm)],[c_6,c_108])).

tff(c_132,plain,(
    ! [A_76,A_77,B_78] :
      ( r1_tarski(k1_setfam_1(A_76),'#skF_3'(A_77,B_78))
      | ~ r2_setfam_1(A_76,A_77)
      | r1_tarski(B_78,k1_setfam_1(A_77))
      | k1_xboole_0 = A_77 ) ),
    inference(resolution,[status(thm)],[c_16,c_113])).

tff(c_14,plain,(
    ! [B_19,A_18] :
      ( ~ r1_tarski(B_19,'#skF_3'(A_18,B_19))
      | r1_tarski(B_19,k1_setfam_1(A_18))
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_146,plain,(
    ! [A_83,A_84] :
      ( ~ r2_setfam_1(A_83,A_84)
      | r1_tarski(k1_setfam_1(A_83),k1_setfam_1(A_84))
      | k1_xboole_0 = A_84 ) ),
    inference(resolution,[status(thm)],[c_132,c_14])).

tff(c_18,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_5'),k1_setfam_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_153,plain,
    ( ~ r2_setfam_1('#skF_5','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_146,c_18])).

tff(c_158,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_153])).

tff(c_160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_158])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:01:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.22  
% 1.91/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.22  %$ r2_setfam_1 > r2_hidden > r1_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_4 > #skF_1
% 1.91/1.22  
% 1.91/1.22  %Foreground sorts:
% 1.91/1.22  
% 1.91/1.22  
% 1.91/1.22  %Background operators:
% 1.91/1.22  
% 1.91/1.22  
% 1.91/1.22  %Foreground operators:
% 1.91/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.91/1.22  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.91/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.22  tff('#skF_5', type, '#skF_5': $i).
% 1.91/1.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.91/1.22  tff(r2_setfam_1, type, r2_setfam_1: ($i * $i) > $o).
% 1.91/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.91/1.22  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.91/1.22  
% 1.91/1.23  tff(f_63, negated_conjecture, ~(![A, B]: (r2_setfam_1(B, A) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_setfam_1)).
% 1.91/1.23  tff(f_56, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(B, C))) => ((A = k1_xboole_0) | r1_tarski(B, k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_setfam_1)).
% 1.91/1.23  tff(f_43, axiom, (![A, B]: (r2_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, A) & r1_tarski(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_setfam_1)).
% 1.91/1.23  tff(f_47, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 1.91/1.23  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.91/1.23  tff(c_20, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.91/1.23  tff(c_22, plain, (r2_setfam_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.91/1.23  tff(c_16, plain, (![A_18, B_19]: (r2_hidden('#skF_3'(A_18, B_19), A_18) | r1_tarski(B_19, k1_setfam_1(A_18)) | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.91/1.23  tff(c_6, plain, (![A_4, B_5, C_14]: (r2_hidden('#skF_2'(A_4, B_5, C_14), A_4) | ~r2_hidden(C_14, B_5) | ~r2_setfam_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.91/1.23  tff(c_12, plain, (![B_17, A_16]: (r1_tarski(k1_setfam_1(B_17), A_16) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.91/1.23  tff(c_57, plain, (![A_41, B_42, C_43]: (r1_tarski('#skF_2'(A_41, B_42, C_43), C_43) | ~r2_hidden(C_43, B_42) | ~r2_setfam_1(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.91/1.23  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.91/1.23  tff(c_97, plain, (![A_59, C_60, A_61, B_62]: (r1_tarski(A_59, C_60) | ~r1_tarski(A_59, '#skF_2'(A_61, B_62, C_60)) | ~r2_hidden(C_60, B_62) | ~r2_setfam_1(A_61, B_62))), inference(resolution, [status(thm)], [c_57, c_2])).
% 1.91/1.23  tff(c_108, plain, (![B_63, C_64, B_65, A_66]: (r1_tarski(k1_setfam_1(B_63), C_64) | ~r2_hidden(C_64, B_65) | ~r2_setfam_1(A_66, B_65) | ~r2_hidden('#skF_2'(A_66, B_65, C_64), B_63))), inference(resolution, [status(thm)], [c_12, c_97])).
% 1.91/1.23  tff(c_113, plain, (![A_67, C_68, B_69]: (r1_tarski(k1_setfam_1(A_67), C_68) | ~r2_hidden(C_68, B_69) | ~r2_setfam_1(A_67, B_69))), inference(resolution, [status(thm)], [c_6, c_108])).
% 1.91/1.23  tff(c_132, plain, (![A_76, A_77, B_78]: (r1_tarski(k1_setfam_1(A_76), '#skF_3'(A_77, B_78)) | ~r2_setfam_1(A_76, A_77) | r1_tarski(B_78, k1_setfam_1(A_77)) | k1_xboole_0=A_77)), inference(resolution, [status(thm)], [c_16, c_113])).
% 1.91/1.23  tff(c_14, plain, (![B_19, A_18]: (~r1_tarski(B_19, '#skF_3'(A_18, B_19)) | r1_tarski(B_19, k1_setfam_1(A_18)) | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.91/1.23  tff(c_146, plain, (![A_83, A_84]: (~r2_setfam_1(A_83, A_84) | r1_tarski(k1_setfam_1(A_83), k1_setfam_1(A_84)) | k1_xboole_0=A_84)), inference(resolution, [status(thm)], [c_132, c_14])).
% 1.91/1.23  tff(c_18, plain, (~r1_tarski(k1_setfam_1('#skF_5'), k1_setfam_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.91/1.23  tff(c_153, plain, (~r2_setfam_1('#skF_5', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_146, c_18])).
% 1.91/1.23  tff(c_158, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_153])).
% 1.91/1.23  tff(c_160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_158])).
% 1.91/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.23  
% 1.91/1.23  Inference rules
% 1.91/1.23  ----------------------
% 1.91/1.23  #Ref     : 0
% 1.91/1.23  #Sup     : 30
% 1.91/1.23  #Fact    : 0
% 1.91/1.23  #Define  : 0
% 1.91/1.23  #Split   : 0
% 1.91/1.23  #Chain   : 0
% 1.91/1.23  #Close   : 0
% 1.91/1.23  
% 1.91/1.23  Ordering : KBO
% 1.91/1.23  
% 1.91/1.23  Simplification rules
% 1.91/1.23  ----------------------
% 1.91/1.23  #Subsume      : 2
% 1.91/1.23  #Demod        : 1
% 1.91/1.23  #Tautology    : 1
% 1.91/1.23  #SimpNegUnit  : 1
% 1.91/1.23  #BackRed      : 0
% 1.91/1.23  
% 1.91/1.23  #Partial instantiations: 0
% 1.91/1.23  #Strategies tried      : 1
% 1.91/1.23  
% 1.91/1.23  Timing (in seconds)
% 1.91/1.23  ----------------------
% 2.03/1.23  Preprocessing        : 0.28
% 2.03/1.23  Parsing              : 0.15
% 2.03/1.23  CNF conversion       : 0.02
% 2.03/1.23  Main loop            : 0.19
% 2.03/1.23  Inferencing          : 0.08
% 2.03/1.23  Reduction            : 0.04
% 2.03/1.23  Demodulation         : 0.03
% 2.03/1.23  BG Simplification    : 0.01
% 2.03/1.23  Subsumption          : 0.04
% 2.03/1.23  Abstraction          : 0.01
% 2.03/1.23  MUC search           : 0.00
% 2.03/1.23  Cooper               : 0.00
% 2.03/1.23  Total                : 0.49
% 2.03/1.23  Index Insertion      : 0.00
% 2.03/1.23  Index Deletion       : 0.00
% 2.03/1.23  Index Matching       : 0.00
% 2.03/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
