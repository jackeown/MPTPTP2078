%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:37 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   39 (  41 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   48 (  54 expanded)
%              Number of equality atoms :   17 (  18 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_52,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_28,plain,(
    r1_setfam_1('#skF_4',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [A_12,B_13,C_22] :
      ( r2_hidden('#skF_3'(A_12,B_13,C_22),B_13)
      | ~ r2_hidden(C_22,A_12)
      | ~ r1_setfam_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_137,plain,(
    ! [A_49,B_50,C_51] :
      ( r2_hidden('#skF_3'(A_49,B_50,C_51),B_50)
      | ~ r2_hidden(C_51,A_49)
      | ~ r1_setfam_1(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_55,plain,(
    ! [A_28,B_29] :
      ( k2_xboole_0(k1_tarski(A_28),B_29) = B_29
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_62,plain,(
    ! [A_28] :
      ( k1_tarski(A_28) = k1_xboole_0
      | ~ r2_hidden(A_28,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_4])).

tff(c_143,plain,(
    ! [A_52,C_53] :
      ( k1_tarski('#skF_3'(A_52,k1_xboole_0,C_53)) = k1_xboole_0
      | ~ r2_hidden(C_53,A_52)
      | ~ r1_setfam_1(A_52,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_137,c_62])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( ~ r2_hidden(B_11,A_10)
      | k4_xboole_0(A_10,k1_tarski(B_11)) != A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_152,plain,(
    ! [A_52,C_53,A_10] :
      ( ~ r2_hidden('#skF_3'(A_52,k1_xboole_0,C_53),A_10)
      | k4_xboole_0(A_10,k1_xboole_0) != A_10
      | ~ r2_hidden(C_53,A_52)
      | ~ r1_setfam_1(A_52,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_14])).

tff(c_169,plain,(
    ! [A_54,C_55,A_56] :
      ( ~ r2_hidden('#skF_3'(A_54,k1_xboole_0,C_55),A_56)
      | ~ r2_hidden(C_55,A_54)
      | ~ r1_setfam_1(A_54,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_152])).

tff(c_175,plain,(
    ! [C_57,A_58] :
      ( ~ r2_hidden(C_57,A_58)
      | ~ r1_setfam_1(A_58,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_169])).

tff(c_188,plain,(
    ! [A_59] :
      ( ~ r1_setfam_1(A_59,k1_xboole_0)
      | k1_xboole_0 = A_59 ) ),
    inference(resolution,[status(thm)],[c_2,c_175])).

tff(c_195,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_28,c_188])).

tff(c_201,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_195])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:12:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.17  
% 1.81/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.17  %$ r2_hidden > r1_tarski > r1_setfam_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2
% 1.81/1.17  
% 1.81/1.17  %Foreground sorts:
% 1.81/1.17  
% 1.81/1.17  
% 1.81/1.17  %Background operators:
% 1.81/1.17  
% 1.81/1.17  
% 1.81/1.17  %Foreground operators:
% 1.81/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.17  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.81/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.81/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.81/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.81/1.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.81/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.81/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.81/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.81/1.17  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.81/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.81/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.81/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.81/1.17  
% 1.81/1.18  tff(f_69, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_setfam_1)).
% 1.81/1.18  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.81/1.18  tff(f_64, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 1.81/1.18  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.81/1.18  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 1.81/1.18  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 1.81/1.18  tff(f_52, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.81/1.18  tff(c_26, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.81/1.18  tff(c_28, plain, (r1_setfam_1('#skF_4', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.81/1.18  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.81/1.18  tff(c_20, plain, (![A_12, B_13, C_22]: (r2_hidden('#skF_3'(A_12, B_13, C_22), B_13) | ~r2_hidden(C_22, A_12) | ~r1_setfam_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.81/1.18  tff(c_8, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.81/1.18  tff(c_137, plain, (![A_49, B_50, C_51]: (r2_hidden('#skF_3'(A_49, B_50, C_51), B_50) | ~r2_hidden(C_51, A_49) | ~r1_setfam_1(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.81/1.18  tff(c_55, plain, (![A_28, B_29]: (k2_xboole_0(k1_tarski(A_28), B_29)=B_29 | ~r2_hidden(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.81/1.18  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.81/1.18  tff(c_62, plain, (![A_28]: (k1_tarski(A_28)=k1_xboole_0 | ~r2_hidden(A_28, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_55, c_4])).
% 1.81/1.18  tff(c_143, plain, (![A_52, C_53]: (k1_tarski('#skF_3'(A_52, k1_xboole_0, C_53))=k1_xboole_0 | ~r2_hidden(C_53, A_52) | ~r1_setfam_1(A_52, k1_xboole_0))), inference(resolution, [status(thm)], [c_137, c_62])).
% 1.81/1.18  tff(c_14, plain, (![B_11, A_10]: (~r2_hidden(B_11, A_10) | k4_xboole_0(A_10, k1_tarski(B_11))!=A_10)), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.81/1.18  tff(c_152, plain, (![A_52, C_53, A_10]: (~r2_hidden('#skF_3'(A_52, k1_xboole_0, C_53), A_10) | k4_xboole_0(A_10, k1_xboole_0)!=A_10 | ~r2_hidden(C_53, A_52) | ~r1_setfam_1(A_52, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_143, c_14])).
% 1.81/1.18  tff(c_169, plain, (![A_54, C_55, A_56]: (~r2_hidden('#skF_3'(A_54, k1_xboole_0, C_55), A_56) | ~r2_hidden(C_55, A_54) | ~r1_setfam_1(A_54, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_152])).
% 1.81/1.18  tff(c_175, plain, (![C_57, A_58]: (~r2_hidden(C_57, A_58) | ~r1_setfam_1(A_58, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_169])).
% 1.81/1.18  tff(c_188, plain, (![A_59]: (~r1_setfam_1(A_59, k1_xboole_0) | k1_xboole_0=A_59)), inference(resolution, [status(thm)], [c_2, c_175])).
% 1.81/1.18  tff(c_195, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_28, c_188])).
% 1.81/1.18  tff(c_201, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_195])).
% 1.81/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.18  
% 1.81/1.18  Inference rules
% 1.81/1.18  ----------------------
% 1.81/1.18  #Ref     : 0
% 1.81/1.18  #Sup     : 35
% 1.81/1.18  #Fact    : 0
% 1.81/1.18  #Define  : 0
% 1.81/1.18  #Split   : 0
% 1.81/1.18  #Chain   : 0
% 1.81/1.18  #Close   : 0
% 1.81/1.18  
% 1.81/1.18  Ordering : KBO
% 1.81/1.18  
% 1.81/1.18  Simplification rules
% 1.81/1.18  ----------------------
% 1.81/1.18  #Subsume      : 3
% 1.81/1.18  #Demod        : 8
% 1.81/1.18  #Tautology    : 22
% 1.81/1.18  #SimpNegUnit  : 1
% 1.81/1.18  #BackRed      : 0
% 1.81/1.18  
% 1.81/1.18  #Partial instantiations: 0
% 1.81/1.18  #Strategies tried      : 1
% 1.81/1.18  
% 1.81/1.18  Timing (in seconds)
% 1.81/1.18  ----------------------
% 1.81/1.18  Preprocessing        : 0.28
% 1.81/1.18  Parsing              : 0.14
% 1.81/1.18  CNF conversion       : 0.02
% 1.81/1.18  Main loop            : 0.14
% 1.81/1.18  Inferencing          : 0.06
% 1.81/1.18  Reduction            : 0.04
% 1.81/1.18  Demodulation         : 0.03
% 1.81/1.19  BG Simplification    : 0.01
% 1.81/1.19  Subsumption          : 0.02
% 1.81/1.19  Abstraction          : 0.01
% 1.81/1.19  MUC search           : 0.00
% 1.81/1.19  Cooper               : 0.00
% 1.81/1.19  Total                : 0.44
% 1.81/1.19  Index Insertion      : 0.00
% 1.81/1.19  Index Deletion       : 0.00
% 1.81/1.19  Index Matching       : 0.00
% 1.81/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
