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
% DateTime   : Thu Dec  3 09:57:35 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   47 (  48 expanded)
%              Number of leaves         :   28 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   44 (  46 expanded)
%              Number of equality atoms :   21 (  22 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_35,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_38,plain,(
    r1_setfam_1('#skF_4',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4,plain,(
    ! [A_3] :
      ( r2_hidden('#skF_1'(A_3),A_3)
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_203,plain,(
    ! [A_68,B_69,C_70] :
      ( r2_hidden('#skF_3'(A_68,B_69,C_70),B_69)
      | ~ r2_hidden(C_70,A_68)
      | ~ r1_setfam_1(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10,plain,(
    ! [A_8] : k5_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_122,plain,(
    ! [A_51,B_52] : k5_xboole_0(A_51,k3_xboole_0(A_51,B_52)) = k4_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_131,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_122])).

tff(c_134,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_131])).

tff(c_22,plain,(
    ! [B_18] : k4_xboole_0(k1_tarski(B_18),k1_tarski(B_18)) != k1_tarski(B_18) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_135,plain,(
    ! [B_18] : k1_tarski(B_18) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_22])).

tff(c_76,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(k1_tarski(A_42),B_43)
      | ~ r2_hidden(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_85,plain,(
    ! [A_42] :
      ( k1_tarski(A_42) = k1_xboole_0
      | ~ r2_hidden(A_42,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_76,c_8])).

tff(c_143,plain,(
    ! [A_42] : ~ r2_hidden(A_42,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_85])).

tff(c_209,plain,(
    ! [C_71,A_72] :
      ( ~ r2_hidden(C_71,A_72)
      | ~ r1_setfam_1(A_72,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_203,c_143])).

tff(c_222,plain,(
    ! [A_73] :
      ( ~ r1_setfam_1(A_73,k1_xboole_0)
      | k1_xboole_0 = A_73 ) ),
    inference(resolution,[status(thm)],[c_4,c_209])).

tff(c_229,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_222])).

tff(c_235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_229])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:01:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.31  
% 2.01/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.32  %$ r2_hidden > r1_tarski > r1_setfam_1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2
% 2.01/1.32  
% 2.01/1.32  %Foreground sorts:
% 2.01/1.32  
% 2.01/1.32  
% 2.01/1.32  %Background operators:
% 2.01/1.32  
% 2.01/1.32  
% 2.01/1.32  %Foreground operators:
% 2.01/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.32  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.01/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.01/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.01/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.01/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.01/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.01/1.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.01/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.01/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.01/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.01/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.01/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.01/1.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.01/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.01/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.01/1.32  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.01/1.32  
% 2.01/1.33  tff(f_77, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_setfam_1)).
% 2.01/1.33  tff(f_35, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.01/1.33  tff(f_70, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 2.01/1.33  tff(f_43, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.01/1.33  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.01/1.33  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.01/1.33  tff(f_58, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.01/1.33  tff(f_53, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.01/1.33  tff(f_41, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.01/1.33  tff(c_36, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.01/1.33  tff(c_38, plain, (r1_setfam_1('#skF_4', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.01/1.33  tff(c_4, plain, (![A_3]: (r2_hidden('#skF_1'(A_3), A_3) | k1_xboole_0=A_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.01/1.33  tff(c_203, plain, (![A_68, B_69, C_70]: (r2_hidden('#skF_3'(A_68, B_69, C_70), B_69) | ~r2_hidden(C_70, A_68) | ~r1_setfam_1(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.01/1.33  tff(c_10, plain, (![A_8]: (k5_xboole_0(A_8, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.01/1.33  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.01/1.33  tff(c_122, plain, (![A_51, B_52]: (k5_xboole_0(A_51, k3_xboole_0(A_51, B_52))=k4_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.01/1.33  tff(c_131, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_122])).
% 2.01/1.33  tff(c_134, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_131])).
% 2.01/1.33  tff(c_22, plain, (![B_18]: (k4_xboole_0(k1_tarski(B_18), k1_tarski(B_18))!=k1_tarski(B_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.01/1.33  tff(c_135, plain, (![B_18]: (k1_tarski(B_18)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_134, c_22])).
% 2.01/1.33  tff(c_76, plain, (![A_42, B_43]: (r1_tarski(k1_tarski(A_42), B_43) | ~r2_hidden(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.01/1.33  tff(c_8, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.01/1.33  tff(c_85, plain, (![A_42]: (k1_tarski(A_42)=k1_xboole_0 | ~r2_hidden(A_42, k1_xboole_0))), inference(resolution, [status(thm)], [c_76, c_8])).
% 2.01/1.33  tff(c_143, plain, (![A_42]: (~r2_hidden(A_42, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_135, c_85])).
% 2.01/1.33  tff(c_209, plain, (![C_71, A_72]: (~r2_hidden(C_71, A_72) | ~r1_setfam_1(A_72, k1_xboole_0))), inference(resolution, [status(thm)], [c_203, c_143])).
% 2.01/1.33  tff(c_222, plain, (![A_73]: (~r1_setfam_1(A_73, k1_xboole_0) | k1_xboole_0=A_73)), inference(resolution, [status(thm)], [c_4, c_209])).
% 2.01/1.33  tff(c_229, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_38, c_222])).
% 2.01/1.33  tff(c_235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_229])).
% 2.01/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.33  
% 2.01/1.33  Inference rules
% 2.01/1.33  ----------------------
% 2.01/1.33  #Ref     : 0
% 2.01/1.33  #Sup     : 38
% 2.01/1.33  #Fact    : 0
% 2.01/1.33  #Define  : 0
% 2.01/1.33  #Split   : 0
% 2.01/1.33  #Chain   : 0
% 2.01/1.33  #Close   : 0
% 2.01/1.33  
% 2.01/1.33  Ordering : KBO
% 2.01/1.33  
% 2.01/1.33  Simplification rules
% 2.01/1.33  ----------------------
% 2.01/1.33  #Subsume      : 0
% 2.01/1.33  #Demod        : 4
% 2.01/1.33  #Tautology    : 27
% 2.01/1.33  #SimpNegUnit  : 5
% 2.01/1.33  #BackRed      : 2
% 2.01/1.33  
% 2.01/1.33  #Partial instantiations: 0
% 2.01/1.33  #Strategies tried      : 1
% 2.01/1.33  
% 2.01/1.33  Timing (in seconds)
% 2.01/1.33  ----------------------
% 2.01/1.33  Preprocessing        : 0.29
% 2.01/1.33  Parsing              : 0.15
% 2.01/1.33  CNF conversion       : 0.02
% 2.01/1.33  Main loop            : 0.22
% 2.01/1.33  Inferencing          : 0.09
% 2.01/1.33  Reduction            : 0.06
% 2.01/1.33  Demodulation         : 0.05
% 2.01/1.33  BG Simplification    : 0.01
% 2.01/1.33  Subsumption          : 0.03
% 2.01/1.33  Abstraction          : 0.01
% 2.01/1.33  MUC search           : 0.00
% 2.01/1.33  Cooper               : 0.00
% 2.01/1.33  Total                : 0.55
% 2.01/1.33  Index Insertion      : 0.00
% 2.01/1.33  Index Deletion       : 0.00
% 2.01/1.33  Index Matching       : 0.00
% 2.01/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
