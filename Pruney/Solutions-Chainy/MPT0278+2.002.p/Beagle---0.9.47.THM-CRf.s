%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:22 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   35 (  40 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   41 (  52 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_26,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_97,plain,(
    ! [A_31,B_32] :
      ( r2_hidden('#skF_1'(A_31,B_32),A_31)
      | r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [C_17,A_13] :
      ( r1_tarski(C_17,A_13)
      | ~ r2_hidden(C_17,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_107,plain,(
    ! [A_13,B_32] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(A_13),B_32),A_13)
      | r1_tarski(k1_zfmisc_1(A_13),B_32) ) ),
    inference(resolution,[status(thm)],[c_97,c_14])).

tff(c_28,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_63,plain,(
    ! [A_22,B_23] :
      ( k2_xboole_0(A_22,B_23) = B_23
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_67,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_28,c_63])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_83,plain,(
    ! [A_28,C_29,B_30] :
      ( r1_tarski(A_28,k2_xboole_0(C_29,B_30))
      | ~ r1_tarski(A_28,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_125,plain,(
    ! [A_35,A_36,B_37] :
      ( r1_tarski(A_35,k2_xboole_0(A_36,B_37))
      | ~ r1_tarski(A_35,A_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_83])).

tff(c_134,plain,(
    ! [A_35] :
      ( r1_tarski(A_35,'#skF_5')
      | ~ r1_tarski(A_35,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_125])).

tff(c_16,plain,(
    ! [C_17,A_13] :
      ( r2_hidden(C_17,k1_zfmisc_1(A_13))
      | ~ r1_tarski(C_17,A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_77,plain,(
    ! [A_26,B_27] :
      ( ~ r2_hidden('#skF_1'(A_26,B_27),B_27)
      | r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_161,plain,(
    ! [A_43,A_44] :
      ( r1_tarski(A_43,k1_zfmisc_1(A_44))
      | ~ r1_tarski('#skF_1'(A_43,k1_zfmisc_1(A_44)),A_44) ) ),
    inference(resolution,[status(thm)],[c_16,c_77])).

tff(c_195,plain,(
    ! [A_47] :
      ( r1_tarski(A_47,k1_zfmisc_1('#skF_5'))
      | ~ r1_tarski('#skF_1'(A_47,k1_zfmisc_1('#skF_5')),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_134,c_161])).

tff(c_199,plain,(
    r1_tarski(k1_zfmisc_1('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_107,c_195])).

tff(c_203,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_26,c_199])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:57:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.36  
% 2.05/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.37  %$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 2.05/1.37  
% 2.05/1.37  %Foreground sorts:
% 2.05/1.37  
% 2.05/1.37  
% 2.05/1.37  %Background operators:
% 2.05/1.37  
% 2.05/1.37  
% 2.05/1.37  %Foreground operators:
% 2.05/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.05/1.37  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.05/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.05/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.05/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.05/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.05/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.05/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.05/1.37  
% 2.15/1.39  tff(f_54, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.15/1.39  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.15/1.39  tff(f_49, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.15/1.39  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.15/1.39  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.15/1.39  tff(f_38, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.15/1.39  tff(c_26, plain, (~r1_tarski(k1_zfmisc_1('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.15/1.39  tff(c_97, plain, (![A_31, B_32]: (r2_hidden('#skF_1'(A_31, B_32), A_31) | r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.15/1.39  tff(c_14, plain, (![C_17, A_13]: (r1_tarski(C_17, A_13) | ~r2_hidden(C_17, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.15/1.39  tff(c_107, plain, (![A_13, B_32]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_13), B_32), A_13) | r1_tarski(k1_zfmisc_1(A_13), B_32))), inference(resolution, [status(thm)], [c_97, c_14])).
% 2.15/1.39  tff(c_28, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.15/1.39  tff(c_63, plain, (![A_22, B_23]: (k2_xboole_0(A_22, B_23)=B_23 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.15/1.39  tff(c_67, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_28, c_63])).
% 2.15/1.39  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.15/1.39  tff(c_83, plain, (![A_28, C_29, B_30]: (r1_tarski(A_28, k2_xboole_0(C_29, B_30)) | ~r1_tarski(A_28, B_30))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.15/1.39  tff(c_125, plain, (![A_35, A_36, B_37]: (r1_tarski(A_35, k2_xboole_0(A_36, B_37)) | ~r1_tarski(A_35, A_36))), inference(superposition, [status(thm), theory('equality')], [c_2, c_83])).
% 2.15/1.39  tff(c_134, plain, (![A_35]: (r1_tarski(A_35, '#skF_5') | ~r1_tarski(A_35, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_67, c_125])).
% 2.15/1.39  tff(c_16, plain, (![C_17, A_13]: (r2_hidden(C_17, k1_zfmisc_1(A_13)) | ~r1_tarski(C_17, A_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.15/1.39  tff(c_77, plain, (![A_26, B_27]: (~r2_hidden('#skF_1'(A_26, B_27), B_27) | r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.15/1.39  tff(c_161, plain, (![A_43, A_44]: (r1_tarski(A_43, k1_zfmisc_1(A_44)) | ~r1_tarski('#skF_1'(A_43, k1_zfmisc_1(A_44)), A_44))), inference(resolution, [status(thm)], [c_16, c_77])).
% 2.15/1.39  tff(c_195, plain, (![A_47]: (r1_tarski(A_47, k1_zfmisc_1('#skF_5')) | ~r1_tarski('#skF_1'(A_47, k1_zfmisc_1('#skF_5')), '#skF_4'))), inference(resolution, [status(thm)], [c_134, c_161])).
% 2.15/1.39  tff(c_199, plain, (r1_tarski(k1_zfmisc_1('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_107, c_195])).
% 2.15/1.39  tff(c_203, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_26, c_199])).
% 2.15/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.39  
% 2.15/1.39  Inference rules
% 2.15/1.39  ----------------------
% 2.15/1.39  #Ref     : 0
% 2.15/1.39  #Sup     : 39
% 2.15/1.39  #Fact    : 0
% 2.15/1.39  #Define  : 0
% 2.15/1.39  #Split   : 0
% 2.15/1.39  #Chain   : 0
% 2.15/1.39  #Close   : 0
% 2.15/1.39  
% 2.15/1.39  Ordering : KBO
% 2.15/1.39  
% 2.15/1.39  Simplification rules
% 2.15/1.39  ----------------------
% 2.15/1.39  #Subsume      : 3
% 2.15/1.39  #Demod        : 4
% 2.15/1.39  #Tautology    : 18
% 2.15/1.39  #SimpNegUnit  : 1
% 2.15/1.39  #BackRed      : 0
% 2.15/1.39  
% 2.15/1.39  #Partial instantiations: 0
% 2.15/1.39  #Strategies tried      : 1
% 2.15/1.39  
% 2.15/1.39  Timing (in seconds)
% 2.15/1.39  ----------------------
% 2.15/1.39  Preprocessing        : 0.31
% 2.15/1.39  Parsing              : 0.17
% 2.15/1.39  CNF conversion       : 0.02
% 2.15/1.39  Main loop            : 0.17
% 2.15/1.39  Inferencing          : 0.07
% 2.15/1.39  Reduction            : 0.05
% 2.15/1.39  Demodulation         : 0.04
% 2.15/1.39  BG Simplification    : 0.02
% 2.15/1.39  Subsumption          : 0.03
% 2.15/1.39  Abstraction          : 0.01
% 2.15/1.39  MUC search           : 0.00
% 2.15/1.39  Cooper               : 0.00
% 2.15/1.39  Total                : 0.52
% 2.15/1.39  Index Insertion      : 0.00
% 2.15/1.39  Index Deletion       : 0.00
% 2.15/1.39  Index Matching       : 0.00
% 2.15/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
