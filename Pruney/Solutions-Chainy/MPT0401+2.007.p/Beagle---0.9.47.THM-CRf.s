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
% DateTime   : Thu Dec  3 09:57:39 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   49 (  53 expanded)
%              Number of leaves         :   28 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   52 (  64 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_setfam_1(B,k1_tarski(A))
       => ! [C] :
            ( r2_hidden(C,B)
           => r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_34,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_54,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_setfam_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(c_40,plain,(
    ~ r1_tarski('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_44,plain,(
    r1_setfam_1('#skF_7',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_6] : k2_xboole_0(A_6,A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_72,plain,(
    ! [A_46,B_47] : k3_tarski(k2_tarski(A_46,B_47)) = k2_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_81,plain,(
    ! [A_8] : k3_tarski(k1_tarski(A_8)) = k2_xboole_0(A_8,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_72])).

tff(c_84,plain,(
    ! [A_8] : k3_tarski(k1_tarski(A_8)) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_81])).

tff(c_102,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(k3_tarski(A_54),k3_tarski(B_55))
      | ~ r1_setfam_1(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_108,plain,(
    ! [A_54,A_8] :
      ( r1_tarski(k3_tarski(A_54),A_8)
      | ~ r1_setfam_1(A_54,k1_tarski(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_102])).

tff(c_42,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_163,plain,(
    ! [C_71,A_72,D_73] :
      ( r2_hidden(C_71,k3_tarski(A_72))
      | ~ r2_hidden(D_73,A_72)
      | ~ r2_hidden(C_71,D_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_173,plain,(
    ! [C_74] :
      ( r2_hidden(C_74,k3_tarski('#skF_7'))
      | ~ r2_hidden(C_74,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_42,c_163])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_203,plain,(
    ! [C_77,B_78] :
      ( r2_hidden(C_77,B_78)
      | ~ r1_tarski(k3_tarski('#skF_7'),B_78)
      | ~ r2_hidden(C_77,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_173,c_2])).

tff(c_286,plain,(
    ! [C_86,A_87] :
      ( r2_hidden(C_86,A_87)
      | ~ r2_hidden(C_86,'#skF_8')
      | ~ r1_setfam_1('#skF_7',k1_tarski(A_87)) ) ),
    inference(resolution,[status(thm)],[c_108,c_203])).

tff(c_714,plain,(
    ! [B_161,A_162] :
      ( r2_hidden('#skF_1'('#skF_8',B_161),A_162)
      | ~ r1_setfam_1('#skF_7',k1_tarski(A_162))
      | r1_tarski('#skF_8',B_161) ) ),
    inference(resolution,[status(thm)],[c_6,c_286])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_752,plain,(
    ! [A_163] :
      ( ~ r1_setfam_1('#skF_7',k1_tarski(A_163))
      | r1_tarski('#skF_8',A_163) ) ),
    inference(resolution,[status(thm)],[c_714,c_4])).

tff(c_755,plain,(
    r1_tarski('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_752])).

tff(c_759,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_755])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:57:01 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.09/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.48  
% 3.09/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.48  %$ r2_hidden > r1_tarski > r1_setfam_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 3.09/1.48  
% 3.09/1.48  %Foreground sorts:
% 3.09/1.48  
% 3.09/1.48  
% 3.09/1.48  %Background operators:
% 3.09/1.48  
% 3.09/1.48  
% 3.09/1.48  %Foreground operators:
% 3.09/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.09/1.48  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 3.09/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.09/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.09/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.09/1.48  tff('#skF_7', type, '#skF_7': $i).
% 3.09/1.48  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.09/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.09/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.09/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.09/1.48  tff('#skF_6', type, '#skF_6': $i).
% 3.09/1.48  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.09/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.09/1.48  tff('#skF_8', type, '#skF_8': $i).
% 3.09/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.09/1.48  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.09/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.09/1.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.09/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.09/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.09/1.48  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.09/1.48  
% 3.09/1.49  tff(f_66, negated_conjecture, ~(![A, B]: (r1_setfam_1(B, k1_tarski(A)) => (![C]: (r2_hidden(C, B) => r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_setfam_1)).
% 3.09/1.49  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.09/1.49  tff(f_34, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.09/1.49  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.09/1.49  tff(f_54, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.09/1.49  tff(f_58, axiom, (![A, B]: (r1_setfam_1(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_setfam_1)).
% 3.09/1.49  tff(f_52, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 3.09/1.49  tff(c_40, plain, (~r1_tarski('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.09/1.49  tff(c_44, plain, (r1_setfam_1('#skF_7', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.09/1.49  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.09/1.49  tff(c_8, plain, (![A_6]: (k2_xboole_0(A_6, A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.09/1.49  tff(c_10, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.09/1.49  tff(c_72, plain, (![A_46, B_47]: (k3_tarski(k2_tarski(A_46, B_47))=k2_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.09/1.49  tff(c_81, plain, (![A_8]: (k3_tarski(k1_tarski(A_8))=k2_xboole_0(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_10, c_72])).
% 3.09/1.49  tff(c_84, plain, (![A_8]: (k3_tarski(k1_tarski(A_8))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_81])).
% 3.09/1.49  tff(c_102, plain, (![A_54, B_55]: (r1_tarski(k3_tarski(A_54), k3_tarski(B_55)) | ~r1_setfam_1(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.09/1.49  tff(c_108, plain, (![A_54, A_8]: (r1_tarski(k3_tarski(A_54), A_8) | ~r1_setfam_1(A_54, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_84, c_102])).
% 3.09/1.49  tff(c_42, plain, (r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.09/1.49  tff(c_163, plain, (![C_71, A_72, D_73]: (r2_hidden(C_71, k3_tarski(A_72)) | ~r2_hidden(D_73, A_72) | ~r2_hidden(C_71, D_73))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.09/1.49  tff(c_173, plain, (![C_74]: (r2_hidden(C_74, k3_tarski('#skF_7')) | ~r2_hidden(C_74, '#skF_8'))), inference(resolution, [status(thm)], [c_42, c_163])).
% 3.09/1.49  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.09/1.49  tff(c_203, plain, (![C_77, B_78]: (r2_hidden(C_77, B_78) | ~r1_tarski(k3_tarski('#skF_7'), B_78) | ~r2_hidden(C_77, '#skF_8'))), inference(resolution, [status(thm)], [c_173, c_2])).
% 3.09/1.49  tff(c_286, plain, (![C_86, A_87]: (r2_hidden(C_86, A_87) | ~r2_hidden(C_86, '#skF_8') | ~r1_setfam_1('#skF_7', k1_tarski(A_87)))), inference(resolution, [status(thm)], [c_108, c_203])).
% 3.09/1.49  tff(c_714, plain, (![B_161, A_162]: (r2_hidden('#skF_1'('#skF_8', B_161), A_162) | ~r1_setfam_1('#skF_7', k1_tarski(A_162)) | r1_tarski('#skF_8', B_161))), inference(resolution, [status(thm)], [c_6, c_286])).
% 3.09/1.49  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.09/1.49  tff(c_752, plain, (![A_163]: (~r1_setfam_1('#skF_7', k1_tarski(A_163)) | r1_tarski('#skF_8', A_163))), inference(resolution, [status(thm)], [c_714, c_4])).
% 3.09/1.49  tff(c_755, plain, (r1_tarski('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_44, c_752])).
% 3.09/1.49  tff(c_759, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_755])).
% 3.09/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.49  
% 3.09/1.49  Inference rules
% 3.09/1.49  ----------------------
% 3.09/1.49  #Ref     : 0
% 3.09/1.49  #Sup     : 175
% 3.09/1.49  #Fact    : 0
% 3.09/1.49  #Define  : 0
% 3.09/1.49  #Split   : 6
% 3.09/1.49  #Chain   : 0
% 3.09/1.49  #Close   : 0
% 3.09/1.49  
% 3.09/1.49  Ordering : KBO
% 3.09/1.49  
% 3.09/1.49  Simplification rules
% 3.09/1.49  ----------------------
% 3.09/1.49  #Subsume      : 27
% 3.09/1.49  #Demod        : 14
% 3.09/1.49  #Tautology    : 17
% 3.09/1.49  #SimpNegUnit  : 1
% 3.09/1.49  #BackRed      : 0
% 3.09/1.49  
% 3.09/1.49  #Partial instantiations: 0
% 3.09/1.49  #Strategies tried      : 1
% 3.09/1.49  
% 3.09/1.49  Timing (in seconds)
% 3.09/1.49  ----------------------
% 3.09/1.49  Preprocessing        : 0.33
% 3.09/1.49  Parsing              : 0.17
% 3.09/1.49  CNF conversion       : 0.03
% 3.09/1.49  Main loop            : 0.41
% 3.09/1.49  Inferencing          : 0.14
% 3.09/1.49  Reduction            : 0.11
% 3.09/1.49  Demodulation         : 0.07
% 3.09/1.49  BG Simplification    : 0.02
% 3.09/1.49  Subsumption          : 0.11
% 3.09/1.49  Abstraction          : 0.02
% 3.09/1.49  MUC search           : 0.00
% 3.09/1.49  Cooper               : 0.00
% 3.09/1.49  Total                : 0.76
% 3.09/1.49  Index Insertion      : 0.00
% 3.09/1.49  Index Deletion       : 0.00
% 3.09/1.49  Index Matching       : 0.00
% 3.09/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
