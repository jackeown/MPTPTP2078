%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:22 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   42 (  48 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 (  58 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_51,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_28,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_117,plain,(
    ! [A_32,B_33] :
      ( r2_hidden('#skF_1'(A_32,B_33),A_32)
      | r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [C_17,A_13] :
      ( r1_tarski(C_17,A_13)
      | ~ r2_hidden(C_17,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_122,plain,(
    ! [A_13,B_33] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(A_13),B_33),A_13)
      | r1_tarski(k1_zfmisc_1(A_13),B_33) ) ),
    inference(resolution,[status(thm)],[c_117,c_14])).

tff(c_30,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_70,plain,(
    ! [A_26,B_27] :
      ( k2_xboole_0(A_26,B_27) = B_27
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_74,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_30,c_70])).

tff(c_12,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_79,plain,(
    ! [A_28,B_29] : k3_tarski(k2_tarski(A_28,B_29)) = k2_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_94,plain,(
    ! [B_30,A_31] : k3_tarski(k2_tarski(B_30,A_31)) = k2_xboole_0(A_31,B_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_79])).

tff(c_26,plain,(
    ! [A_18,B_19] : k3_tarski(k2_tarski(A_18,B_19)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_100,plain,(
    ! [B_30,A_31] : k2_xboole_0(B_30,A_31) = k2_xboole_0(A_31,B_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_26])).

tff(c_157,plain,(
    ! [A_36,C_37,B_38] :
      ( r1_tarski(A_36,k2_xboole_0(C_37,B_38))
      | ~ r1_tarski(A_36,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_206,plain,(
    ! [A_46,B_47,A_48] :
      ( r1_tarski(A_46,k2_xboole_0(B_47,A_48))
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_157])).

tff(c_221,plain,(
    ! [A_46] :
      ( r1_tarski(A_46,'#skF_5')
      | ~ r1_tarski(A_46,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_206])).

tff(c_16,plain,(
    ! [C_17,A_13] :
      ( r2_hidden(C_17,k1_zfmisc_1(A_13))
      | ~ r1_tarski(C_17,A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_171,plain,(
    ! [A_39,B_40] :
      ( ~ r2_hidden('#skF_1'(A_39,B_40),B_40)
      | r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_264,plain,(
    ! [A_56,A_57] :
      ( r1_tarski(A_56,k1_zfmisc_1(A_57))
      | ~ r1_tarski('#skF_1'(A_56,k1_zfmisc_1(A_57)),A_57) ) ),
    inference(resolution,[status(thm)],[c_16,c_171])).

tff(c_312,plain,(
    ! [A_63] :
      ( r1_tarski(A_63,k1_zfmisc_1('#skF_5'))
      | ~ r1_tarski('#skF_1'(A_63,k1_zfmisc_1('#skF_5')),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_221,c_264])).

tff(c_316,plain,(
    r1_tarski(k1_zfmisc_1('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_122,c_312])).

tff(c_320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_28,c_316])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:57:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.28  
% 1.96/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.28  %$ r2_hidden > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 1.96/1.28  
% 1.96/1.28  %Foreground sorts:
% 1.96/1.28  
% 1.96/1.28  
% 1.96/1.28  %Background operators:
% 1.96/1.28  
% 1.96/1.28  
% 1.96/1.28  %Foreground operators:
% 1.96/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.28  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.96/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.96/1.28  tff('#skF_5', type, '#skF_5': $i).
% 1.96/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.96/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.96/1.28  tff('#skF_4', type, '#skF_4': $i).
% 1.96/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.96/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.96/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.96/1.28  
% 1.96/1.29  tff(f_56, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 1.96/1.29  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.96/1.29  tff(f_49, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.96/1.29  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.96/1.29  tff(f_42, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.96/1.29  tff(f_51, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.96/1.29  tff(f_36, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.96/1.29  tff(c_28, plain, (~r1_tarski(k1_zfmisc_1('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.96/1.29  tff(c_117, plain, (![A_32, B_33]: (r2_hidden('#skF_1'(A_32, B_33), A_32) | r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.96/1.29  tff(c_14, plain, (![C_17, A_13]: (r1_tarski(C_17, A_13) | ~r2_hidden(C_17, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.96/1.29  tff(c_122, plain, (![A_13, B_33]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_13), B_33), A_13) | r1_tarski(k1_zfmisc_1(A_13), B_33))), inference(resolution, [status(thm)], [c_117, c_14])).
% 1.96/1.29  tff(c_30, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.96/1.29  tff(c_70, plain, (![A_26, B_27]: (k2_xboole_0(A_26, B_27)=B_27 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.96/1.29  tff(c_74, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_30, c_70])).
% 1.96/1.29  tff(c_12, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.96/1.29  tff(c_79, plain, (![A_28, B_29]: (k3_tarski(k2_tarski(A_28, B_29))=k2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.96/1.29  tff(c_94, plain, (![B_30, A_31]: (k3_tarski(k2_tarski(B_30, A_31))=k2_xboole_0(A_31, B_30))), inference(superposition, [status(thm), theory('equality')], [c_12, c_79])).
% 1.96/1.29  tff(c_26, plain, (![A_18, B_19]: (k3_tarski(k2_tarski(A_18, B_19))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.96/1.29  tff(c_100, plain, (![B_30, A_31]: (k2_xboole_0(B_30, A_31)=k2_xboole_0(A_31, B_30))), inference(superposition, [status(thm), theory('equality')], [c_94, c_26])).
% 1.96/1.29  tff(c_157, plain, (![A_36, C_37, B_38]: (r1_tarski(A_36, k2_xboole_0(C_37, B_38)) | ~r1_tarski(A_36, B_38))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.96/1.29  tff(c_206, plain, (![A_46, B_47, A_48]: (r1_tarski(A_46, k2_xboole_0(B_47, A_48)) | ~r1_tarski(A_46, B_47))), inference(superposition, [status(thm), theory('equality')], [c_100, c_157])).
% 1.96/1.29  tff(c_221, plain, (![A_46]: (r1_tarski(A_46, '#skF_5') | ~r1_tarski(A_46, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_206])).
% 1.96/1.29  tff(c_16, plain, (![C_17, A_13]: (r2_hidden(C_17, k1_zfmisc_1(A_13)) | ~r1_tarski(C_17, A_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.96/1.29  tff(c_171, plain, (![A_39, B_40]: (~r2_hidden('#skF_1'(A_39, B_40), B_40) | r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.96/1.29  tff(c_264, plain, (![A_56, A_57]: (r1_tarski(A_56, k1_zfmisc_1(A_57)) | ~r1_tarski('#skF_1'(A_56, k1_zfmisc_1(A_57)), A_57))), inference(resolution, [status(thm)], [c_16, c_171])).
% 1.96/1.29  tff(c_312, plain, (![A_63]: (r1_tarski(A_63, k1_zfmisc_1('#skF_5')) | ~r1_tarski('#skF_1'(A_63, k1_zfmisc_1('#skF_5')), '#skF_4'))), inference(resolution, [status(thm)], [c_221, c_264])).
% 1.96/1.29  tff(c_316, plain, (r1_tarski(k1_zfmisc_1('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_122, c_312])).
% 1.96/1.29  tff(c_320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_28, c_316])).
% 1.96/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.29  
% 1.96/1.29  Inference rules
% 1.96/1.29  ----------------------
% 1.96/1.29  #Ref     : 0
% 1.96/1.29  #Sup     : 68
% 1.96/1.29  #Fact    : 0
% 1.96/1.29  #Define  : 0
% 1.96/1.29  #Split   : 1
% 1.96/1.29  #Chain   : 0
% 1.96/1.29  #Close   : 0
% 1.96/1.29  
% 1.96/1.29  Ordering : KBO
% 1.96/1.29  
% 1.96/1.29  Simplification rules
% 1.96/1.29  ----------------------
% 1.96/1.29  #Subsume      : 5
% 1.96/1.29  #Demod        : 7
% 1.96/1.29  #Tautology    : 33
% 1.96/1.29  #SimpNegUnit  : 1
% 1.96/1.29  #BackRed      : 0
% 1.96/1.29  
% 1.96/1.29  #Partial instantiations: 0
% 1.96/1.29  #Strategies tried      : 1
% 1.96/1.29  
% 1.96/1.29  Timing (in seconds)
% 1.96/1.29  ----------------------
% 1.96/1.29  Preprocessing        : 0.29
% 1.96/1.30  Parsing              : 0.16
% 1.96/1.30  CNF conversion       : 0.02
% 1.96/1.30  Main loop            : 0.22
% 1.96/1.30  Inferencing          : 0.08
% 1.96/1.30  Reduction            : 0.06
% 1.96/1.30  Demodulation         : 0.05
% 1.96/1.30  BG Simplification    : 0.01
% 1.96/1.30  Subsumption          : 0.05
% 1.96/1.30  Abstraction          : 0.01
% 1.96/1.30  MUC search           : 0.00
% 1.96/1.30  Cooper               : 0.00
% 1.96/1.30  Total                : 0.54
% 1.96/1.30  Index Insertion      : 0.00
% 1.96/1.30  Index Deletion       : 0.00
% 1.96/1.30  Index Matching       : 0.00
% 1.96/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
