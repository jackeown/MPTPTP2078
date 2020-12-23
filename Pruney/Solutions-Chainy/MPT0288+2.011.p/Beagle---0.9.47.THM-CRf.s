%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:32 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   38 (  42 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  53 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(c_36,plain,(
    ~ r1_tarski(k3_tarski('#skF_4'),k3_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_34,plain,(
    ! [A_14,B_15] :
      ( r2_hidden('#skF_3'(A_14,B_15),A_14)
      | r1_tarski(k3_tarski(A_14),B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,(
    ! [A_9] : k4_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_73,plain,(
    ! [B_24,A_25] :
      ( ~ r2_hidden(B_24,A_25)
      | k4_xboole_0(A_25,k1_tarski(B_24)) != A_25 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_78,plain,(
    ! [B_24] : ~ r2_hidden(B_24,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_73])).

tff(c_38,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_46,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = k1_xboole_0
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_50,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_46])).

tff(c_220,plain,(
    ! [D_43,A_44,B_45] :
      ( r2_hidden(D_43,k4_xboole_0(A_44,B_45))
      | r2_hidden(D_43,B_45)
      | ~ r2_hidden(D_43,A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_238,plain,(
    ! [D_43] :
      ( r2_hidden(D_43,k1_xboole_0)
      | r2_hidden(D_43,'#skF_5')
      | ~ r2_hidden(D_43,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_220])).

tff(c_246,plain,(
    ! [D_43] :
      ( r2_hidden(D_43,'#skF_5')
      | ~ r2_hidden(D_43,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_238])).

tff(c_26,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,k3_tarski(B_11))
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_155,plain,(
    ! [A_37,B_38] :
      ( ~ r1_tarski('#skF_3'(A_37,B_38),B_38)
      | r1_tarski(k3_tarski(A_37),B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_326,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(k3_tarski(A_63),k3_tarski(B_64))
      | ~ r2_hidden('#skF_3'(A_63,k3_tarski(B_64)),B_64) ) ),
    inference(resolution,[status(thm)],[c_26,c_155])).

tff(c_475,plain,(
    ! [A_72] :
      ( r1_tarski(k3_tarski(A_72),k3_tarski('#skF_5'))
      | ~ r2_hidden('#skF_3'(A_72,k3_tarski('#skF_5')),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_246,c_326])).

tff(c_479,plain,(
    r1_tarski(k3_tarski('#skF_4'),k3_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_34,c_475])).

tff(c_483,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_36,c_479])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:35:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.34  
% 2.26/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.34  %$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 2.26/1.34  
% 2.26/1.34  %Foreground sorts:
% 2.26/1.34  
% 2.26/1.34  
% 2.26/1.34  %Background operators:
% 2.26/1.34  
% 2.26/1.34  
% 2.26/1.34  %Foreground operators:
% 2.26/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.26/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.26/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.26/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.26/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.26/1.34  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.26/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.26/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.26/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.26/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.26/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.26/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.34  
% 2.26/1.35  tff(f_62, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 2.26/1.35  tff(f_57, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 2.26/1.35  tff(f_41, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.26/1.35  tff(f_50, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.26/1.35  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.26/1.35  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.26/1.35  tff(f_45, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.26/1.35  tff(c_36, plain, (~r1_tarski(k3_tarski('#skF_4'), k3_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.26/1.35  tff(c_34, plain, (![A_14, B_15]: (r2_hidden('#skF_3'(A_14, B_15), A_14) | r1_tarski(k3_tarski(A_14), B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.26/1.35  tff(c_24, plain, (![A_9]: (k4_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.26/1.35  tff(c_73, plain, (![B_24, A_25]: (~r2_hidden(B_24, A_25) | k4_xboole_0(A_25, k1_tarski(B_24))!=A_25)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.26/1.35  tff(c_78, plain, (![B_24]: (~r2_hidden(B_24, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_73])).
% 2.26/1.35  tff(c_38, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.26/1.35  tff(c_46, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=k1_xboole_0 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.26/1.35  tff(c_50, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_46])).
% 2.26/1.35  tff(c_220, plain, (![D_43, A_44, B_45]: (r2_hidden(D_43, k4_xboole_0(A_44, B_45)) | r2_hidden(D_43, B_45) | ~r2_hidden(D_43, A_44))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.26/1.35  tff(c_238, plain, (![D_43]: (r2_hidden(D_43, k1_xboole_0) | r2_hidden(D_43, '#skF_5') | ~r2_hidden(D_43, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_220])).
% 2.26/1.35  tff(c_246, plain, (![D_43]: (r2_hidden(D_43, '#skF_5') | ~r2_hidden(D_43, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_78, c_238])).
% 2.26/1.35  tff(c_26, plain, (![A_10, B_11]: (r1_tarski(A_10, k3_tarski(B_11)) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.26/1.35  tff(c_155, plain, (![A_37, B_38]: (~r1_tarski('#skF_3'(A_37, B_38), B_38) | r1_tarski(k3_tarski(A_37), B_38))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.26/1.35  tff(c_326, plain, (![A_63, B_64]: (r1_tarski(k3_tarski(A_63), k3_tarski(B_64)) | ~r2_hidden('#skF_3'(A_63, k3_tarski(B_64)), B_64))), inference(resolution, [status(thm)], [c_26, c_155])).
% 2.26/1.35  tff(c_475, plain, (![A_72]: (r1_tarski(k3_tarski(A_72), k3_tarski('#skF_5')) | ~r2_hidden('#skF_3'(A_72, k3_tarski('#skF_5')), '#skF_4'))), inference(resolution, [status(thm)], [c_246, c_326])).
% 2.26/1.35  tff(c_479, plain, (r1_tarski(k3_tarski('#skF_4'), k3_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_34, c_475])).
% 2.26/1.35  tff(c_483, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_36, c_479])).
% 2.26/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.35  
% 2.26/1.35  Inference rules
% 2.26/1.35  ----------------------
% 2.26/1.35  #Ref     : 0
% 2.26/1.35  #Sup     : 101
% 2.26/1.35  #Fact    : 0
% 2.26/1.35  #Define  : 0
% 2.26/1.35  #Split   : 1
% 2.26/1.35  #Chain   : 0
% 2.26/1.35  #Close   : 0
% 2.26/1.35  
% 2.26/1.35  Ordering : KBO
% 2.26/1.35  
% 2.26/1.35  Simplification rules
% 2.26/1.35  ----------------------
% 2.26/1.35  #Subsume      : 18
% 2.26/1.35  #Demod        : 18
% 2.26/1.35  #Tautology    : 37
% 2.26/1.35  #SimpNegUnit  : 11
% 2.26/1.35  #BackRed      : 2
% 2.26/1.35  
% 2.26/1.35  #Partial instantiations: 0
% 2.26/1.35  #Strategies tried      : 1
% 2.26/1.35  
% 2.26/1.35  Timing (in seconds)
% 2.26/1.35  ----------------------
% 2.26/1.35  Preprocessing        : 0.28
% 2.26/1.35  Parsing              : 0.15
% 2.26/1.35  CNF conversion       : 0.02
% 2.26/1.35  Main loop            : 0.26
% 2.26/1.36  Inferencing          : 0.10
% 2.26/1.36  Reduction            : 0.07
% 2.26/1.36  Demodulation         : 0.04
% 2.26/1.36  BG Simplification    : 0.01
% 2.26/1.36  Subsumption          : 0.05
% 2.26/1.36  Abstraction          : 0.01
% 2.46/1.36  MUC search           : 0.00
% 2.46/1.36  Cooper               : 0.00
% 2.46/1.36  Total                : 0.56
% 2.46/1.36  Index Insertion      : 0.00
% 2.46/1.36  Index Deletion       : 0.00
% 2.46/1.36  Index Matching       : 0.00
% 2.46/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
