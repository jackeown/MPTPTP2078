%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:13 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   39 (  48 expanded)
%              Number of leaves         :   18 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :   59 (  81 expanded)
%              Number of equality atoms :   18 (  26 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => ( A = k1_xboole_0
          | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(B,C) )
     => ( A = k1_xboole_0
        | r1_tarski(B,k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(c_22,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_1'(A_12,B_13),A_12)
      | r1_tarski(B_13,k1_setfam_1(A_12))
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(k1_tarski(A_8),B_9) = k1_xboole_0
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | k4_xboole_0(A_6,B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_81,plain,(
    ! [A_27,C_28,B_29] :
      ( r1_tarski(A_27,C_28)
      | ~ r1_tarski(B_29,C_28)
      | ~ r1_tarski(A_27,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_91,plain,(
    ! [A_30] :
      ( r1_tarski(A_30,'#skF_3')
      | ~ r1_tarski(A_30,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_81])).

tff(c_111,plain,(
    ! [A_34] :
      ( r1_tarski(A_34,'#skF_3')
      | k4_xboole_0(A_34,'#skF_2') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_91])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = k1_xboole_0
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_137,plain,(
    ! [A_36] :
      ( k4_xboole_0(A_36,'#skF_3') = k1_xboole_0
      | k4_xboole_0(A_36,'#skF_2') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_111,c_10])).

tff(c_159,plain,(
    ! [A_39] :
      ( k4_xboole_0(k1_tarski(A_39),'#skF_3') = k1_xboole_0
      | ~ r2_hidden(A_39,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_137])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | k4_xboole_0(k1_tarski(A_8),B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_181,plain,(
    ! [A_40] :
      ( r2_hidden(A_40,'#skF_3')
      | ~ r2_hidden(A_40,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_12])).

tff(c_185,plain,(
    ! [B_13] :
      ( r2_hidden('#skF_1'('#skF_2',B_13),'#skF_3')
      | r1_tarski(B_13,k1_setfam_1('#skF_2'))
      | k1_xboole_0 = '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_20,c_181])).

tff(c_188,plain,(
    ! [B_13] :
      ( r2_hidden('#skF_1'('#skF_2',B_13),'#skF_3')
      | r1_tarski(B_13,k1_setfam_1('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_185])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k1_setfam_1(B_11),A_10)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_229,plain,(
    ! [B_46,A_47] :
      ( ~ r1_tarski(B_46,'#skF_1'(A_47,B_46))
      | r1_tarski(B_46,k1_setfam_1(A_47))
      | k1_xboole_0 = A_47 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_505,plain,(
    ! [B_84,A_85] :
      ( r1_tarski(k1_setfam_1(B_84),k1_setfam_1(A_85))
      | k1_xboole_0 = A_85
      | ~ r2_hidden('#skF_1'(A_85,k1_setfam_1(B_84)),B_84) ) ),
    inference(resolution,[status(thm)],[c_16,c_229])).

tff(c_509,plain,
    ( k1_xboole_0 = '#skF_2'
    | r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_188,c_505])).

tff(c_517,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_24,c_22,c_509])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:55:02 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.40  
% 2.36/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.40  %$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.36/1.40  
% 2.36/1.40  %Foreground sorts:
% 2.36/1.40  
% 2.36/1.40  
% 2.36/1.40  %Background operators:
% 2.36/1.40  
% 2.36/1.40  
% 2.36/1.40  %Foreground operators:
% 2.36/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.36/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.36/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.36/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.36/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.36/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.36/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.36/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.36/1.40  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.36/1.40  
% 2.36/1.41  tff(f_63, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.36/1.41  tff(f_56, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(B, C))) => ((A = k1_xboole_0) | r1_tarski(B, k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_setfam_1)).
% 2.36/1.41  tff(f_43, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 2.36/1.41  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 2.36/1.41  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.36/1.41  tff(f_47, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.36/1.41  tff(c_22, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.36/1.41  tff(c_24, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.36/1.41  tff(c_20, plain, (![A_12, B_13]: (r2_hidden('#skF_1'(A_12, B_13), A_12) | r1_tarski(B_13, k1_setfam_1(A_12)) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.36/1.41  tff(c_14, plain, (![A_8, B_9]: (k4_xboole_0(k1_tarski(A_8), B_9)=k1_xboole_0 | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.36/1.41  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | k4_xboole_0(A_6, B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.36/1.41  tff(c_26, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.36/1.41  tff(c_81, plain, (![A_27, C_28, B_29]: (r1_tarski(A_27, C_28) | ~r1_tarski(B_29, C_28) | ~r1_tarski(A_27, B_29))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.36/1.41  tff(c_91, plain, (![A_30]: (r1_tarski(A_30, '#skF_3') | ~r1_tarski(A_30, '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_81])).
% 2.36/1.41  tff(c_111, plain, (![A_34]: (r1_tarski(A_34, '#skF_3') | k4_xboole_0(A_34, '#skF_2')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_91])).
% 2.36/1.41  tff(c_10, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=k1_xboole_0 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.36/1.41  tff(c_137, plain, (![A_36]: (k4_xboole_0(A_36, '#skF_3')=k1_xboole_0 | k4_xboole_0(A_36, '#skF_2')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_111, c_10])).
% 2.36/1.41  tff(c_159, plain, (![A_39]: (k4_xboole_0(k1_tarski(A_39), '#skF_3')=k1_xboole_0 | ~r2_hidden(A_39, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_137])).
% 2.36/1.41  tff(c_12, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | k4_xboole_0(k1_tarski(A_8), B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.36/1.41  tff(c_181, plain, (![A_40]: (r2_hidden(A_40, '#skF_3') | ~r2_hidden(A_40, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_159, c_12])).
% 2.36/1.41  tff(c_185, plain, (![B_13]: (r2_hidden('#skF_1'('#skF_2', B_13), '#skF_3') | r1_tarski(B_13, k1_setfam_1('#skF_2')) | k1_xboole_0='#skF_2')), inference(resolution, [status(thm)], [c_20, c_181])).
% 2.36/1.41  tff(c_188, plain, (![B_13]: (r2_hidden('#skF_1'('#skF_2', B_13), '#skF_3') | r1_tarski(B_13, k1_setfam_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_24, c_185])).
% 2.36/1.41  tff(c_16, plain, (![B_11, A_10]: (r1_tarski(k1_setfam_1(B_11), A_10) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.36/1.41  tff(c_229, plain, (![B_46, A_47]: (~r1_tarski(B_46, '#skF_1'(A_47, B_46)) | r1_tarski(B_46, k1_setfam_1(A_47)) | k1_xboole_0=A_47)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.36/1.41  tff(c_505, plain, (![B_84, A_85]: (r1_tarski(k1_setfam_1(B_84), k1_setfam_1(A_85)) | k1_xboole_0=A_85 | ~r2_hidden('#skF_1'(A_85, k1_setfam_1(B_84)), B_84))), inference(resolution, [status(thm)], [c_16, c_229])).
% 2.36/1.41  tff(c_509, plain, (k1_xboole_0='#skF_2' | r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(resolution, [status(thm)], [c_188, c_505])).
% 2.36/1.41  tff(c_517, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_24, c_22, c_509])).
% 2.36/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.41  
% 2.36/1.41  Inference rules
% 2.36/1.41  ----------------------
% 2.36/1.41  #Ref     : 0
% 2.36/1.41  #Sup     : 119
% 2.36/1.41  #Fact    : 0
% 2.36/1.41  #Define  : 0
% 2.36/1.41  #Split   : 1
% 2.36/1.41  #Chain   : 0
% 2.36/1.41  #Close   : 0
% 2.36/1.41  
% 2.36/1.41  Ordering : KBO
% 2.36/1.41  
% 2.36/1.41  Simplification rules
% 2.36/1.41  ----------------------
% 2.36/1.41  #Subsume      : 21
% 2.36/1.41  #Demod        : 8
% 2.36/1.41  #Tautology    : 28
% 2.36/1.41  #SimpNegUnit  : 2
% 2.36/1.41  #BackRed      : 0
% 2.36/1.41  
% 2.36/1.41  #Partial instantiations: 0
% 2.36/1.41  #Strategies tried      : 1
% 2.36/1.41  
% 2.36/1.41  Timing (in seconds)
% 2.36/1.41  ----------------------
% 2.36/1.41  Preprocessing        : 0.29
% 2.36/1.41  Parsing              : 0.16
% 2.36/1.41  CNF conversion       : 0.02
% 2.36/1.41  Main loop            : 0.29
% 2.36/1.41  Inferencing          : 0.11
% 2.36/1.41  Reduction            : 0.06
% 2.36/1.41  Demodulation         : 0.04
% 2.36/1.41  BG Simplification    : 0.01
% 2.36/1.41  Subsumption          : 0.08
% 2.36/1.42  Abstraction          : 0.01
% 2.36/1.42  MUC search           : 0.00
% 2.36/1.42  Cooper               : 0.00
% 2.36/1.42  Total                : 0.61
% 2.36/1.42  Index Insertion      : 0.00
% 2.36/1.42  Index Deletion       : 0.00
% 2.36/1.42  Index Matching       : 0.00
% 2.36/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
