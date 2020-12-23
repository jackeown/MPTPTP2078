%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:13 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.53s
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

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => ( A = k1_xboole_0
          | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(B,C) )
     => ( A = k1_xboole_0
        | r1_tarski(B,k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(c_18,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_1'(A_10,B_11),A_10)
      | r1_tarski(B_11,k1_setfam_1(A_10))
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(k1_tarski(A_6),B_7) = k1_xboole_0
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_77,plain,(
    ! [A_25,C_26,B_27] :
      ( r1_tarski(A_25,C_26)
      | ~ r1_tarski(B_27,C_26)
      | ~ r1_tarski(A_25,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_87,plain,(
    ! [A_28] :
      ( r1_tarski(A_28,'#skF_3')
      | ~ r1_tarski(A_28,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_77])).

tff(c_107,plain,(
    ! [A_32] :
      ( r1_tarski(A_32,'#skF_3')
      | k4_xboole_0(A_32,'#skF_2') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_87])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_133,plain,(
    ! [A_34] :
      ( k4_xboole_0(A_34,'#skF_3') = k1_xboole_0
      | k4_xboole_0(A_34,'#skF_2') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_107,c_4])).

tff(c_155,plain,(
    ! [A_37] :
      ( k4_xboole_0(k1_tarski(A_37),'#skF_3') = k1_xboole_0
      | ~ r2_hidden(A_37,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_133])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | k4_xboole_0(k1_tarski(A_6),B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_177,plain,(
    ! [A_38] :
      ( r2_hidden(A_38,'#skF_3')
      | ~ r2_hidden(A_38,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_8])).

tff(c_181,plain,(
    ! [B_11] :
      ( r2_hidden('#skF_1'('#skF_2',B_11),'#skF_3')
      | r1_tarski(B_11,k1_setfam_1('#skF_2'))
      | k1_xboole_0 = '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_16,c_177])).

tff(c_184,plain,(
    ! [B_11] :
      ( r2_hidden('#skF_1'('#skF_2',B_11),'#skF_3')
      | r1_tarski(B_11,k1_setfam_1('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_181])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_setfam_1(B_9),A_8)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_225,plain,(
    ! [B_44,A_45] :
      ( ~ r1_tarski(B_44,'#skF_1'(A_45,B_44))
      | r1_tarski(B_44,k1_setfam_1(A_45))
      | k1_xboole_0 = A_45 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_501,plain,(
    ! [B_82,A_83] :
      ( r1_tarski(k1_setfam_1(B_82),k1_setfam_1(A_83))
      | k1_xboole_0 = A_83
      | ~ r2_hidden('#skF_1'(A_83,k1_setfam_1(B_82)),B_82) ) ),
    inference(resolution,[status(thm)],[c_12,c_225])).

tff(c_505,plain,
    ( k1_xboole_0 = '#skF_2'
    | r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_184,c_501])).

tff(c_513,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_20,c_18,c_505])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:52:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.35  
% 2.41/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.35  %$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.53/1.35  
% 2.53/1.35  %Foreground sorts:
% 2.53/1.35  
% 2.53/1.35  
% 2.53/1.35  %Background operators:
% 2.53/1.35  
% 2.53/1.35  
% 2.53/1.35  %Foreground operators:
% 2.53/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.53/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.53/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.53/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.53/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.53/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.53/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.53/1.35  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.53/1.35  
% 2.53/1.36  tff(f_59, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.53/1.36  tff(f_52, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(B, C))) => ((A = k1_xboole_0) | r1_tarski(B, k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_setfam_1)).
% 2.53/1.36  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 2.53/1.36  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.53/1.36  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.53/1.36  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.53/1.36  tff(c_18, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.53/1.36  tff(c_20, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.53/1.36  tff(c_16, plain, (![A_10, B_11]: (r2_hidden('#skF_1'(A_10, B_11), A_10) | r1_tarski(B_11, k1_setfam_1(A_10)) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.53/1.36  tff(c_10, plain, (![A_6, B_7]: (k4_xboole_0(k1_tarski(A_6), B_7)=k1_xboole_0 | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.53/1.36  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.53/1.36  tff(c_22, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.53/1.36  tff(c_77, plain, (![A_25, C_26, B_27]: (r1_tarski(A_25, C_26) | ~r1_tarski(B_27, C_26) | ~r1_tarski(A_25, B_27))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.53/1.36  tff(c_87, plain, (![A_28]: (r1_tarski(A_28, '#skF_3') | ~r1_tarski(A_28, '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_77])).
% 2.53/1.36  tff(c_107, plain, (![A_32]: (r1_tarski(A_32, '#skF_3') | k4_xboole_0(A_32, '#skF_2')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_87])).
% 2.53/1.36  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.53/1.36  tff(c_133, plain, (![A_34]: (k4_xboole_0(A_34, '#skF_3')=k1_xboole_0 | k4_xboole_0(A_34, '#skF_2')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_107, c_4])).
% 2.53/1.36  tff(c_155, plain, (![A_37]: (k4_xboole_0(k1_tarski(A_37), '#skF_3')=k1_xboole_0 | ~r2_hidden(A_37, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_10, c_133])).
% 2.53/1.36  tff(c_8, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | k4_xboole_0(k1_tarski(A_6), B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.53/1.36  tff(c_177, plain, (![A_38]: (r2_hidden(A_38, '#skF_3') | ~r2_hidden(A_38, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_155, c_8])).
% 2.53/1.36  tff(c_181, plain, (![B_11]: (r2_hidden('#skF_1'('#skF_2', B_11), '#skF_3') | r1_tarski(B_11, k1_setfam_1('#skF_2')) | k1_xboole_0='#skF_2')), inference(resolution, [status(thm)], [c_16, c_177])).
% 2.53/1.36  tff(c_184, plain, (![B_11]: (r2_hidden('#skF_1'('#skF_2', B_11), '#skF_3') | r1_tarski(B_11, k1_setfam_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_20, c_181])).
% 2.53/1.36  tff(c_12, plain, (![B_9, A_8]: (r1_tarski(k1_setfam_1(B_9), A_8) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.53/1.36  tff(c_225, plain, (![B_44, A_45]: (~r1_tarski(B_44, '#skF_1'(A_45, B_44)) | r1_tarski(B_44, k1_setfam_1(A_45)) | k1_xboole_0=A_45)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.53/1.36  tff(c_501, plain, (![B_82, A_83]: (r1_tarski(k1_setfam_1(B_82), k1_setfam_1(A_83)) | k1_xboole_0=A_83 | ~r2_hidden('#skF_1'(A_83, k1_setfam_1(B_82)), B_82))), inference(resolution, [status(thm)], [c_12, c_225])).
% 2.53/1.36  tff(c_505, plain, (k1_xboole_0='#skF_2' | r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(resolution, [status(thm)], [c_184, c_501])).
% 2.53/1.36  tff(c_513, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_20, c_18, c_505])).
% 2.53/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.36  
% 2.53/1.36  Inference rules
% 2.53/1.36  ----------------------
% 2.53/1.36  #Ref     : 0
% 2.53/1.36  #Sup     : 119
% 2.53/1.36  #Fact    : 0
% 2.53/1.36  #Define  : 0
% 2.53/1.36  #Split   : 1
% 2.53/1.36  #Chain   : 0
% 2.53/1.36  #Close   : 0
% 2.53/1.36  
% 2.53/1.36  Ordering : KBO
% 2.53/1.36  
% 2.53/1.36  Simplification rules
% 2.53/1.36  ----------------------
% 2.53/1.36  #Subsume      : 19
% 2.53/1.36  #Demod        : 8
% 2.53/1.36  #Tautology    : 28
% 2.53/1.36  #SimpNegUnit  : 2
% 2.53/1.36  #BackRed      : 0
% 2.53/1.36  
% 2.53/1.36  #Partial instantiations: 0
% 2.53/1.36  #Strategies tried      : 1
% 2.53/1.36  
% 2.53/1.36  Timing (in seconds)
% 2.53/1.37  ----------------------
% 2.53/1.37  Preprocessing        : 0.27
% 2.53/1.37  Parsing              : 0.15
% 2.53/1.37  CNF conversion       : 0.02
% 2.53/1.37  Main loop            : 0.29
% 2.53/1.37  Inferencing          : 0.11
% 2.53/1.37  Reduction            : 0.07
% 2.53/1.37  Demodulation         : 0.04
% 2.53/1.37  BG Simplification    : 0.01
% 2.53/1.37  Subsumption          : 0.08
% 2.53/1.37  Abstraction          : 0.01
% 2.53/1.37  MUC search           : 0.00
% 2.53/1.37  Cooper               : 0.00
% 2.53/1.37  Total                : 0.59
% 2.53/1.37  Index Insertion      : 0.00
% 2.53/1.37  Index Deletion       : 0.00
% 2.53/1.37  Index Matching       : 0.00
% 2.53/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
