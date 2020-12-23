%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:13 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   33 (  41 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   49 (  69 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_55,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => ( A = k1_xboole_0
          | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(B,C) )
     => ( A = k1_xboole_0
        | r1_tarski(B,k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(c_14,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_93,plain,(
    ! [A_32,B_33] :
      ( r2_hidden('#skF_1'(A_32,B_33),A_32)
      | r1_tarski(B_33,k1_setfam_1(A_32))
      | k1_xboole_0 = A_32 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(k1_tarski(A_4),B_5)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_30,plain,(
    ! [A_17,C_18,B_19] :
      ( r1_tarski(A_17,C_18)
      | ~ r1_tarski(B_19,C_18)
      | ~ r1_tarski(A_17,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    ! [A_20] :
      ( r1_tarski(A_20,'#skF_3')
      | ~ r1_tarski(A_20,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_30])).

tff(c_55,plain,(
    ! [A_22] :
      ( r1_tarski(k1_tarski(A_22),'#skF_3')
      | ~ r2_hidden(A_22,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6,c_40])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | ~ r1_tarski(k1_tarski(A_4),B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_62,plain,(
    ! [A_22] :
      ( r2_hidden(A_22,'#skF_3')
      | ~ r2_hidden(A_22,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_55,c_4])).

tff(c_97,plain,(
    ! [B_33] :
      ( r2_hidden('#skF_1'('#skF_2',B_33),'#skF_3')
      | r1_tarski(B_33,k1_setfam_1('#skF_2'))
      | k1_xboole_0 = '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_93,c_62])).

tff(c_100,plain,(
    ! [B_33] :
      ( r2_hidden('#skF_1'('#skF_2',B_33),'#skF_3')
      | r1_tarski(B_33,k1_setfam_1('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_97])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_setfam_1(B_7),A_6)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_113,plain,(
    ! [B_37,A_38] :
      ( ~ r1_tarski(B_37,'#skF_1'(A_38,B_37))
      | r1_tarski(B_37,k1_setfam_1(A_38))
      | k1_xboole_0 = A_38 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_157,plain,(
    ! [B_55,A_56] :
      ( r1_tarski(k1_setfam_1(B_55),k1_setfam_1(A_56))
      | k1_xboole_0 = A_56
      | ~ r2_hidden('#skF_1'(A_56,k1_setfam_1(B_55)),B_55) ) ),
    inference(resolution,[status(thm)],[c_8,c_113])).

tff(c_161,plain,
    ( k1_xboole_0 = '#skF_2'
    | r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_100,c_157])).

tff(c_169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_16,c_14,c_161])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:44:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.20  
% 2.01/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.20  %$ r2_hidden > r1_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.01/1.20  
% 2.01/1.20  %Foreground sorts:
% 2.01/1.20  
% 2.01/1.20  
% 2.01/1.20  %Background operators:
% 2.01/1.20  
% 2.01/1.20  
% 2.01/1.20  %Foreground operators:
% 2.01/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.01/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.01/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.01/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.01/1.20  tff('#skF_2', type, '#skF_2': $i).
% 2.01/1.20  tff('#skF_3', type, '#skF_3': $i).
% 2.01/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.01/1.20  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.01/1.20  
% 2.01/1.21  tff(f_55, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.01/1.21  tff(f_48, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(B, C))) => ((A = k1_xboole_0) | r1_tarski(B, k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_setfam_1)).
% 2.01/1.21  tff(f_35, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.01/1.21  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.01/1.21  tff(f_39, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.01/1.21  tff(c_14, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.01/1.21  tff(c_16, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.01/1.21  tff(c_93, plain, (![A_32, B_33]: (r2_hidden('#skF_1'(A_32, B_33), A_32) | r1_tarski(B_33, k1_setfam_1(A_32)) | k1_xboole_0=A_32)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.01/1.21  tff(c_6, plain, (![A_4, B_5]: (r1_tarski(k1_tarski(A_4), B_5) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.01/1.21  tff(c_18, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.01/1.21  tff(c_30, plain, (![A_17, C_18, B_19]: (r1_tarski(A_17, C_18) | ~r1_tarski(B_19, C_18) | ~r1_tarski(A_17, B_19))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.01/1.21  tff(c_40, plain, (![A_20]: (r1_tarski(A_20, '#skF_3') | ~r1_tarski(A_20, '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_30])).
% 2.01/1.21  tff(c_55, plain, (![A_22]: (r1_tarski(k1_tarski(A_22), '#skF_3') | ~r2_hidden(A_22, '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_40])).
% 2.01/1.21  tff(c_4, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | ~r1_tarski(k1_tarski(A_4), B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.01/1.21  tff(c_62, plain, (![A_22]: (r2_hidden(A_22, '#skF_3') | ~r2_hidden(A_22, '#skF_2'))), inference(resolution, [status(thm)], [c_55, c_4])).
% 2.01/1.21  tff(c_97, plain, (![B_33]: (r2_hidden('#skF_1'('#skF_2', B_33), '#skF_3') | r1_tarski(B_33, k1_setfam_1('#skF_2')) | k1_xboole_0='#skF_2')), inference(resolution, [status(thm)], [c_93, c_62])).
% 2.01/1.21  tff(c_100, plain, (![B_33]: (r2_hidden('#skF_1'('#skF_2', B_33), '#skF_3') | r1_tarski(B_33, k1_setfam_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_16, c_97])).
% 2.01/1.21  tff(c_8, plain, (![B_7, A_6]: (r1_tarski(k1_setfam_1(B_7), A_6) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.01/1.21  tff(c_113, plain, (![B_37, A_38]: (~r1_tarski(B_37, '#skF_1'(A_38, B_37)) | r1_tarski(B_37, k1_setfam_1(A_38)) | k1_xboole_0=A_38)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.01/1.21  tff(c_157, plain, (![B_55, A_56]: (r1_tarski(k1_setfam_1(B_55), k1_setfam_1(A_56)) | k1_xboole_0=A_56 | ~r2_hidden('#skF_1'(A_56, k1_setfam_1(B_55)), B_55))), inference(resolution, [status(thm)], [c_8, c_113])).
% 2.01/1.21  tff(c_161, plain, (k1_xboole_0='#skF_2' | r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(resolution, [status(thm)], [c_100, c_157])).
% 2.01/1.21  tff(c_169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_16, c_14, c_161])).
% 2.01/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.21  
% 2.01/1.21  Inference rules
% 2.01/1.21  ----------------------
% 2.01/1.21  #Ref     : 0
% 2.01/1.21  #Sup     : 32
% 2.01/1.21  #Fact    : 0
% 2.01/1.21  #Define  : 0
% 2.01/1.21  #Split   : 0
% 2.01/1.21  #Chain   : 0
% 2.01/1.21  #Close   : 0
% 2.01/1.21  
% 2.01/1.21  Ordering : KBO
% 2.01/1.21  
% 2.01/1.21  Simplification rules
% 2.01/1.21  ----------------------
% 2.01/1.21  #Subsume      : 0
% 2.01/1.21  #Demod        : 0
% 2.01/1.21  #Tautology    : 1
% 2.01/1.21  #SimpNegUnit  : 2
% 2.01/1.21  #BackRed      : 0
% 2.01/1.21  
% 2.01/1.21  #Partial instantiations: 0
% 2.01/1.21  #Strategies tried      : 1
% 2.01/1.21  
% 2.01/1.21  Timing (in seconds)
% 2.01/1.21  ----------------------
% 2.01/1.21  Preprocessing        : 0.27
% 2.01/1.21  Parsing              : 0.15
% 2.01/1.21  CNF conversion       : 0.02
% 2.01/1.21  Main loop            : 0.18
% 2.01/1.21  Inferencing          : 0.07
% 2.01/1.21  Reduction            : 0.04
% 2.01/1.21  Demodulation         : 0.02
% 2.01/1.21  BG Simplification    : 0.01
% 2.01/1.21  Subsumption          : 0.05
% 2.01/1.21  Abstraction          : 0.01
% 2.01/1.21  MUC search           : 0.00
% 2.01/1.21  Cooper               : 0.00
% 2.01/1.21  Total                : 0.48
% 2.01/1.21  Index Insertion      : 0.00
% 2.01/1.21  Index Deletion       : 0.00
% 2.01/1.21  Index Matching       : 0.00
% 2.01/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
