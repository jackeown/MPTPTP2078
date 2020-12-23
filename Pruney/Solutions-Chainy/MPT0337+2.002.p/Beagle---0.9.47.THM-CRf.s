%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:15 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   36 (  59 expanded)
%              Number of leaves         :   13 (  27 expanded)
%              Depth                    :   16
%              Number of atoms          :   61 ( 148 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > #nlpp > k3_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( ! [C,D] :
            ( ( r2_hidden(C,A)
              & r2_hidden(D,B) )
           => r1_xboole_0(C,D) )
       => r1_xboole_0(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_xboole_0(C,B) )
     => r1_xboole_0(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_zfmisc_1)).

tff(c_12,plain,(
    ~ r1_xboole_0(k3_tarski('#skF_3'),k3_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),A_6)
      | r1_xboole_0(k3_tarski(A_6),B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_28,plain,(
    ! [A_24,B_25] :
      ( r2_hidden('#skF_2'(A_24,B_25),A_24)
      | r1_xboole_0(k3_tarski(A_24),B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    ! [C_11,D_12] :
      ( r1_xboole_0(C_11,D_12)
      | ~ r2_hidden(D_12,'#skF_4')
      | ~ r2_hidden(C_11,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_49,plain,(
    ! [C_30,B_31] :
      ( r1_xboole_0(C_30,'#skF_2'('#skF_4',B_31))
      | ~ r2_hidden(C_30,'#skF_3')
      | r1_xboole_0(k3_tarski('#skF_4'),B_31) ) ),
    inference(resolution,[status(thm)],[c_28,c_14])).

tff(c_2,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_99,plain,(
    ! [C_41,B_42,C_43] :
      ( ~ r2_hidden(C_41,B_42)
      | ~ r2_hidden(C_41,k3_tarski('#skF_4'))
      | r1_xboole_0(C_43,'#skF_2'('#skF_4',B_42))
      | ~ r2_hidden(C_43,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_49,c_2])).

tff(c_212,plain,(
    ! [A_67,B_68,C_69] :
      ( ~ r2_hidden('#skF_1'(A_67,B_68),k3_tarski('#skF_4'))
      | r1_xboole_0(C_69,'#skF_2'('#skF_4',A_67))
      | ~ r2_hidden(C_69,'#skF_3')
      | r1_xboole_0(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_6,c_99])).

tff(c_221,plain,(
    ! [C_70,A_71] :
      ( r1_xboole_0(C_70,'#skF_2'('#skF_4',A_71))
      | ~ r2_hidden(C_70,'#skF_3')
      | r1_xboole_0(A_71,k3_tarski('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_4,c_212])).

tff(c_240,plain,(
    ! [C_72] :
      ( r1_xboole_0(C_72,'#skF_2'('#skF_4',k3_tarski('#skF_3')))
      | ~ r2_hidden(C_72,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_221,c_12])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( ~ r1_xboole_0('#skF_2'(A_6,B_7),B_7)
      | r1_xboole_0(k3_tarski(A_6),B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_314,plain,(
    ! [A_84] :
      ( r1_xboole_0(k3_tarski(A_84),'#skF_2'('#skF_4',k3_tarski('#skF_3')))
      | ~ r2_hidden('#skF_2'(A_84,'#skF_2'('#skF_4',k3_tarski('#skF_3'))),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_240,c_8])).

tff(c_319,plain,(
    r1_xboole_0(k3_tarski('#skF_3'),'#skF_2'('#skF_4',k3_tarski('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_10,c_314])).

tff(c_323,plain,(
    ! [C_85] :
      ( ~ r2_hidden(C_85,'#skF_2'('#skF_4',k3_tarski('#skF_3')))
      | ~ r2_hidden(C_85,k3_tarski('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_319,c_2])).

tff(c_522,plain,(
    ! [B_126] :
      ( ~ r2_hidden('#skF_1'('#skF_2'('#skF_4',k3_tarski('#skF_3')),B_126),k3_tarski('#skF_3'))
      | r1_xboole_0('#skF_2'('#skF_4',k3_tarski('#skF_3')),B_126) ) ),
    inference(resolution,[status(thm)],[c_6,c_323])).

tff(c_527,plain,(
    r1_xboole_0('#skF_2'('#skF_4',k3_tarski('#skF_3')),k3_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_522])).

tff(c_533,plain,(
    r1_xboole_0(k3_tarski('#skF_4'),k3_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_527,c_8])).

tff(c_537,plain,(
    ! [C_127] :
      ( ~ r2_hidden(C_127,k3_tarski('#skF_3'))
      | ~ r2_hidden(C_127,k3_tarski('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_533,c_2])).

tff(c_566,plain,(
    ! [B_132] :
      ( ~ r2_hidden('#skF_1'(k3_tarski('#skF_3'),B_132),k3_tarski('#skF_4'))
      | r1_xboole_0(k3_tarski('#skF_3'),B_132) ) ),
    inference(resolution,[status(thm)],[c_6,c_537])).

tff(c_570,plain,(
    r1_xboole_0(k3_tarski('#skF_3'),k3_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_566])).

tff(c_574,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_12,c_570])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:04:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.39  
% 2.91/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.39  %$ r2_hidden > r1_xboole_0 > #nlpp > k3_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.91/1.39  
% 2.91/1.39  %Foreground sorts:
% 2.91/1.39  
% 2.91/1.39  
% 2.91/1.39  %Background operators:
% 2.91/1.39  
% 2.91/1.39  
% 2.91/1.39  %Foreground operators:
% 2.91/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.91/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.91/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.91/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.91/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.91/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.91/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.91/1.39  
% 2.91/1.40  tff(f_60, negated_conjecture, ~(![A, B]: ((![C, D]: ((r2_hidden(C, A) & r2_hidden(D, B)) => r1_xboole_0(C, D))) => r1_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_zfmisc_1)).
% 2.91/1.40  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.91/1.40  tff(f_50, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_xboole_0(C, B))) => r1_xboole_0(k3_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_zfmisc_1)).
% 2.91/1.40  tff(c_12, plain, (~r1_xboole_0(k3_tarski('#skF_3'), k3_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.91/1.40  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.91/1.40  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.91/1.40  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), A_6) | r1_xboole_0(k3_tarski(A_6), B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.91/1.40  tff(c_28, plain, (![A_24, B_25]: (r2_hidden('#skF_2'(A_24, B_25), A_24) | r1_xboole_0(k3_tarski(A_24), B_25))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.91/1.40  tff(c_14, plain, (![C_11, D_12]: (r1_xboole_0(C_11, D_12) | ~r2_hidden(D_12, '#skF_4') | ~r2_hidden(C_11, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.91/1.40  tff(c_49, plain, (![C_30, B_31]: (r1_xboole_0(C_30, '#skF_2'('#skF_4', B_31)) | ~r2_hidden(C_30, '#skF_3') | r1_xboole_0(k3_tarski('#skF_4'), B_31))), inference(resolution, [status(thm)], [c_28, c_14])).
% 2.91/1.40  tff(c_2, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.91/1.40  tff(c_99, plain, (![C_41, B_42, C_43]: (~r2_hidden(C_41, B_42) | ~r2_hidden(C_41, k3_tarski('#skF_4')) | r1_xboole_0(C_43, '#skF_2'('#skF_4', B_42)) | ~r2_hidden(C_43, '#skF_3'))), inference(resolution, [status(thm)], [c_49, c_2])).
% 2.91/1.40  tff(c_212, plain, (![A_67, B_68, C_69]: (~r2_hidden('#skF_1'(A_67, B_68), k3_tarski('#skF_4')) | r1_xboole_0(C_69, '#skF_2'('#skF_4', A_67)) | ~r2_hidden(C_69, '#skF_3') | r1_xboole_0(A_67, B_68))), inference(resolution, [status(thm)], [c_6, c_99])).
% 2.91/1.40  tff(c_221, plain, (![C_70, A_71]: (r1_xboole_0(C_70, '#skF_2'('#skF_4', A_71)) | ~r2_hidden(C_70, '#skF_3') | r1_xboole_0(A_71, k3_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_4, c_212])).
% 2.91/1.40  tff(c_240, plain, (![C_72]: (r1_xboole_0(C_72, '#skF_2'('#skF_4', k3_tarski('#skF_3'))) | ~r2_hidden(C_72, '#skF_3'))), inference(resolution, [status(thm)], [c_221, c_12])).
% 2.91/1.40  tff(c_8, plain, (![A_6, B_7]: (~r1_xboole_0('#skF_2'(A_6, B_7), B_7) | r1_xboole_0(k3_tarski(A_6), B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.91/1.40  tff(c_314, plain, (![A_84]: (r1_xboole_0(k3_tarski(A_84), '#skF_2'('#skF_4', k3_tarski('#skF_3'))) | ~r2_hidden('#skF_2'(A_84, '#skF_2'('#skF_4', k3_tarski('#skF_3'))), '#skF_3'))), inference(resolution, [status(thm)], [c_240, c_8])).
% 2.91/1.40  tff(c_319, plain, (r1_xboole_0(k3_tarski('#skF_3'), '#skF_2'('#skF_4', k3_tarski('#skF_3')))), inference(resolution, [status(thm)], [c_10, c_314])).
% 2.91/1.40  tff(c_323, plain, (![C_85]: (~r2_hidden(C_85, '#skF_2'('#skF_4', k3_tarski('#skF_3'))) | ~r2_hidden(C_85, k3_tarski('#skF_3')))), inference(resolution, [status(thm)], [c_319, c_2])).
% 2.91/1.40  tff(c_522, plain, (![B_126]: (~r2_hidden('#skF_1'('#skF_2'('#skF_4', k3_tarski('#skF_3')), B_126), k3_tarski('#skF_3')) | r1_xboole_0('#skF_2'('#skF_4', k3_tarski('#skF_3')), B_126))), inference(resolution, [status(thm)], [c_6, c_323])).
% 2.91/1.40  tff(c_527, plain, (r1_xboole_0('#skF_2'('#skF_4', k3_tarski('#skF_3')), k3_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_4, c_522])).
% 2.91/1.40  tff(c_533, plain, (r1_xboole_0(k3_tarski('#skF_4'), k3_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_527, c_8])).
% 2.91/1.40  tff(c_537, plain, (![C_127]: (~r2_hidden(C_127, k3_tarski('#skF_3')) | ~r2_hidden(C_127, k3_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_533, c_2])).
% 2.91/1.40  tff(c_566, plain, (![B_132]: (~r2_hidden('#skF_1'(k3_tarski('#skF_3'), B_132), k3_tarski('#skF_4')) | r1_xboole_0(k3_tarski('#skF_3'), B_132))), inference(resolution, [status(thm)], [c_6, c_537])).
% 2.91/1.40  tff(c_570, plain, (r1_xboole_0(k3_tarski('#skF_3'), k3_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_4, c_566])).
% 2.91/1.40  tff(c_574, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_12, c_570])).
% 2.91/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.40  
% 2.91/1.40  Inference rules
% 2.91/1.40  ----------------------
% 2.91/1.40  #Ref     : 0
% 2.91/1.40  #Sup     : 116
% 2.91/1.40  #Fact    : 0
% 2.91/1.40  #Define  : 0
% 2.91/1.40  #Split   : 4
% 2.91/1.40  #Chain   : 0
% 2.91/1.40  #Close   : 0
% 2.91/1.40  
% 2.91/1.40  Ordering : KBO
% 2.91/1.40  
% 2.91/1.40  Simplification rules
% 2.91/1.40  ----------------------
% 2.91/1.40  #Subsume      : 16
% 2.91/1.40  #Demod        : 8
% 2.91/1.40  #Tautology    : 7
% 2.91/1.40  #SimpNegUnit  : 1
% 2.91/1.40  #BackRed      : 1
% 2.91/1.40  
% 2.91/1.40  #Partial instantiations: 0
% 2.91/1.40  #Strategies tried      : 1
% 2.91/1.40  
% 2.91/1.40  Timing (in seconds)
% 2.91/1.40  ----------------------
% 2.91/1.41  Preprocessing        : 0.26
% 2.91/1.41  Parsing              : 0.15
% 2.91/1.41  CNF conversion       : 0.02
% 2.91/1.41  Main loop            : 0.38
% 2.91/1.41  Inferencing          : 0.17
% 2.91/1.41  Reduction            : 0.07
% 2.91/1.41  Demodulation         : 0.04
% 2.91/1.41  BG Simplification    : 0.02
% 2.91/1.41  Subsumption          : 0.11
% 2.91/1.41  Abstraction          : 0.01
% 2.91/1.41  MUC search           : 0.00
% 2.91/1.41  Cooper               : 0.00
% 2.91/1.41  Total                : 0.66
% 2.91/1.41  Index Insertion      : 0.00
% 2.91/1.41  Index Deletion       : 0.00
% 2.91/1.41  Index Matching       : 0.00
% 2.91/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
