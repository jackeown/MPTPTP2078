%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:34 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   31 (  34 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   42 (  51 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( ! [C] :
            ( r2_hidden(C,A)
           => r1_xboole_0(C,B) )
       => r1_xboole_0(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(c_18,plain,(
    ~ r1_xboole_0(k3_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( r2_hidden('#skF_1'(A_14,B_15),A_14)
      | r1_tarski(k3_tarski(A_14),B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,k3_tarski(B_13))
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [A_30,B_31] :
      ( r2_hidden('#skF_1'(A_30,B_31),A_30)
      | r1_tarski(k3_tarski(A_30),B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_20,plain,(
    ! [C_18] :
      ( r1_xboole_0(C_18,'#skF_3')
      | ~ r2_hidden(C_18,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_31,plain,(
    ! [B_31] :
      ( r1_xboole_0('#skF_1'('#skF_2',B_31),'#skF_3')
      | r1_tarski(k3_tarski('#skF_2'),B_31) ) ),
    inference(resolution,[status(thm)],[c_26,c_20])).

tff(c_45,plain,(
    ! [A_38,B_39,C_40] :
      ( r1_tarski(A_38,k4_xboole_0(B_39,C_40))
      | ~ r1_xboole_0(A_38,C_40)
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( ~ r1_tarski('#skF_1'(A_14,B_15),B_15)
      | r1_tarski(k3_tarski(A_14),B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_66,plain,(
    ! [A_46,B_47,C_48] :
      ( r1_tarski(k3_tarski(A_46),k4_xboole_0(B_47,C_48))
      | ~ r1_xboole_0('#skF_1'(A_46,k4_xboole_0(B_47,C_48)),C_48)
      | ~ r1_tarski('#skF_1'(A_46,k4_xboole_0(B_47,C_48)),B_47) ) ),
    inference(resolution,[status(thm)],[c_45,c_14])).

tff(c_71,plain,(
    ! [B_49] :
      ( ~ r1_tarski('#skF_1'('#skF_2',k4_xboole_0(B_49,'#skF_3')),B_49)
      | r1_tarski(k3_tarski('#skF_2'),k4_xboole_0(B_49,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_31,c_66])).

tff(c_82,plain,(
    ! [B_50] :
      ( r1_tarski(k3_tarski('#skF_2'),k4_xboole_0(k3_tarski(B_50),'#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_2',k4_xboole_0(k3_tarski(B_50),'#skF_3')),B_50) ) ),
    inference(resolution,[status(thm)],[c_12,c_71])).

tff(c_87,plain,(
    r1_tarski(k3_tarski('#skF_2'),k4_xboole_0(k3_tarski('#skF_2'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_82])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_xboole_0(A_1,C_3)
      | ~ r1_tarski(A_1,k4_xboole_0(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_90,plain,(
    r1_xboole_0(k3_tarski('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_87,c_2])).

tff(c_97,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_90])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:53:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.17  
% 1.64/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.17  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1
% 1.64/1.17  
% 1.64/1.17  %Foreground sorts:
% 1.64/1.17  
% 1.64/1.17  
% 1.64/1.17  %Background operators:
% 1.64/1.17  
% 1.64/1.17  
% 1.64/1.17  %Foreground operators:
% 1.64/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.64/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.64/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.64/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.17  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.64/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.64/1.17  
% 1.87/1.18  tff(f_64, negated_conjecture, ~(![A, B]: ((![C]: (r2_hidden(C, A) => r1_xboole_0(C, B))) => r1_xboole_0(k3_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_zfmisc_1)).
% 1.87/1.18  tff(f_56, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 1.87/1.18  tff(f_49, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 1.87/1.18  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 1.87/1.18  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 1.87/1.18  tff(c_18, plain, (~r1_xboole_0(k3_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.87/1.18  tff(c_16, plain, (![A_14, B_15]: (r2_hidden('#skF_1'(A_14, B_15), A_14) | r1_tarski(k3_tarski(A_14), B_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.87/1.18  tff(c_12, plain, (![A_12, B_13]: (r1_tarski(A_12, k3_tarski(B_13)) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.87/1.18  tff(c_26, plain, (![A_30, B_31]: (r2_hidden('#skF_1'(A_30, B_31), A_30) | r1_tarski(k3_tarski(A_30), B_31))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.87/1.18  tff(c_20, plain, (![C_18]: (r1_xboole_0(C_18, '#skF_3') | ~r2_hidden(C_18, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.87/1.18  tff(c_31, plain, (![B_31]: (r1_xboole_0('#skF_1'('#skF_2', B_31), '#skF_3') | r1_tarski(k3_tarski('#skF_2'), B_31))), inference(resolution, [status(thm)], [c_26, c_20])).
% 1.87/1.18  tff(c_45, plain, (![A_38, B_39, C_40]: (r1_tarski(A_38, k4_xboole_0(B_39, C_40)) | ~r1_xboole_0(A_38, C_40) | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.87/1.18  tff(c_14, plain, (![A_14, B_15]: (~r1_tarski('#skF_1'(A_14, B_15), B_15) | r1_tarski(k3_tarski(A_14), B_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.87/1.18  tff(c_66, plain, (![A_46, B_47, C_48]: (r1_tarski(k3_tarski(A_46), k4_xboole_0(B_47, C_48)) | ~r1_xboole_0('#skF_1'(A_46, k4_xboole_0(B_47, C_48)), C_48) | ~r1_tarski('#skF_1'(A_46, k4_xboole_0(B_47, C_48)), B_47))), inference(resolution, [status(thm)], [c_45, c_14])).
% 1.87/1.18  tff(c_71, plain, (![B_49]: (~r1_tarski('#skF_1'('#skF_2', k4_xboole_0(B_49, '#skF_3')), B_49) | r1_tarski(k3_tarski('#skF_2'), k4_xboole_0(B_49, '#skF_3')))), inference(resolution, [status(thm)], [c_31, c_66])).
% 1.87/1.18  tff(c_82, plain, (![B_50]: (r1_tarski(k3_tarski('#skF_2'), k4_xboole_0(k3_tarski(B_50), '#skF_3')) | ~r2_hidden('#skF_1'('#skF_2', k4_xboole_0(k3_tarski(B_50), '#skF_3')), B_50))), inference(resolution, [status(thm)], [c_12, c_71])).
% 1.87/1.18  tff(c_87, plain, (r1_tarski(k3_tarski('#skF_2'), k4_xboole_0(k3_tarski('#skF_2'), '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_82])).
% 1.87/1.18  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_xboole_0(A_1, C_3) | ~r1_tarski(A_1, k4_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.18  tff(c_90, plain, (r1_xboole_0(k3_tarski('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_87, c_2])).
% 1.87/1.18  tff(c_97, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_90])).
% 1.87/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.18  
% 1.87/1.18  Inference rules
% 1.87/1.18  ----------------------
% 1.87/1.18  #Ref     : 0
% 1.87/1.18  #Sup     : 14
% 1.87/1.18  #Fact    : 0
% 1.87/1.18  #Define  : 0
% 1.87/1.18  #Split   : 0
% 1.87/1.18  #Chain   : 0
% 1.87/1.18  #Close   : 0
% 1.87/1.18  
% 1.87/1.18  Ordering : KBO
% 1.87/1.18  
% 1.87/1.18  Simplification rules
% 1.87/1.18  ----------------------
% 1.87/1.18  #Subsume      : 1
% 1.87/1.18  #Demod        : 0
% 1.87/1.18  #Tautology    : 2
% 1.87/1.18  #SimpNegUnit  : 1
% 1.87/1.18  #BackRed      : 0
% 1.87/1.18  
% 1.87/1.18  #Partial instantiations: 0
% 1.87/1.18  #Strategies tried      : 1
% 1.87/1.18  
% 1.87/1.18  Timing (in seconds)
% 1.87/1.18  ----------------------
% 1.87/1.18  Preprocessing        : 0.27
% 1.87/1.18  Parsing              : 0.16
% 1.87/1.18  CNF conversion       : 0.02
% 1.87/1.18  Main loop            : 0.14
% 1.87/1.18  Inferencing          : 0.07
% 1.87/1.18  Reduction            : 0.03
% 1.87/1.18  Demodulation         : 0.02
% 1.87/1.18  BG Simplification    : 0.01
% 1.87/1.18  Subsumption          : 0.03
% 1.87/1.18  Abstraction          : 0.00
% 1.87/1.18  MUC search           : 0.00
% 1.87/1.18  Cooper               : 0.00
% 1.87/1.18  Total                : 0.43
% 1.87/1.18  Index Insertion      : 0.00
% 1.87/1.18  Index Deletion       : 0.00
% 1.87/1.18  Index Matching       : 0.00
% 1.87/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
