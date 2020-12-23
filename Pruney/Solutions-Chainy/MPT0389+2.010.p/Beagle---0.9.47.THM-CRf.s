%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:13 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   32 (  35 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  55 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => ( A = k1_xboole_0
          | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(B,C) )
     => ( A = k1_xboole_0
        | r1_tarski(B,k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(c_18,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_31,plain,(
    ! [A_21,B_22] :
      ( r2_hidden('#skF_1'(A_21,B_22),A_21)
      | r1_tarski(B_22,k1_setfam_1(A_21))
      | k1_xboole_0 = A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_47,plain,(
    ! [A_28,B_29,A_30] :
      ( r2_hidden('#skF_1'(A_28,B_29),A_30)
      | ~ m1_subset_1(A_28,k1_zfmisc_1(A_30))
      | r1_tarski(B_29,k1_setfam_1(A_28))
      | k1_xboole_0 = A_28 ) ),
    inference(resolution,[status(thm)],[c_31,c_2])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k1_setfam_1(B_8),A_7)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_35,plain,(
    ! [B_23,A_24] :
      ( ~ r1_tarski(B_23,'#skF_1'(A_24,B_23))
      | r1_tarski(B_23,k1_setfam_1(A_24))
      | k1_xboole_0 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_39,plain,(
    ! [B_8,A_24] :
      ( r1_tarski(k1_setfam_1(B_8),k1_setfam_1(A_24))
      | k1_xboole_0 = A_24
      | ~ r2_hidden('#skF_1'(A_24,k1_setfam_1(B_8)),B_8) ) ),
    inference(resolution,[status(thm)],[c_8,c_35])).

tff(c_56,plain,(
    ! [A_31,A_32] :
      ( ~ m1_subset_1(A_31,k1_zfmisc_1(A_32))
      | r1_tarski(k1_setfam_1(A_32),k1_setfam_1(A_31))
      | k1_xboole_0 = A_31 ) ),
    inference(resolution,[status(thm)],[c_47,c_39])).

tff(c_14,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_59,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_3'))
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_56,c_14])).

tff(c_62,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_59])).

tff(c_65,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_62])).

tff(c_69,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_65])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:16:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.11  
% 1.65/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.11  %$ r2_hidden > r1_tarski > m1_subset_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.65/1.11  
% 1.65/1.11  %Foreground sorts:
% 1.65/1.11  
% 1.65/1.11  
% 1.65/1.11  %Background operators:
% 1.65/1.11  
% 1.65/1.11  
% 1.65/1.11  %Foreground operators:
% 1.65/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.65/1.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.65/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.65/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.65/1.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.65/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.11  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.65/1.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.65/1.11  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.65/1.11  
% 1.65/1.12  tff(f_56, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 1.65/1.12  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.65/1.12  tff(f_49, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(B, C))) => ((A = k1_xboole_0) | r1_tarski(B, k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_setfam_1)).
% 1.65/1.12  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 1.65/1.12  tff(f_40, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 1.65/1.12  tff(c_18, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.65/1.12  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.65/1.12  tff(c_16, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.65/1.12  tff(c_31, plain, (![A_21, B_22]: (r2_hidden('#skF_1'(A_21, B_22), A_21) | r1_tarski(B_22, k1_setfam_1(A_21)) | k1_xboole_0=A_21)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.65/1.12  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.65/1.12  tff(c_47, plain, (![A_28, B_29, A_30]: (r2_hidden('#skF_1'(A_28, B_29), A_30) | ~m1_subset_1(A_28, k1_zfmisc_1(A_30)) | r1_tarski(B_29, k1_setfam_1(A_28)) | k1_xboole_0=A_28)), inference(resolution, [status(thm)], [c_31, c_2])).
% 1.65/1.12  tff(c_8, plain, (![B_8, A_7]: (r1_tarski(k1_setfam_1(B_8), A_7) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.65/1.12  tff(c_35, plain, (![B_23, A_24]: (~r1_tarski(B_23, '#skF_1'(A_24, B_23)) | r1_tarski(B_23, k1_setfam_1(A_24)) | k1_xboole_0=A_24)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.65/1.12  tff(c_39, plain, (![B_8, A_24]: (r1_tarski(k1_setfam_1(B_8), k1_setfam_1(A_24)) | k1_xboole_0=A_24 | ~r2_hidden('#skF_1'(A_24, k1_setfam_1(B_8)), B_8))), inference(resolution, [status(thm)], [c_8, c_35])).
% 1.65/1.12  tff(c_56, plain, (![A_31, A_32]: (~m1_subset_1(A_31, k1_zfmisc_1(A_32)) | r1_tarski(k1_setfam_1(A_32), k1_setfam_1(A_31)) | k1_xboole_0=A_31)), inference(resolution, [status(thm)], [c_47, c_39])).
% 1.65/1.12  tff(c_14, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.65/1.12  tff(c_59, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_3')) | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_56, c_14])).
% 1.65/1.12  tff(c_62, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_16, c_59])).
% 1.65/1.12  tff(c_65, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_6, c_62])).
% 1.65/1.12  tff(c_69, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_65])).
% 1.65/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.12  
% 1.65/1.12  Inference rules
% 1.65/1.12  ----------------------
% 1.65/1.12  #Ref     : 0
% 1.65/1.12  #Sup     : 9
% 1.65/1.12  #Fact    : 0
% 1.65/1.12  #Define  : 0
% 1.65/1.12  #Split   : 0
% 1.65/1.12  #Chain   : 0
% 1.65/1.12  #Close   : 0
% 1.65/1.12  
% 1.65/1.12  Ordering : KBO
% 1.65/1.12  
% 1.65/1.12  Simplification rules
% 1.65/1.12  ----------------------
% 1.65/1.12  #Subsume      : 0
% 1.65/1.12  #Demod        : 1
% 1.65/1.12  #Tautology    : 1
% 1.65/1.12  #SimpNegUnit  : 1
% 1.65/1.12  #BackRed      : 0
% 1.65/1.12  
% 1.65/1.12  #Partial instantiations: 0
% 1.65/1.12  #Strategies tried      : 1
% 1.65/1.12  
% 1.65/1.12  Timing (in seconds)
% 1.65/1.12  ----------------------
% 1.65/1.13  Preprocessing        : 0.26
% 1.65/1.13  Parsing              : 0.14
% 1.65/1.13  CNF conversion       : 0.02
% 1.65/1.13  Main loop            : 0.10
% 1.65/1.13  Inferencing          : 0.05
% 1.65/1.13  Reduction            : 0.02
% 1.65/1.13  Demodulation         : 0.01
% 1.65/1.13  BG Simplification    : 0.01
% 1.65/1.13  Subsumption          : 0.02
% 1.65/1.13  Abstraction          : 0.00
% 1.65/1.13  MUC search           : 0.00
% 1.65/1.13  Cooper               : 0.00
% 1.65/1.13  Total                : 0.39
% 1.65/1.13  Index Insertion      : 0.00
% 1.65/1.13  Index Deletion       : 0.00
% 1.65/1.13  Index Matching       : 0.00
% 1.65/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
