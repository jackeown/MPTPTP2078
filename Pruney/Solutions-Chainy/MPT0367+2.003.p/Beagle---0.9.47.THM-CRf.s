%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:47 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   29 (  36 expanded)
%              Number of leaves         :   16 (  21 expanded)
%              Depth                    :    4
%              Number of atoms          :   41 (  64 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ! [D] :
                  ( m1_subset_1(D,B)
                 => r2_hidden(D,C) )
             => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_37,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(c_18,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_47,plain,(
    ! [A_22,B_23] :
      ( r2_hidden('#skF_1'(A_22,B_23),A_22)
      | r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( ~ v1_xboole_0(B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_52,plain,(
    ! [A_24,B_25] :
      ( ~ v1_xboole_0(A_24)
      | r1_tarski(A_24,B_25) ) ),
    inference(resolution,[status(thm)],[c_47,c_8])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_18])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_57,plain,(
    ! [B_26,A_27] :
      ( m1_subset_1(B_26,A_27)
      | ~ r2_hidden(B_26,A_27)
      | v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_178,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1('#skF_1'(A_46,B_47),A_46)
      | v1_xboole_0(A_46)
      | r1_tarski(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_6,c_57])).

tff(c_20,plain,(
    ! [D_14] :
      ( r2_hidden(D_14,'#skF_4')
      | ~ m1_subset_1(D_14,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_68,plain,(
    ! [A_28,B_29] :
      ( ~ r2_hidden('#skF_1'(A_28,B_29),B_29)
      | r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_78,plain,(
    ! [A_28] :
      ( r1_tarski(A_28,'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_28,'#skF_4'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_68])).

tff(c_182,plain,
    ( v1_xboole_0('#skF_3')
    | r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_178,c_78])).

tff(c_193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_56,c_18,c_182])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.31  % Computer   : n017.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % DateTime   : Tue Dec  1 18:32:01 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.17/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.15  
% 1.75/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.15  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.75/1.15  
% 1.75/1.15  %Foreground sorts:
% 1.75/1.15  
% 1.75/1.15  
% 1.75/1.15  %Background operators:
% 1.75/1.15  
% 1.75/1.15  
% 1.75/1.15  %Foreground operators:
% 1.75/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.75/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.75/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.75/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.75/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.75/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.75/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.15  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.75/1.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.75/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.75/1.15  
% 1.75/1.16  tff(f_63, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, B) => r2_hidden(D, C))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_subset_1)).
% 1.75/1.16  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.75/1.16  tff(f_37, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 1.75/1.16  tff(f_50, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 1.75/1.16  tff(c_18, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.75/1.16  tff(c_47, plain, (![A_22, B_23]: (r2_hidden('#skF_1'(A_22, B_23), A_22) | r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.75/1.16  tff(c_8, plain, (![B_7, A_6]: (~v1_xboole_0(B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.75/1.16  tff(c_52, plain, (![A_24, B_25]: (~v1_xboole_0(A_24) | r1_tarski(A_24, B_25))), inference(resolution, [status(thm)], [c_47, c_8])).
% 1.75/1.16  tff(c_56, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_18])).
% 1.75/1.16  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.75/1.16  tff(c_57, plain, (![B_26, A_27]: (m1_subset_1(B_26, A_27) | ~r2_hidden(B_26, A_27) | v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.75/1.16  tff(c_178, plain, (![A_46, B_47]: (m1_subset_1('#skF_1'(A_46, B_47), A_46) | v1_xboole_0(A_46) | r1_tarski(A_46, B_47))), inference(resolution, [status(thm)], [c_6, c_57])).
% 1.75/1.16  tff(c_20, plain, (![D_14]: (r2_hidden(D_14, '#skF_4') | ~m1_subset_1(D_14, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.75/1.16  tff(c_68, plain, (![A_28, B_29]: (~r2_hidden('#skF_1'(A_28, B_29), B_29) | r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.75/1.16  tff(c_78, plain, (![A_28]: (r1_tarski(A_28, '#skF_4') | ~m1_subset_1('#skF_1'(A_28, '#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_68])).
% 1.75/1.16  tff(c_182, plain, (v1_xboole_0('#skF_3') | r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_178, c_78])).
% 1.75/1.16  tff(c_193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_56, c_18, c_182])).
% 1.75/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.16  
% 1.75/1.16  Inference rules
% 1.75/1.16  ----------------------
% 1.75/1.16  #Ref     : 0
% 1.75/1.16  #Sup     : 32
% 1.75/1.16  #Fact    : 0
% 1.75/1.16  #Define  : 0
% 1.75/1.16  #Split   : 2
% 1.75/1.16  #Chain   : 0
% 1.75/1.16  #Close   : 0
% 1.75/1.16  
% 1.75/1.16  Ordering : KBO
% 1.75/1.16  
% 1.75/1.16  Simplification rules
% 1.75/1.16  ----------------------
% 1.75/1.16  #Subsume      : 11
% 1.75/1.16  #Demod        : 2
% 1.75/1.16  #Tautology    : 5
% 1.75/1.16  #SimpNegUnit  : 4
% 1.75/1.16  #BackRed      : 1
% 1.75/1.16  
% 1.75/1.16  #Partial instantiations: 0
% 1.75/1.16  #Strategies tried      : 1
% 1.75/1.16  
% 1.75/1.16  Timing (in seconds)
% 1.75/1.16  ----------------------
% 1.75/1.17  Preprocessing        : 0.27
% 1.75/1.17  Parsing              : 0.15
% 1.75/1.17  CNF conversion       : 0.02
% 1.75/1.17  Main loop            : 0.18
% 1.75/1.17  Inferencing          : 0.08
% 1.75/1.17  Reduction            : 0.04
% 1.75/1.17  Demodulation         : 0.03
% 1.75/1.17  BG Simplification    : 0.01
% 1.75/1.17  Subsumption          : 0.04
% 1.75/1.17  Abstraction          : 0.01
% 1.75/1.17  MUC search           : 0.00
% 1.75/1.17  Cooper               : 0.00
% 1.75/1.17  Total                : 0.48
% 1.75/1.17  Index Insertion      : 0.00
% 1.75/1.17  Index Deletion       : 0.00
% 1.75/1.17  Index Matching       : 0.00
% 1.75/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
