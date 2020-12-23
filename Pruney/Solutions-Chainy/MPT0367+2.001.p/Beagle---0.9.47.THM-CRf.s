%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:47 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   29 (  37 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :    4
%              Number of atoms          :   39 (  64 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ! [D] :
                  ( m1_subset_1(D,B)
                 => r2_hidden(D,C) )
             => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(c_20,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_86,plain,(
    ! [A_31,B_32] :
      ( r2_hidden('#skF_2'(A_31,B_32),A_31)
      | r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_95,plain,(
    ! [A_33,B_34] :
      ( ~ v1_xboole_0(A_33)
      | r1_tarski(A_33,B_34) ) ),
    inference(resolution,[status(thm)],[c_86,c_2])).

tff(c_99,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_95,c_20])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( m1_subset_1(B_11,A_10)
      | ~ r2_hidden(B_11,A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_221,plain,(
    ! [A_54,B_55] :
      ( m1_subset_1('#skF_2'(A_54,B_55),A_54)
      | v1_xboole_0(A_54)
      | r1_tarski(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_86,c_12])).

tff(c_22,plain,(
    ! [D_16] :
      ( r2_hidden(D_16,'#skF_5')
      | ~ m1_subset_1(D_16,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_100,plain,(
    ! [A_35,B_36] :
      ( ~ r2_hidden('#skF_2'(A_35,B_36),B_36)
      | r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_115,plain,(
    ! [A_35] :
      ( r1_tarski(A_35,'#skF_5')
      | ~ m1_subset_1('#skF_2'(A_35,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_100])).

tff(c_229,plain,
    ( v1_xboole_0('#skF_4')
    | r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_221,c_115])).

tff(c_238,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_99,c_20,c_229])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:41:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.29  
% 1.93/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.29  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 1.93/1.29  
% 1.93/1.29  %Foreground sorts:
% 1.93/1.29  
% 1.93/1.29  
% 1.93/1.29  %Background operators:
% 1.93/1.29  
% 1.93/1.29  
% 1.93/1.29  %Foreground operators:
% 1.93/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.93/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.29  tff('#skF_5', type, '#skF_5': $i).
% 1.93/1.29  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.93/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.29  tff('#skF_4', type, '#skF_4': $i).
% 1.93/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.93/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.93/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.93/1.29  
% 1.93/1.30  tff(f_64, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, B) => r2_hidden(D, C))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_subset_1)).
% 1.93/1.30  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.93/1.30  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.93/1.30  tff(f_51, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 1.93/1.30  tff(c_20, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.93/1.30  tff(c_86, plain, (![A_31, B_32]: (r2_hidden('#skF_2'(A_31, B_32), A_31) | r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.93/1.30  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.30  tff(c_95, plain, (![A_33, B_34]: (~v1_xboole_0(A_33) | r1_tarski(A_33, B_34))), inference(resolution, [status(thm)], [c_86, c_2])).
% 1.93/1.30  tff(c_99, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_95, c_20])).
% 1.93/1.30  tff(c_12, plain, (![B_11, A_10]: (m1_subset_1(B_11, A_10) | ~r2_hidden(B_11, A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.93/1.30  tff(c_221, plain, (![A_54, B_55]: (m1_subset_1('#skF_2'(A_54, B_55), A_54) | v1_xboole_0(A_54) | r1_tarski(A_54, B_55))), inference(resolution, [status(thm)], [c_86, c_12])).
% 1.93/1.30  tff(c_22, plain, (![D_16]: (r2_hidden(D_16, '#skF_5') | ~m1_subset_1(D_16, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.93/1.30  tff(c_100, plain, (![A_35, B_36]: (~r2_hidden('#skF_2'(A_35, B_36), B_36) | r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.93/1.30  tff(c_115, plain, (![A_35]: (r1_tarski(A_35, '#skF_5') | ~m1_subset_1('#skF_2'(A_35, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_22, c_100])).
% 1.93/1.30  tff(c_229, plain, (v1_xboole_0('#skF_4') | r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_221, c_115])).
% 1.93/1.30  tff(c_238, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_99, c_20, c_229])).
% 1.93/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.30  
% 1.93/1.30  Inference rules
% 1.93/1.30  ----------------------
% 1.93/1.30  #Ref     : 0
% 1.93/1.30  #Sup     : 42
% 1.93/1.30  #Fact    : 0
% 1.93/1.30  #Define  : 0
% 1.93/1.30  #Split   : 3
% 1.93/1.30  #Chain   : 0
% 1.93/1.30  #Close   : 0
% 1.93/1.30  
% 1.93/1.30  Ordering : KBO
% 1.93/1.30  
% 1.93/1.30  Simplification rules
% 1.93/1.30  ----------------------
% 1.93/1.30  #Subsume      : 12
% 1.93/1.30  #Demod        : 1
% 1.93/1.30  #Tautology    : 9
% 1.93/1.30  #SimpNegUnit  : 6
% 1.93/1.30  #BackRed      : 0
% 1.93/1.30  
% 1.93/1.30  #Partial instantiations: 0
% 1.93/1.30  #Strategies tried      : 1
% 1.93/1.30  
% 1.93/1.30  Timing (in seconds)
% 1.93/1.30  ----------------------
% 1.93/1.30  Preprocessing        : 0.29
% 1.93/1.30  Parsing              : 0.16
% 1.93/1.30  CNF conversion       : 0.02
% 1.93/1.30  Main loop            : 0.20
% 1.93/1.30  Inferencing          : 0.09
% 1.93/1.30  Reduction            : 0.05
% 1.93/1.30  Demodulation         : 0.03
% 1.93/1.30  BG Simplification    : 0.01
% 1.93/1.30  Subsumption          : 0.04
% 1.93/1.30  Abstraction          : 0.01
% 1.93/1.30  MUC search           : 0.00
% 1.93/1.30  Cooper               : 0.00
% 1.93/1.30  Total                : 0.52
% 1.93/1.30  Index Insertion      : 0.00
% 1.93/1.30  Index Deletion       : 0.00
% 1.93/1.30  Index Matching       : 0.00
% 1.93/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
