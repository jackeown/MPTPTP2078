%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:45 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   38 (  89 expanded)
%              Number of leaves         :   14 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :   59 ( 230 expanded)
%              Number of equality atoms :   12 (  41 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_53,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(A))
                 => ( r2_hidden(D,B)
                  <=> r2_hidden(D,C) ) )
             => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(c_12,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r2_hidden('#skF_2'(A_1,B_2),A_1)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_23,plain,(
    ! [A_14,C_15,B_16] :
      ( m1_subset_1(A_14,C_15)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(C_15))
      | ~ r2_hidden(A_14,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_43,plain,(
    ! [A_19] :
      ( m1_subset_1(A_19,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_19,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_23])).

tff(c_20,plain,(
    ! [D_11] :
      ( r2_hidden(D_11,'#skF_5')
      | ~ r2_hidden(D_11,'#skF_4')
      | ~ m1_subset_1(D_11,k1_zfmisc_1('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_50,plain,(
    ! [A_19] :
      ( r2_hidden(A_19,'#skF_5')
      | ~ r2_hidden(A_19,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_43,c_20])).

tff(c_69,plain,(
    ! [A_25,B_26] :
      ( r2_hidden('#skF_1'(A_25,B_26),B_26)
      | ~ r2_hidden('#skF_2'(A_25,B_26),B_26)
      | B_26 = A_25 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_143,plain,(
    ! [A_34] :
      ( r2_hidden('#skF_1'(A_34,'#skF_5'),'#skF_5')
      | A_34 = '#skF_5'
      | ~ r2_hidden('#skF_2'(A_34,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_69])).

tff(c_147,plain,
    ( r2_hidden('#skF_1'('#skF_4','#skF_5'),'#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8,c_143])).

tff(c_154,plain,(
    r2_hidden('#skF_1'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_12,c_147])).

tff(c_14,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    ! [A_17] :
      ( m1_subset_1(A_17,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_17,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_14,c_23])).

tff(c_18,plain,(
    ! [D_11] :
      ( r2_hidden(D_11,'#skF_4')
      | ~ r2_hidden(D_11,'#skF_5')
      | ~ m1_subset_1(D_11,k1_zfmisc_1('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_41,plain,(
    ! [A_17] :
      ( r2_hidden(A_17,'#skF_4')
      | ~ r2_hidden(A_17,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_18])).

tff(c_166,plain,(
    r2_hidden('#skF_1'('#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_154,c_41])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r2_hidden('#skF_2'(A_1,B_2),A_1)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_168,plain,
    ( ~ r2_hidden('#skF_2'('#skF_4','#skF_5'),'#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_166,c_2])).

tff(c_175,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_168])).

tff(c_181,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_175])).

tff(c_229,plain,
    ( ~ r2_hidden('#skF_1'('#skF_4','#skF_5'),'#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6,c_181])).

tff(c_235,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_229])).

tff(c_237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_235])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:06:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.21  
% 2.04/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.22  %$ r2_hidden > m1_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.04/1.22  
% 2.04/1.22  %Foreground sorts:
% 2.04/1.22  
% 2.04/1.22  
% 2.04/1.22  %Background operators:
% 2.04/1.22  
% 2.04/1.22  
% 2.04/1.22  %Foreground operators:
% 2.04/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.22  tff('#skF_5', type, '#skF_5': $i).
% 2.04/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.04/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.04/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.22  tff('#skF_4', type, '#skF_4': $i).
% 2.04/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.04/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.04/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.04/1.22  
% 2.04/1.23  tff(f_53, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_setfam_1)).
% 2.04/1.23  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 2.04/1.23  tff(f_38, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.04/1.23  tff(c_12, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.04/1.23  tff(c_8, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r2_hidden('#skF_2'(A_1, B_2), A_1) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.04/1.23  tff(c_16, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.04/1.23  tff(c_23, plain, (![A_14, C_15, B_16]: (m1_subset_1(A_14, C_15) | ~m1_subset_1(B_16, k1_zfmisc_1(C_15)) | ~r2_hidden(A_14, B_16))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.04/1.23  tff(c_43, plain, (![A_19]: (m1_subset_1(A_19, k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_19, '#skF_4'))), inference(resolution, [status(thm)], [c_16, c_23])).
% 2.04/1.23  tff(c_20, plain, (![D_11]: (r2_hidden(D_11, '#skF_5') | ~r2_hidden(D_11, '#skF_4') | ~m1_subset_1(D_11, k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.04/1.23  tff(c_50, plain, (![A_19]: (r2_hidden(A_19, '#skF_5') | ~r2_hidden(A_19, '#skF_4'))), inference(resolution, [status(thm)], [c_43, c_20])).
% 2.04/1.23  tff(c_69, plain, (![A_25, B_26]: (r2_hidden('#skF_1'(A_25, B_26), B_26) | ~r2_hidden('#skF_2'(A_25, B_26), B_26) | B_26=A_25)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.04/1.23  tff(c_143, plain, (![A_34]: (r2_hidden('#skF_1'(A_34, '#skF_5'), '#skF_5') | A_34='#skF_5' | ~r2_hidden('#skF_2'(A_34, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_50, c_69])).
% 2.04/1.23  tff(c_147, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_5'), '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_8, c_143])).
% 2.04/1.23  tff(c_154, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_12, c_12, c_147])).
% 2.04/1.23  tff(c_14, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.04/1.23  tff(c_30, plain, (![A_17]: (m1_subset_1(A_17, k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_17, '#skF_5'))), inference(resolution, [status(thm)], [c_14, c_23])).
% 2.04/1.23  tff(c_18, plain, (![D_11]: (r2_hidden(D_11, '#skF_4') | ~r2_hidden(D_11, '#skF_5') | ~m1_subset_1(D_11, k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.04/1.23  tff(c_41, plain, (![A_17]: (r2_hidden(A_17, '#skF_4') | ~r2_hidden(A_17, '#skF_5'))), inference(resolution, [status(thm)], [c_30, c_18])).
% 2.04/1.23  tff(c_166, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_154, c_41])).
% 2.04/1.23  tff(c_6, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), A_1) | r2_hidden('#skF_2'(A_1, B_2), A_1) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.04/1.23  tff(c_2, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), A_1) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.04/1.23  tff(c_168, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_5'), '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_166, c_2])).
% 2.04/1.23  tff(c_175, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_12, c_168])).
% 2.04/1.23  tff(c_181, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_50, c_175])).
% 2.04/1.23  tff(c_229, plain, (~r2_hidden('#skF_1'('#skF_4', '#skF_5'), '#skF_4') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_6, c_181])).
% 2.04/1.23  tff(c_235, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_166, c_229])).
% 2.04/1.23  tff(c_237, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_235])).
% 2.04/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.23  
% 2.04/1.23  Inference rules
% 2.04/1.23  ----------------------
% 2.04/1.23  #Ref     : 0
% 2.04/1.23  #Sup     : 46
% 2.04/1.23  #Fact    : 0
% 2.04/1.23  #Define  : 0
% 2.04/1.23  #Split   : 1
% 2.04/1.23  #Chain   : 0
% 2.04/1.23  #Close   : 0
% 2.04/1.23  
% 2.04/1.23  Ordering : KBO
% 2.04/1.23  
% 2.04/1.23  Simplification rules
% 2.04/1.23  ----------------------
% 2.04/1.23  #Subsume      : 7
% 2.04/1.23  #Demod        : 2
% 2.04/1.23  #Tautology    : 9
% 2.04/1.23  #SimpNegUnit  : 7
% 2.04/1.23  #BackRed      : 0
% 2.04/1.23  
% 2.04/1.23  #Partial instantiations: 0
% 2.04/1.23  #Strategies tried      : 1
% 2.04/1.23  
% 2.04/1.23  Timing (in seconds)
% 2.04/1.23  ----------------------
% 2.04/1.23  Preprocessing        : 0.26
% 2.04/1.23  Parsing              : 0.14
% 2.04/1.23  CNF conversion       : 0.02
% 2.04/1.23  Main loop            : 0.20
% 2.04/1.23  Inferencing          : 0.08
% 2.04/1.23  Reduction            : 0.05
% 2.04/1.23  Demodulation         : 0.03
% 2.04/1.23  BG Simplification    : 0.01
% 2.04/1.23  Subsumption          : 0.05
% 2.04/1.23  Abstraction          : 0.01
% 2.04/1.23  MUC search           : 0.00
% 2.04/1.23  Cooper               : 0.00
% 2.04/1.23  Total                : 0.49
% 2.04/1.23  Index Insertion      : 0.00
% 2.04/1.23  Index Deletion       : 0.00
% 2.04/1.23  Index Matching       : 0.00
% 2.04/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
