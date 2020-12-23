%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:43 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   35 (  66 expanded)
%              Number of leaves         :   15 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   52 ( 150 expanded)
%              Number of equality atoms :    5 (  16 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_59,negated_conjecture,(
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
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_16,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_48,plain,(
    ! [A_28,C_29,B_30] :
      ( m1_subset_1(A_28,C_29)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(C_29))
      | ~ r2_hidden(A_28,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_55,plain,(
    ! [A_31] :
      ( m1_subset_1(A_31,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_31,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_48])).

tff(c_22,plain,(
    ! [D_15] :
      ( r2_hidden(D_15,'#skF_3')
      | ~ r2_hidden(D_15,'#skF_4')
      | ~ m1_subset_1(D_15,k1_zfmisc_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_67,plain,(
    ! [A_32] :
      ( r2_hidden(A_32,'#skF_3')
      | ~ r2_hidden(A_32,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_55,c_22])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_108,plain,(
    ! [A_38] :
      ( r1_tarski(A_38,'#skF_3')
      | ~ r2_hidden('#skF_1'(A_38,'#skF_3'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_67,c_4])).

tff(c_118,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_108])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_120,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_118,c_8])).

tff(c_123,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_120])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_76,plain,(
    ! [A_33] :
      ( m1_subset_1(A_33,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_33,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_48])).

tff(c_24,plain,(
    ! [D_15] :
      ( r2_hidden(D_15,'#skF_4')
      | ~ r2_hidden(D_15,'#skF_3')
      | ~ m1_subset_1(D_15,k1_zfmisc_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_84,plain,(
    ! [A_34] :
      ( r2_hidden(A_34,'#skF_4')
      | ~ r2_hidden(A_34,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_76,c_24])).

tff(c_124,plain,(
    ! [B_39] :
      ( r2_hidden('#skF_1'('#skF_3',B_39),'#skF_4')
      | r1_tarski('#skF_3',B_39) ) ),
    inference(resolution,[status(thm)],[c_6,c_84])).

tff(c_134,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_124,c_4])).

tff(c_141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_123,c_134])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:28:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.22  
% 1.79/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.22  %$ r2_hidden > r1_tarski > m1_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.79/1.22  
% 1.79/1.22  %Foreground sorts:
% 1.79/1.22  
% 1.79/1.22  
% 1.79/1.22  %Background operators:
% 1.79/1.22  
% 1.79/1.22  
% 1.79/1.22  %Foreground operators:
% 1.79/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.79/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.79/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.79/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.79/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.79/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.79/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.79/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.79/1.22  
% 1.94/1.23  tff(f_59, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_setfam_1)).
% 1.94/1.23  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.94/1.23  tff(f_44, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 1.94/1.23  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.94/1.23  tff(c_16, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.94/1.23  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.94/1.23  tff(c_18, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.94/1.23  tff(c_48, plain, (![A_28, C_29, B_30]: (m1_subset_1(A_28, C_29) | ~m1_subset_1(B_30, k1_zfmisc_1(C_29)) | ~r2_hidden(A_28, B_30))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.94/1.23  tff(c_55, plain, (![A_31]: (m1_subset_1(A_31, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_31, '#skF_4'))), inference(resolution, [status(thm)], [c_18, c_48])).
% 1.94/1.23  tff(c_22, plain, (![D_15]: (r2_hidden(D_15, '#skF_3') | ~r2_hidden(D_15, '#skF_4') | ~m1_subset_1(D_15, k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.94/1.23  tff(c_67, plain, (![A_32]: (r2_hidden(A_32, '#skF_3') | ~r2_hidden(A_32, '#skF_4'))), inference(resolution, [status(thm)], [c_55, c_22])).
% 1.94/1.23  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.94/1.23  tff(c_108, plain, (![A_38]: (r1_tarski(A_38, '#skF_3') | ~r2_hidden('#skF_1'(A_38, '#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_67, c_4])).
% 1.94/1.23  tff(c_118, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_6, c_108])).
% 1.94/1.23  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.94/1.23  tff(c_120, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_118, c_8])).
% 1.94/1.23  tff(c_123, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_16, c_120])).
% 1.94/1.23  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.94/1.23  tff(c_76, plain, (![A_33]: (m1_subset_1(A_33, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_33, '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_48])).
% 1.94/1.23  tff(c_24, plain, (![D_15]: (r2_hidden(D_15, '#skF_4') | ~r2_hidden(D_15, '#skF_3') | ~m1_subset_1(D_15, k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.94/1.23  tff(c_84, plain, (![A_34]: (r2_hidden(A_34, '#skF_4') | ~r2_hidden(A_34, '#skF_3'))), inference(resolution, [status(thm)], [c_76, c_24])).
% 1.94/1.23  tff(c_124, plain, (![B_39]: (r2_hidden('#skF_1'('#skF_3', B_39), '#skF_4') | r1_tarski('#skF_3', B_39))), inference(resolution, [status(thm)], [c_6, c_84])).
% 1.94/1.23  tff(c_134, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_124, c_4])).
% 1.94/1.23  tff(c_141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_123, c_123, c_134])).
% 1.94/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.23  
% 1.94/1.23  Inference rules
% 1.94/1.23  ----------------------
% 1.94/1.23  #Ref     : 0
% 1.94/1.23  #Sup     : 23
% 1.94/1.23  #Fact    : 0
% 1.94/1.23  #Define  : 0
% 1.94/1.23  #Split   : 0
% 1.94/1.23  #Chain   : 0
% 1.94/1.23  #Close   : 0
% 1.94/1.23  
% 1.94/1.23  Ordering : KBO
% 1.94/1.23  
% 1.94/1.23  Simplification rules
% 1.94/1.23  ----------------------
% 1.94/1.23  #Subsume      : 2
% 1.94/1.23  #Demod        : 4
% 1.94/1.23  #Tautology    : 7
% 1.94/1.23  #SimpNegUnit  : 2
% 1.94/1.23  #BackRed      : 0
% 1.94/1.23  
% 1.94/1.23  #Partial instantiations: 0
% 1.94/1.23  #Strategies tried      : 1
% 1.94/1.23  
% 1.94/1.23  Timing (in seconds)
% 1.94/1.23  ----------------------
% 1.94/1.23  Preprocessing        : 0.28
% 1.94/1.23  Parsing              : 0.16
% 1.94/1.23  CNF conversion       : 0.02
% 1.94/1.23  Main loop            : 0.13
% 1.94/1.23  Inferencing          : 0.05
% 1.94/1.23  Reduction            : 0.03
% 1.94/1.23  Demodulation         : 0.02
% 1.94/1.23  BG Simplification    : 0.01
% 1.94/1.23  Subsumption          : 0.03
% 1.94/1.23  Abstraction          : 0.01
% 1.94/1.23  MUC search           : 0.00
% 1.94/1.23  Cooper               : 0.00
% 1.94/1.23  Total                : 0.43
% 1.94/1.23  Index Insertion      : 0.00
% 1.94/1.23  Index Deletion       : 0.00
% 1.94/1.23  Index Matching       : 0.00
% 1.94/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
