%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:47 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   40 (  46 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   55 (  91 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( ( r1_tarski(B,C)
                    & r1_xboole_0(D,C) )
                 => r1_tarski(B,k3_subset_1(A,D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_subset_1)).

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

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

tff(c_24,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_61,plain,(
    ! [A_35,B_36,C_37] :
      ( ~ r1_xboole_0(A_35,B_36)
      | ~ r2_hidden(C_37,B_36)
      | ~ r2_hidden(C_37,A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_71,plain,(
    ! [C_38] :
      ( ~ r2_hidden(C_38,'#skF_4')
      | ~ r2_hidden(C_38,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_61])).

tff(c_89,plain,(
    ! [A_40] :
      ( ~ r2_hidden('#skF_1'(A_40,'#skF_5'),'#skF_4')
      | r1_xboole_0(A_40,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4,c_71])).

tff(c_94,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_89])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = A_9
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_101,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_94,c_12])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_xboole_0(A_6,C_8)
      | ~ r1_tarski(A_6,k4_xboole_0(B_7,C_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_105,plain,(
    ! [A_6] :
      ( r1_xboole_0(A_6,'#skF_5')
      | ~ r1_tarski(A_6,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_8])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_143,plain,(
    ! [B_44,A_45,C_46] :
      ( r1_tarski(B_44,k3_subset_1(A_45,C_46))
      | ~ r1_xboole_0(B_44,C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(A_45))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_20,plain,(
    ~ r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_146,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_143,c_20])).

tff(c_149,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_146])).

tff(c_155,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_105,c_149])).

tff(c_163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n021.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 16:57:49 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.14  
% 1.78/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.14  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.78/1.14  
% 1.78/1.14  %Foreground sorts:
% 1.78/1.14  
% 1.78/1.14  
% 1.78/1.14  %Background operators:
% 1.78/1.14  
% 1.78/1.14  
% 1.78/1.14  %Foreground operators:
% 1.78/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.78/1.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.78/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.78/1.14  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.78/1.14  tff('#skF_5', type, '#skF_5': $i).
% 1.78/1.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.78/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.78/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.78/1.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.78/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.78/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.78/1.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.78/1.14  
% 1.78/1.15  tff(f_77, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_xboole_0(D, C)) => r1_tarski(B, k3_subset_1(A, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_subset_1)).
% 1.78/1.15  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.78/1.15  tff(f_53, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.78/1.15  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 1.78/1.15  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 1.78/1.15  tff(c_24, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.78/1.15  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.78/1.15  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.78/1.15  tff(c_22, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.78/1.15  tff(c_61, plain, (![A_35, B_36, C_37]: (~r1_xboole_0(A_35, B_36) | ~r2_hidden(C_37, B_36) | ~r2_hidden(C_37, A_35))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.78/1.15  tff(c_71, plain, (![C_38]: (~r2_hidden(C_38, '#skF_4') | ~r2_hidden(C_38, '#skF_5'))), inference(resolution, [status(thm)], [c_22, c_61])).
% 1.78/1.15  tff(c_89, plain, (![A_40]: (~r2_hidden('#skF_1'(A_40, '#skF_5'), '#skF_4') | r1_xboole_0(A_40, '#skF_5'))), inference(resolution, [status(thm)], [c_4, c_71])).
% 1.78/1.15  tff(c_94, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_89])).
% 1.78/1.15  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=A_9 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.78/1.15  tff(c_101, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_94, c_12])).
% 1.78/1.15  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_xboole_0(A_6, C_8) | ~r1_tarski(A_6, k4_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.78/1.15  tff(c_105, plain, (![A_6]: (r1_xboole_0(A_6, '#skF_5') | ~r1_tarski(A_6, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_8])).
% 1.78/1.15  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.78/1.15  tff(c_26, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.78/1.15  tff(c_143, plain, (![B_44, A_45, C_46]: (r1_tarski(B_44, k3_subset_1(A_45, C_46)) | ~r1_xboole_0(B_44, C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(A_45)) | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.78/1.15  tff(c_20, plain, (~r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.78/1.15  tff(c_146, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_143, c_20])).
% 1.78/1.15  tff(c_149, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_146])).
% 1.78/1.15  tff(c_155, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_105, c_149])).
% 1.78/1.15  tff(c_163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_155])).
% 1.78/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.15  
% 1.78/1.15  Inference rules
% 1.78/1.15  ----------------------
% 1.78/1.15  #Ref     : 0
% 1.78/1.15  #Sup     : 33
% 1.78/1.15  #Fact    : 0
% 1.78/1.15  #Define  : 0
% 1.78/1.15  #Split   : 0
% 1.78/1.15  #Chain   : 0
% 1.78/1.15  #Close   : 0
% 1.78/1.15  
% 1.78/1.15  Ordering : KBO
% 1.78/1.15  
% 1.78/1.15  Simplification rules
% 1.78/1.15  ----------------------
% 1.78/1.15  #Subsume      : 1
% 1.78/1.15  #Demod        : 4
% 1.78/1.15  #Tautology    : 11
% 1.78/1.15  #SimpNegUnit  : 0
% 1.78/1.15  #BackRed      : 0
% 1.78/1.15  
% 1.78/1.15  #Partial instantiations: 0
% 1.78/1.15  #Strategies tried      : 1
% 1.78/1.15  
% 1.78/1.15  Timing (in seconds)
% 1.78/1.15  ----------------------
% 1.78/1.15  Preprocessing        : 0.30
% 1.78/1.15  Parsing              : 0.17
% 1.78/1.15  CNF conversion       : 0.02
% 1.78/1.15  Main loop            : 0.18
% 1.78/1.15  Inferencing          : 0.08
% 1.78/1.15  Reduction            : 0.05
% 1.78/1.15  Demodulation         : 0.03
% 1.78/1.15  BG Simplification    : 0.01
% 1.78/1.16  Subsumption          : 0.03
% 1.78/1.16  Abstraction          : 0.01
% 1.78/1.16  MUC search           : 0.00
% 1.78/1.16  Cooper               : 0.00
% 1.78/1.16  Total                : 0.50
% 1.78/1.16  Index Insertion      : 0.00
% 1.78/1.16  Index Deletion       : 0.00
% 1.78/1.16  Index Matching       : 0.00
% 1.78/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
