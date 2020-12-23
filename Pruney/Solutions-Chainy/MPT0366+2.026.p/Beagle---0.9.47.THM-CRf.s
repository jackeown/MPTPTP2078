%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:47 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   36 (  42 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 (  87 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( ( r1_tarski(B,C)
                    & r1_xboole_0(D,C) )
                 => r1_tarski(B,k3_subset_1(A,D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

tff(c_18,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

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

tff(c_16,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_27,plain,(
    ! [A_21,B_22,C_23] :
      ( ~ r1_xboole_0(A_21,B_22)
      | ~ r2_hidden(C_23,B_22)
      | ~ r2_hidden(C_23,A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_31,plain,(
    ! [C_24] :
      ( ~ r2_hidden(C_24,'#skF_4')
      | ~ r2_hidden(C_24,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_27])).

tff(c_49,plain,(
    ! [A_26] :
      ( ~ r2_hidden('#skF_1'(A_26,'#skF_5'),'#skF_4')
      | r1_xboole_0(A_26,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4,c_31])).

tff(c_54,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_49])).

tff(c_58,plain,(
    ! [A_27,C_28,B_29] :
      ( r1_xboole_0(A_27,C_28)
      | ~ r1_xboole_0(B_29,C_28)
      | ~ r1_tarski(A_27,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_63,plain,(
    ! [A_27] :
      ( r1_xboole_0(A_27,'#skF_5')
      | ~ r1_tarski(A_27,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_58])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_20,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_108,plain,(
    ! [B_43,A_44,C_45] :
      ( r1_tarski(B_43,k3_subset_1(A_44,C_45))
      | ~ r1_xboole_0(B_43,C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(A_44))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14,plain,(
    ~ r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_118,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_108,c_14])).

tff(c_124,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_118])).

tff(c_127,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_63,c_124])).

tff(c_131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_127])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:45:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.18  
% 1.87/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.19  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.87/1.19  
% 1.87/1.19  %Foreground sorts:
% 1.87/1.19  
% 1.87/1.19  
% 1.87/1.19  %Background operators:
% 1.87/1.19  
% 1.87/1.19  
% 1.87/1.19  %Foreground operators:
% 1.87/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.19  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.87/1.19  tff('#skF_5', type, '#skF_5': $i).
% 1.87/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.87/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.87/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.87/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.87/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.87/1.19  
% 1.97/1.20  tff(f_73, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_xboole_0(D, C)) => r1_tarski(B, k3_subset_1(A, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_subset_1)).
% 1.97/1.20  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.97/1.20  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.97/1.20  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_subset_1)).
% 1.97/1.20  tff(c_18, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.97/1.20  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.97/1.20  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.97/1.20  tff(c_16, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.97/1.20  tff(c_27, plain, (![A_21, B_22, C_23]: (~r1_xboole_0(A_21, B_22) | ~r2_hidden(C_23, B_22) | ~r2_hidden(C_23, A_21))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.97/1.20  tff(c_31, plain, (![C_24]: (~r2_hidden(C_24, '#skF_4') | ~r2_hidden(C_24, '#skF_5'))), inference(resolution, [status(thm)], [c_16, c_27])).
% 1.97/1.20  tff(c_49, plain, (![A_26]: (~r2_hidden('#skF_1'(A_26, '#skF_5'), '#skF_4') | r1_xboole_0(A_26, '#skF_5'))), inference(resolution, [status(thm)], [c_4, c_31])).
% 1.97/1.20  tff(c_54, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_49])).
% 1.97/1.20  tff(c_58, plain, (![A_27, C_28, B_29]: (r1_xboole_0(A_27, C_28) | ~r1_xboole_0(B_29, C_28) | ~r1_tarski(A_27, B_29))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.97/1.20  tff(c_63, plain, (![A_27]: (r1_xboole_0(A_27, '#skF_5') | ~r1_tarski(A_27, '#skF_4'))), inference(resolution, [status(thm)], [c_54, c_58])).
% 1.97/1.20  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.97/1.20  tff(c_20, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.97/1.20  tff(c_108, plain, (![B_43, A_44, C_45]: (r1_tarski(B_43, k3_subset_1(A_44, C_45)) | ~r1_xboole_0(B_43, C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(A_44)) | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.97/1.20  tff(c_14, plain, (~r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.97/1.20  tff(c_118, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_108, c_14])).
% 1.97/1.20  tff(c_124, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_118])).
% 1.97/1.20  tff(c_127, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_63, c_124])).
% 1.97/1.20  tff(c_131, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_127])).
% 1.97/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.20  
% 1.97/1.20  Inference rules
% 1.97/1.20  ----------------------
% 1.97/1.20  #Ref     : 0
% 1.97/1.20  #Sup     : 23
% 1.97/1.20  #Fact    : 0
% 1.97/1.20  #Define  : 0
% 1.97/1.20  #Split   : 2
% 1.97/1.20  #Chain   : 0
% 1.97/1.20  #Close   : 0
% 1.97/1.20  
% 1.97/1.20  Ordering : KBO
% 1.97/1.20  
% 1.97/1.20  Simplification rules
% 1.97/1.20  ----------------------
% 1.97/1.20  #Subsume      : 1
% 1.97/1.20  #Demod        : 4
% 1.97/1.20  #Tautology    : 2
% 1.97/1.20  #SimpNegUnit  : 0
% 1.97/1.20  #BackRed      : 0
% 1.97/1.20  
% 1.97/1.20  #Partial instantiations: 0
% 1.97/1.20  #Strategies tried      : 1
% 1.97/1.20  
% 1.97/1.20  Timing (in seconds)
% 1.97/1.20  ----------------------
% 1.97/1.20  Preprocessing        : 0.27
% 1.97/1.20  Parsing              : 0.16
% 1.97/1.20  CNF conversion       : 0.02
% 1.97/1.20  Main loop            : 0.16
% 1.97/1.20  Inferencing          : 0.07
% 1.97/1.20  Reduction            : 0.04
% 1.97/1.20  Demodulation         : 0.03
% 1.97/1.20  BG Simplification    : 0.01
% 1.97/1.20  Subsumption          : 0.04
% 1.97/1.20  Abstraction          : 0.01
% 1.97/1.20  MUC search           : 0.00
% 1.97/1.20  Cooper               : 0.00
% 1.97/1.20  Total                : 0.47
% 1.97/1.20  Index Insertion      : 0.00
% 1.97/1.20  Index Deletion       : 0.00
% 1.97/1.20  Index Matching       : 0.00
% 1.97/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
