%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:47 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   31 (  35 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   36 (  60 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_57,negated_conjecture,(
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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

tff(c_16,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = A_16
      | ~ r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_14,c_24])).

tff(c_37,plain,(
    ! [A_18,C_19,B_20] :
      ( r1_xboole_0(A_18,k4_xboole_0(C_19,B_20))
      | ~ r1_tarski(A_18,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_43,plain,(
    ! [A_18] :
      ( r1_xboole_0(A_18,'#skF_4')
      | ~ r1_tarski(A_18,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_37])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_68,plain,(
    ! [B_25,A_26,C_27] :
      ( r1_tarski(B_25,k3_subset_1(A_26,C_27))
      | ~ r1_xboole_0(B_25,C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(A_26))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12,plain,(
    ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_71,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_68,c_12])).

tff(c_74,plain,(
    ~ r1_xboole_0('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_71])).

tff(c_77,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_43,c_74])).

tff(c_84,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_77])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:23:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.15  
% 1.70/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.15  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.70/1.15  
% 1.70/1.15  %Foreground sorts:
% 1.70/1.15  
% 1.70/1.15  
% 1.70/1.15  %Background operators:
% 1.70/1.15  
% 1.70/1.15  
% 1.70/1.15  %Foreground operators:
% 1.70/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.70/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.70/1.15  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.70/1.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.70/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.70/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.70/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.70/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.70/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.70/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.70/1.15  
% 1.70/1.16  tff(f_57, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_xboole_0(D, C)) => r1_tarski(B, k3_subset_1(A, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_subset_1)).
% 1.70/1.16  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.70/1.16  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 1.70/1.16  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_subset_1)).
% 1.70/1.16  tff(c_16, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.70/1.16  tff(c_14, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.70/1.16  tff(c_24, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=A_16 | ~r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.70/1.16  tff(c_32, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_14, c_24])).
% 1.70/1.16  tff(c_37, plain, (![A_18, C_19, B_20]: (r1_xboole_0(A_18, k4_xboole_0(C_19, B_20)) | ~r1_tarski(A_18, B_20))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.70/1.16  tff(c_43, plain, (![A_18]: (r1_xboole_0(A_18, '#skF_4') | ~r1_tarski(A_18, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_37])).
% 1.70/1.16  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.70/1.16  tff(c_18, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.70/1.16  tff(c_68, plain, (![B_25, A_26, C_27]: (r1_tarski(B_25, k3_subset_1(A_26, C_27)) | ~r1_xboole_0(B_25, C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(A_26)) | ~m1_subset_1(B_25, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.70/1.16  tff(c_12, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.70/1.16  tff(c_71, plain, (~r1_xboole_0('#skF_2', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_12])).
% 1.70/1.16  tff(c_74, plain, (~r1_xboole_0('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_71])).
% 1.70/1.16  tff(c_77, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_43, c_74])).
% 1.70/1.16  tff(c_84, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_77])).
% 1.70/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.16  
% 1.70/1.16  Inference rules
% 1.70/1.16  ----------------------
% 1.70/1.16  #Ref     : 0
% 1.70/1.16  #Sup     : 15
% 1.70/1.16  #Fact    : 0
% 1.70/1.16  #Define  : 0
% 1.70/1.16  #Split   : 0
% 1.70/1.16  #Chain   : 0
% 1.70/1.16  #Close   : 0
% 1.70/1.16  
% 1.70/1.16  Ordering : KBO
% 1.70/1.16  
% 1.70/1.16  Simplification rules
% 1.70/1.16  ----------------------
% 1.70/1.16  #Subsume      : 0
% 1.70/1.16  #Demod        : 3
% 1.70/1.16  #Tautology    : 5
% 1.70/1.16  #SimpNegUnit  : 0
% 1.70/1.16  #BackRed      : 0
% 1.70/1.16  
% 1.70/1.16  #Partial instantiations: 0
% 1.70/1.16  #Strategies tried      : 1
% 1.70/1.16  
% 1.70/1.16  Timing (in seconds)
% 1.70/1.16  ----------------------
% 1.70/1.16  Preprocessing        : 0.27
% 1.70/1.16  Parsing              : 0.15
% 1.70/1.16  CNF conversion       : 0.02
% 1.70/1.16  Main loop            : 0.12
% 1.70/1.16  Inferencing          : 0.05
% 1.70/1.16  Reduction            : 0.03
% 1.70/1.16  Demodulation         : 0.02
% 1.70/1.16  BG Simplification    : 0.01
% 1.70/1.16  Subsumption          : 0.02
% 1.70/1.16  Abstraction          : 0.00
% 1.70/1.16  MUC search           : 0.00
% 1.70/1.16  Cooper               : 0.00
% 1.70/1.16  Total                : 0.41
% 1.70/1.16  Index Insertion      : 0.00
% 1.70/1.16  Index Deletion       : 0.00
% 1.70/1.16  Index Matching       : 0.00
% 1.70/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
