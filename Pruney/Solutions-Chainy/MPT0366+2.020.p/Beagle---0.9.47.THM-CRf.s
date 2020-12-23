%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:46 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   34 (  38 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   42 (  66 expanded)
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

tff(f_63,negated_conjecture,(
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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

tff(c_20,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_18,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_27,plain,(
    ! [B_16,A_17] :
      ( r1_xboole_0(B_16,A_17)
      | ~ r1_xboole_0(A_17,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_27])).

tff(c_35,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = A_18
      | ~ r1_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_42,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_35])).

tff(c_75,plain,(
    ! [A_27,C_28,B_29] :
      ( r1_xboole_0(A_27,C_28)
      | ~ r1_tarski(A_27,k4_xboole_0(B_29,C_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_78,plain,(
    ! [A_27] :
      ( r1_xboole_0(A_27,'#skF_4')
      | ~ r1_tarski(A_27,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_75])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_147,plain,(
    ! [B_41,A_42,C_43] :
      ( r1_tarski(B_41,k3_subset_1(A_42,C_43))
      | ~ r1_xboole_0(B_41,C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(A_42))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_153,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_147,c_16])).

tff(c_157,plain,(
    ~ r1_xboole_0('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_153])).

tff(c_163,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_157])).

tff(c_174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_163])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:40:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.20  
% 1.84/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.20  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.84/1.20  
% 1.84/1.20  %Foreground sorts:
% 1.84/1.20  
% 1.84/1.20  
% 1.84/1.20  %Background operators:
% 1.84/1.20  
% 1.84/1.20  
% 1.84/1.20  %Foreground operators:
% 1.84/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.84/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.84/1.20  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.84/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.84/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.84/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.84/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.84/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.84/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.84/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.84/1.20  
% 1.84/1.21  tff(f_63, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_xboole_0(D, C)) => r1_tarski(B, k3_subset_1(A, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_subset_1)).
% 1.84/1.21  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.84/1.21  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.84/1.21  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 1.84/1.21  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 1.84/1.21  tff(c_20, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.84/1.21  tff(c_18, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.84/1.21  tff(c_27, plain, (![B_16, A_17]: (r1_xboole_0(B_16, A_17) | ~r1_xboole_0(A_17, B_16))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.84/1.21  tff(c_30, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_18, c_27])).
% 1.84/1.21  tff(c_35, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=A_18 | ~r1_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.84/1.21  tff(c_42, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_30, c_35])).
% 1.84/1.21  tff(c_75, plain, (![A_27, C_28, B_29]: (r1_xboole_0(A_27, C_28) | ~r1_tarski(A_27, k4_xboole_0(B_29, C_28)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.84/1.21  tff(c_78, plain, (![A_27]: (r1_xboole_0(A_27, '#skF_4') | ~r1_tarski(A_27, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_75])).
% 1.84/1.21  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.84/1.21  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.84/1.21  tff(c_147, plain, (![B_41, A_42, C_43]: (r1_tarski(B_41, k3_subset_1(A_42, C_43)) | ~r1_xboole_0(B_41, C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(A_42)) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.84/1.21  tff(c_16, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.84/1.21  tff(c_153, plain, (~r1_xboole_0('#skF_2', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_147, c_16])).
% 1.84/1.21  tff(c_157, plain, (~r1_xboole_0('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_153])).
% 1.84/1.21  tff(c_163, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_78, c_157])).
% 1.84/1.21  tff(c_174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_163])).
% 1.84/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.21  
% 1.84/1.21  Inference rules
% 1.84/1.21  ----------------------
% 1.84/1.21  #Ref     : 0
% 1.84/1.21  #Sup     : 39
% 1.84/1.21  #Fact    : 0
% 1.84/1.21  #Define  : 0
% 1.84/1.21  #Split   : 0
% 1.84/1.21  #Chain   : 0
% 1.84/1.21  #Close   : 0
% 1.84/1.21  
% 1.84/1.21  Ordering : KBO
% 1.84/1.21  
% 1.84/1.21  Simplification rules
% 1.84/1.21  ----------------------
% 1.84/1.21  #Subsume      : 4
% 1.84/1.21  #Demod        : 4
% 1.84/1.21  #Tautology    : 12
% 1.84/1.21  #SimpNegUnit  : 0
% 1.84/1.21  #BackRed      : 0
% 1.84/1.21  
% 1.84/1.21  #Partial instantiations: 0
% 1.84/1.21  #Strategies tried      : 1
% 1.84/1.21  
% 1.84/1.21  Timing (in seconds)
% 1.84/1.21  ----------------------
% 1.84/1.22  Preprocessing        : 0.28
% 1.84/1.22  Parsing              : 0.15
% 1.84/1.22  CNF conversion       : 0.02
% 1.84/1.22  Main loop            : 0.17
% 1.84/1.22  Inferencing          : 0.07
% 1.84/1.22  Reduction            : 0.04
% 1.84/1.22  Demodulation         : 0.03
% 1.84/1.22  BG Simplification    : 0.01
% 1.84/1.22  Subsumption          : 0.03
% 1.84/1.22  Abstraction          : 0.01
% 1.84/1.22  MUC search           : 0.00
% 1.84/1.22  Cooper               : 0.00
% 1.84/1.22  Total                : 0.47
% 1.84/1.22  Index Insertion      : 0.00
% 1.84/1.22  Index Deletion       : 0.00
% 1.84/1.22  Index Matching       : 0.00
% 1.84/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
