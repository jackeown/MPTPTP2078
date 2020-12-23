%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:27 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   32 (  35 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  52 expanded)
%              Number of equality atoms :   10 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_10,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_65,plain,(
    ! [A_25,B_26] :
      ( k4_xboole_0(A_25,B_26) = k3_subset_1(A_25,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_69,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_65])).

tff(c_30,plain,(
    ! [C_18,B_19,A_20] :
      ( r1_tarski(k4_xboole_0(C_18,B_19),k4_xboole_0(C_18,A_20))
      | ~ r1_tarski(A_20,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,(
    ! [A_27,C_28,A_29,B_30] :
      ( r1_tarski(A_27,k4_xboole_0(C_28,A_29))
      | ~ r1_tarski(A_27,k4_xboole_0(C_28,B_30))
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(resolution,[status(thm)],[c_30,c_2])).

tff(c_146,plain,(
    ! [A_36,A_37] :
      ( r1_tarski(A_36,k4_xboole_0('#skF_1',A_37))
      | ~ r1_tarski(A_36,k3_subset_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_37,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_92])).

tff(c_6,plain,(
    ! [A_7,B_8] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k4_xboole_0(B_8,A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_173,plain,(
    ! [A_38] :
      ( k1_xboole_0 = A_38
      | ~ r1_tarski(A_38,k3_subset_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_38,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_146,c_6])).

tff(c_182,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_173])).

tff(c_187,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_182])).

tff(c_189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_187])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:33:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.27  
% 1.94/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.27  %$ r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.94/1.27  
% 1.94/1.27  %Foreground sorts:
% 1.94/1.27  
% 1.94/1.27  
% 1.94/1.27  %Background operators:
% 1.94/1.27  
% 1.94/1.27  
% 1.94/1.27  %Foreground operators:
% 1.94/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.94/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.27  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.94/1.27  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.27  tff('#skF_3', type, '#skF_3': $i).
% 1.94/1.27  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.94/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.94/1.27  
% 1.94/1.28  tff(f_52, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 1.94/1.28  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 1.94/1.28  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_xboole_1)).
% 1.94/1.28  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.94/1.28  tff(f_39, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 1.94/1.28  tff(c_10, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.94/1.28  tff(c_14, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.94/1.28  tff(c_12, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.94/1.28  tff(c_16, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.94/1.28  tff(c_65, plain, (![A_25, B_26]: (k4_xboole_0(A_25, B_26)=k3_subset_1(A_25, B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.94/1.28  tff(c_69, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_16, c_65])).
% 1.94/1.28  tff(c_30, plain, (![C_18, B_19, A_20]: (r1_tarski(k4_xboole_0(C_18, B_19), k4_xboole_0(C_18, A_20)) | ~r1_tarski(A_20, B_19))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.94/1.28  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.94/1.28  tff(c_92, plain, (![A_27, C_28, A_29, B_30]: (r1_tarski(A_27, k4_xboole_0(C_28, A_29)) | ~r1_tarski(A_27, k4_xboole_0(C_28, B_30)) | ~r1_tarski(A_29, B_30))), inference(resolution, [status(thm)], [c_30, c_2])).
% 1.94/1.28  tff(c_146, plain, (![A_36, A_37]: (r1_tarski(A_36, k4_xboole_0('#skF_1', A_37)) | ~r1_tarski(A_36, k3_subset_1('#skF_1', '#skF_3')) | ~r1_tarski(A_37, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_69, c_92])).
% 1.94/1.28  tff(c_6, plain, (![A_7, B_8]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k4_xboole_0(B_8, A_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.94/1.28  tff(c_173, plain, (![A_38]: (k1_xboole_0=A_38 | ~r1_tarski(A_38, k3_subset_1('#skF_1', '#skF_3')) | ~r1_tarski(A_38, '#skF_3'))), inference(resolution, [status(thm)], [c_146, c_6])).
% 1.94/1.28  tff(c_182, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_12, c_173])).
% 1.94/1.28  tff(c_187, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_182])).
% 1.94/1.28  tff(c_189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_187])).
% 1.94/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.28  
% 1.94/1.28  Inference rules
% 1.94/1.28  ----------------------
% 1.94/1.28  #Ref     : 0
% 1.94/1.28  #Sup     : 43
% 1.94/1.28  #Fact    : 0
% 1.94/1.28  #Define  : 0
% 1.94/1.28  #Split   : 3
% 1.94/1.28  #Chain   : 0
% 1.94/1.28  #Close   : 0
% 1.94/1.28  
% 1.94/1.28  Ordering : KBO
% 1.94/1.28  
% 1.94/1.28  Simplification rules
% 1.94/1.28  ----------------------
% 1.94/1.28  #Subsume      : 8
% 1.94/1.28  #Demod        : 5
% 1.94/1.28  #Tautology    : 5
% 1.94/1.28  #SimpNegUnit  : 1
% 1.94/1.28  #BackRed      : 0
% 1.94/1.28  
% 1.94/1.28  #Partial instantiations: 0
% 1.94/1.28  #Strategies tried      : 1
% 1.94/1.28  
% 1.94/1.28  Timing (in seconds)
% 1.94/1.28  ----------------------
% 1.94/1.29  Preprocessing        : 0.27
% 1.94/1.29  Parsing              : 0.14
% 1.94/1.29  CNF conversion       : 0.02
% 1.94/1.29  Main loop            : 0.18
% 1.94/1.29  Inferencing          : 0.07
% 1.94/1.29  Reduction            : 0.05
% 1.94/1.29  Demodulation         : 0.03
% 1.94/1.29  BG Simplification    : 0.01
% 1.94/1.29  Subsumption          : 0.04
% 1.94/1.29  Abstraction          : 0.01
% 1.94/1.29  MUC search           : 0.00
% 1.94/1.29  Cooper               : 0.00
% 1.94/1.29  Total                : 0.47
% 1.94/1.29  Index Insertion      : 0.00
% 1.94/1.29  Index Deletion       : 0.00
% 1.94/1.29  Index Matching       : 0.00
% 1.94/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
