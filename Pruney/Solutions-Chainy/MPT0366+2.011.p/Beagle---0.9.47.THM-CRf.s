%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:45 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   43 (  48 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   49 (  75 expanded)
%              Number of equality atoms :   15 (  16 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_65,negated_conjecture,(
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

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_293,plain,(
    ! [B_41,A_42,C_43] :
      ( r1_tarski(B_41,k3_subset_1(A_42,C_43))
      | ~ r1_xboole_0(B_41,C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(A_42))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_18,plain,(
    ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_299,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_293,c_18])).

tff(c_303,plain,(
    ~ r1_xboole_0('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_299])).

tff(c_311,plain,(
    k3_xboole_0('#skF_2','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_303])).

tff(c_12,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_36,plain,(
    ! [B_20,A_21] :
      ( r1_xboole_0(B_20,A_21)
      | ~ r1_xboole_0(A_21,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_39,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_36])).

tff(c_44,plain,(
    ! [A_22,B_23] :
      ( k3_xboole_0(A_22,B_23) = k1_xboole_0
      | ~ r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_51,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_39,c_44])).

tff(c_22,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_61,plain,(
    ! [A_24,B_25] :
      ( k3_xboole_0(A_24,B_25) = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_65,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_22,c_61])).

tff(c_78,plain,(
    ! [A_28,B_29,C_30] : k3_xboole_0(k3_xboole_0(A_28,B_29),C_30) = k3_xboole_0(A_28,k3_xboole_0(B_29,C_30)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_312,plain,(
    ! [C_44] : k3_xboole_0('#skF_2',k3_xboole_0('#skF_3',C_44)) = k3_xboole_0('#skF_2',C_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_78])).

tff(c_329,plain,(
    k3_xboole_0('#skF_2',k1_xboole_0) = k3_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_312])).

tff(c_339,plain,(
    k3_xboole_0('#skF_2','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_329])).

tff(c_341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_311,c_339])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:06:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.27  
% 2.08/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.27  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.08/1.27  
% 2.08/1.27  %Foreground sorts:
% 2.08/1.27  
% 2.08/1.27  
% 2.08/1.27  %Background operators:
% 2.08/1.27  
% 2.08/1.27  
% 2.08/1.27  %Foreground operators:
% 2.08/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.27  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.08/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.08/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.08/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.08/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.08/1.28  
% 2.08/1.29  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.08/1.29  tff(f_65, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_xboole_0(D, C)) => r1_tarski(B, k3_subset_1(A, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_subset_1)).
% 2.08/1.29  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_subset_1)).
% 2.08/1.29  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.08/1.29  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.08/1.29  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.08/1.29  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 2.08/1.29  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.08/1.29  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.08/1.29  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.08/1.29  tff(c_293, plain, (![B_41, A_42, C_43]: (r1_tarski(B_41, k3_subset_1(A_42, C_43)) | ~r1_xboole_0(B_41, C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(A_42)) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.08/1.29  tff(c_18, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.08/1.29  tff(c_299, plain, (~r1_xboole_0('#skF_2', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_293, c_18])).
% 2.08/1.29  tff(c_303, plain, (~r1_xboole_0('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_299])).
% 2.08/1.29  tff(c_311, plain, (k3_xboole_0('#skF_2', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_303])).
% 2.08/1.29  tff(c_12, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.08/1.29  tff(c_20, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.08/1.29  tff(c_36, plain, (![B_20, A_21]: (r1_xboole_0(B_20, A_21) | ~r1_xboole_0(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.08/1.29  tff(c_39, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_20, c_36])).
% 2.08/1.29  tff(c_44, plain, (![A_22, B_23]: (k3_xboole_0(A_22, B_23)=k1_xboole_0 | ~r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.08/1.29  tff(c_51, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_39, c_44])).
% 2.08/1.29  tff(c_22, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.08/1.29  tff(c_61, plain, (![A_24, B_25]: (k3_xboole_0(A_24, B_25)=A_24 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.08/1.29  tff(c_65, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_22, c_61])).
% 2.08/1.29  tff(c_78, plain, (![A_28, B_29, C_30]: (k3_xboole_0(k3_xboole_0(A_28, B_29), C_30)=k3_xboole_0(A_28, k3_xboole_0(B_29, C_30)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.08/1.29  tff(c_312, plain, (![C_44]: (k3_xboole_0('#skF_2', k3_xboole_0('#skF_3', C_44))=k3_xboole_0('#skF_2', C_44))), inference(superposition, [status(thm), theory('equality')], [c_65, c_78])).
% 2.08/1.29  tff(c_329, plain, (k3_xboole_0('#skF_2', k1_xboole_0)=k3_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_51, c_312])).
% 2.08/1.29  tff(c_339, plain, (k3_xboole_0('#skF_2', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_329])).
% 2.08/1.29  tff(c_341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_311, c_339])).
% 2.08/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.29  
% 2.08/1.29  Inference rules
% 2.08/1.29  ----------------------
% 2.08/1.29  #Ref     : 0
% 2.08/1.29  #Sup     : 82
% 2.08/1.29  #Fact    : 0
% 2.08/1.29  #Define  : 0
% 2.08/1.29  #Split   : 1
% 2.08/1.29  #Chain   : 0
% 2.08/1.29  #Close   : 0
% 2.08/1.29  
% 2.08/1.29  Ordering : KBO
% 2.08/1.29  
% 2.08/1.29  Simplification rules
% 2.08/1.29  ----------------------
% 2.08/1.29  #Subsume      : 1
% 2.08/1.29  #Demod        : 58
% 2.08/1.29  #Tautology    : 53
% 2.08/1.29  #SimpNegUnit  : 1
% 2.08/1.29  #BackRed      : 1
% 2.08/1.29  
% 2.08/1.29  #Partial instantiations: 0
% 2.08/1.29  #Strategies tried      : 1
% 2.08/1.29  
% 2.08/1.29  Timing (in seconds)
% 2.08/1.29  ----------------------
% 2.08/1.29  Preprocessing        : 0.29
% 2.08/1.29  Parsing              : 0.16
% 2.08/1.29  CNF conversion       : 0.02
% 2.08/1.29  Main loop            : 0.24
% 2.08/1.29  Inferencing          : 0.09
% 2.08/1.29  Reduction            : 0.08
% 2.08/1.29  Demodulation         : 0.06
% 2.08/1.29  BG Simplification    : 0.01
% 2.08/1.29  Subsumption          : 0.04
% 2.08/1.29  Abstraction          : 0.01
% 2.08/1.29  MUC search           : 0.00
% 2.08/1.29  Cooper               : 0.00
% 2.08/1.29  Total                : 0.55
% 2.08/1.29  Index Insertion      : 0.00
% 2.08/1.29  Index Deletion       : 0.00
% 2.08/1.29  Index Matching       : 0.00
% 2.08/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
