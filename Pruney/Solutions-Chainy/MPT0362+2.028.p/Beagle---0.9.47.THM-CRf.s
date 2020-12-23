%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:36 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   34 (  43 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   36 (  55 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_16,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_56,plain,(
    ! [A_24,B_25,C_26] :
      ( k9_subset_1(A_24,B_25,C_26) = k3_xboole_0(B_25,C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(A_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_61,plain,(
    ! [B_25] : k9_subset_1('#skF_1',B_25,'#skF_3') = k3_xboole_0(B_25,'#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_56])).

tff(c_82,plain,(
    ! [A_29,B_30,C_31] :
      ( m1_subset_1(k9_subset_1(A_29,B_30,C_31),k1_zfmisc_1(A_29))
      | ~ m1_subset_1(C_31,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_90,plain,(
    ! [B_25] :
      ( m1_subset_1(k3_xboole_0(B_25,'#skF_3'),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_82])).

tff(c_95,plain,(
    ! [B_25] : m1_subset_1(k3_xboole_0(B_25,'#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_90])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_20,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_29,plain,(
    ! [A_18,B_19] : r1_tarski(k3_xboole_0(A_18,B_19),A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2])).

tff(c_225,plain,(
    ! [A_55,C_56,B_57] :
      ( r1_tarski(k3_subset_1(A_55,C_56),k3_subset_1(A_55,B_57))
      | ~ r1_tarski(B_57,C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(A_55))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_14,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1',k9_subset_1('#skF_1','#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_63,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1',k3_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_14])).

tff(c_231,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_225,c_63])).

tff(c_236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_18,c_29,c_231])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:34:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.20  
% 1.98/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.20  %$ r1_tarski > m1_subset_1 > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.98/1.20  
% 1.98/1.20  %Foreground sorts:
% 1.98/1.20  
% 1.98/1.20  
% 1.98/1.20  %Background operators:
% 1.98/1.20  
% 1.98/1.20  
% 1.98/1.20  %Foreground operators:
% 1.98/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.98/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.98/1.20  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.98/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.98/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.98/1.20  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 1.98/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.20  
% 1.98/1.21  tff(f_54, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_subset_1)).
% 1.98/1.21  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 1.98/1.21  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 1.98/1.21  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.98/1.21  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.98/1.21  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 1.98/1.21  tff(c_16, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.98/1.21  tff(c_56, plain, (![A_24, B_25, C_26]: (k9_subset_1(A_24, B_25, C_26)=k3_xboole_0(B_25, C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.98/1.21  tff(c_61, plain, (![B_25]: (k9_subset_1('#skF_1', B_25, '#skF_3')=k3_xboole_0(B_25, '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_56])).
% 1.98/1.21  tff(c_82, plain, (![A_29, B_30, C_31]: (m1_subset_1(k9_subset_1(A_29, B_30, C_31), k1_zfmisc_1(A_29)) | ~m1_subset_1(C_31, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.98/1.21  tff(c_90, plain, (![B_25]: (m1_subset_1(k3_xboole_0(B_25, '#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_61, c_82])).
% 1.98/1.21  tff(c_95, plain, (![B_25]: (m1_subset_1(k3_xboole_0(B_25, '#skF_3'), k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_90])).
% 1.98/1.21  tff(c_18, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.98/1.21  tff(c_20, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.98/1.21  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.98/1.21  tff(c_29, plain, (![A_18, B_19]: (r1_tarski(k3_xboole_0(A_18, B_19), A_18))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2])).
% 1.98/1.21  tff(c_225, plain, (![A_55, C_56, B_57]: (r1_tarski(k3_subset_1(A_55, C_56), k3_subset_1(A_55, B_57)) | ~r1_tarski(B_57, C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(A_55)) | ~m1_subset_1(B_57, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.98/1.21  tff(c_14, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', k9_subset_1('#skF_1', '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.98/1.21  tff(c_63, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_14])).
% 1.98/1.21  tff(c_231, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_225, c_63])).
% 1.98/1.21  tff(c_236, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95, c_18, c_29, c_231])).
% 1.98/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.21  
% 1.98/1.21  Inference rules
% 1.98/1.21  ----------------------
% 1.98/1.21  #Ref     : 0
% 1.98/1.21  #Sup     : 51
% 1.98/1.21  #Fact    : 0
% 1.98/1.21  #Define  : 0
% 1.98/1.21  #Split   : 0
% 1.98/1.21  #Chain   : 0
% 1.98/1.21  #Close   : 0
% 1.98/1.21  
% 1.98/1.21  Ordering : KBO
% 1.98/1.21  
% 1.98/1.21  Simplification rules
% 1.98/1.21  ----------------------
% 1.98/1.21  #Subsume      : 0
% 1.98/1.21  #Demod        : 18
% 1.98/1.21  #Tautology    : 28
% 1.98/1.21  #SimpNegUnit  : 0
% 1.98/1.21  #BackRed      : 1
% 1.98/1.21  
% 1.98/1.21  #Partial instantiations: 0
% 1.98/1.21  #Strategies tried      : 1
% 1.98/1.21  
% 1.98/1.21  Timing (in seconds)
% 1.98/1.21  ----------------------
% 1.98/1.21  Preprocessing        : 0.28
% 1.98/1.21  Parsing              : 0.15
% 1.98/1.21  CNF conversion       : 0.02
% 1.98/1.21  Main loop            : 0.17
% 1.98/1.21  Inferencing          : 0.07
% 1.98/1.21  Reduction            : 0.05
% 1.98/1.21  Demodulation         : 0.04
% 1.98/1.21  BG Simplification    : 0.01
% 1.98/1.21  Subsumption          : 0.02
% 1.98/1.21  Abstraction          : 0.01
% 1.98/1.21  MUC search           : 0.00
% 1.98/1.21  Cooper               : 0.00
% 1.98/1.21  Total                : 0.47
% 1.98/1.21  Index Insertion      : 0.00
% 1.98/1.21  Index Deletion       : 0.00
% 1.98/1.21  Index Matching       : 0.00
% 1.98/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
