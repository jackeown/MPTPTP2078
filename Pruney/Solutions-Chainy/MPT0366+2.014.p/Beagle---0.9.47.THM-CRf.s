%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:45 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :   44 (  58 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   60 ( 115 expanded)
%              Number of equality atoms :    6 (   9 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_71,negated_conjecture,(
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
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,k3_subset_1(A,C))
          <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).

tff(c_24,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_31,plain,(
    ! [B_20,A_21] :
      ( r1_xboole_0(B_20,A_21)
      | ~ r1_xboole_0(A_21,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_34,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_31])).

tff(c_39,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = A_22
      | ~ r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_46,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_34,c_39])).

tff(c_79,plain,(
    ! [A_31,C_32,B_33] :
      ( r1_xboole_0(A_31,C_32)
      | ~ r1_tarski(A_31,k4_xboole_0(B_33,C_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_82,plain,(
    ! [A_31] :
      ( r1_xboole_0(A_31,'#skF_4')
      | ~ r1_tarski(A_31,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_79])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k3_subset_1(A_8,B_9),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_86,plain,(
    ! [A_34,B_35] :
      ( k3_subset_1(A_34,k3_subset_1(A_34,B_35)) = B_35
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_93,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_26,c_86])).

tff(c_221,plain,(
    ! [B_51,C_52,A_53] :
      ( r1_tarski(B_51,C_52)
      | ~ r1_xboole_0(B_51,k3_subset_1(A_53,C_52))
      | ~ m1_subset_1(C_52,k1_zfmisc_1(A_53))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_246,plain,(
    ! [B_51] :
      ( r1_tarski(B_51,k3_subset_1('#skF_1','#skF_4'))
      | ~ r1_xboole_0(B_51,'#skF_4')
      | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_4'),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(B_51,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_221])).

tff(c_682,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_4'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_246])).

tff(c_685,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_12,c_682])).

tff(c_689,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_685])).

tff(c_787,plain,(
    ! [B_88] :
      ( r1_tarski(B_88,k3_subset_1('#skF_1','#skF_4'))
      | ~ r1_xboole_0(B_88,'#skF_4')
      | ~ m1_subset_1(B_88,k1_zfmisc_1('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_20,plain,(
    ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_790,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_787,c_20])).

tff(c_793,plain,(
    ~ r1_xboole_0('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_790])).

tff(c_802,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_793])).

tff(c_814,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_802])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:57:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.49  
% 3.05/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.49  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.05/1.49  
% 3.05/1.49  %Foreground sorts:
% 3.05/1.49  
% 3.05/1.49  
% 3.05/1.49  %Background operators:
% 3.05/1.49  
% 3.05/1.49  
% 3.05/1.49  %Foreground operators:
% 3.05/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.05/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.05/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.05/1.49  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.05/1.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.05/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.05/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.05/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.05/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.05/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.05/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.05/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.05/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.05/1.49  
% 3.05/1.50  tff(f_71, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_xboole_0(D, C)) => r1_tarski(B, k3_subset_1(A, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_subset_1)).
% 3.05/1.50  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.05/1.50  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.05/1.50  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.05/1.50  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.05/1.50  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.05/1.50  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_subset_1)).
% 3.05/1.50  tff(c_24, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.05/1.50  tff(c_22, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.05/1.50  tff(c_31, plain, (![B_20, A_21]: (r1_xboole_0(B_20, A_21) | ~r1_xboole_0(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.05/1.50  tff(c_34, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_22, c_31])).
% 3.05/1.50  tff(c_39, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=A_22 | ~r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.05/1.50  tff(c_46, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_34, c_39])).
% 3.05/1.50  tff(c_79, plain, (![A_31, C_32, B_33]: (r1_xboole_0(A_31, C_32) | ~r1_tarski(A_31, k4_xboole_0(B_33, C_32)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.05/1.50  tff(c_82, plain, (![A_31]: (r1_xboole_0(A_31, '#skF_4') | ~r1_tarski(A_31, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_79])).
% 3.05/1.50  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.05/1.50  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.05/1.50  tff(c_12, plain, (![A_8, B_9]: (m1_subset_1(k3_subset_1(A_8, B_9), k1_zfmisc_1(A_8)) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.05/1.50  tff(c_86, plain, (![A_34, B_35]: (k3_subset_1(A_34, k3_subset_1(A_34, B_35))=B_35 | ~m1_subset_1(B_35, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.05/1.50  tff(c_93, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_26, c_86])).
% 3.05/1.50  tff(c_221, plain, (![B_51, C_52, A_53]: (r1_tarski(B_51, C_52) | ~r1_xboole_0(B_51, k3_subset_1(A_53, C_52)) | ~m1_subset_1(C_52, k1_zfmisc_1(A_53)) | ~m1_subset_1(B_51, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.05/1.50  tff(c_246, plain, (![B_51]: (r1_tarski(B_51, k3_subset_1('#skF_1', '#skF_4')) | ~r1_xboole_0(B_51, '#skF_4') | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_4'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(B_51, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_93, c_221])).
% 3.05/1.50  tff(c_682, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_4'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_246])).
% 3.05/1.50  tff(c_685, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_682])).
% 3.05/1.50  tff(c_689, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_685])).
% 3.05/1.50  tff(c_787, plain, (![B_88]: (r1_tarski(B_88, k3_subset_1('#skF_1', '#skF_4')) | ~r1_xboole_0(B_88, '#skF_4') | ~m1_subset_1(B_88, k1_zfmisc_1('#skF_1')))), inference(splitRight, [status(thm)], [c_246])).
% 3.05/1.50  tff(c_20, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.05/1.50  tff(c_790, plain, (~r1_xboole_0('#skF_2', '#skF_4') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_787, c_20])).
% 3.05/1.50  tff(c_793, plain, (~r1_xboole_0('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_790])).
% 3.05/1.50  tff(c_802, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_82, c_793])).
% 3.05/1.50  tff(c_814, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_802])).
% 3.05/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.50  
% 3.05/1.50  Inference rules
% 3.05/1.50  ----------------------
% 3.05/1.50  #Ref     : 0
% 3.05/1.50  #Sup     : 187
% 3.05/1.50  #Fact    : 0
% 3.05/1.50  #Define  : 0
% 3.05/1.50  #Split   : 11
% 3.05/1.50  #Chain   : 0
% 3.05/1.50  #Close   : 0
% 3.05/1.50  
% 3.05/1.50  Ordering : KBO
% 3.05/1.50  
% 3.05/1.50  Simplification rules
% 3.05/1.50  ----------------------
% 3.05/1.50  #Subsume      : 13
% 3.05/1.50  #Demod        : 43
% 3.05/1.50  #Tautology    : 52
% 3.05/1.50  #SimpNegUnit  : 10
% 3.05/1.50  #BackRed      : 0
% 3.05/1.50  
% 3.05/1.50  #Partial instantiations: 0
% 3.05/1.50  #Strategies tried      : 1
% 3.05/1.50  
% 3.05/1.50  Timing (in seconds)
% 3.05/1.50  ----------------------
% 3.05/1.50  Preprocessing        : 0.28
% 3.05/1.50  Parsing              : 0.16
% 3.05/1.50  CNF conversion       : 0.02
% 3.05/1.50  Main loop            : 0.40
% 3.05/1.50  Inferencing          : 0.15
% 3.05/1.50  Reduction            : 0.11
% 3.05/1.50  Demodulation         : 0.07
% 3.05/1.50  BG Simplification    : 0.02
% 3.05/1.50  Subsumption          : 0.09
% 3.05/1.50  Abstraction          : 0.02
% 3.05/1.50  MUC search           : 0.00
% 3.05/1.50  Cooper               : 0.00
% 3.05/1.50  Total                : 0.71
% 3.05/1.50  Index Insertion      : 0.00
% 3.05/1.50  Index Deletion       : 0.00
% 3.05/1.50  Index Matching       : 0.00
% 3.05/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
