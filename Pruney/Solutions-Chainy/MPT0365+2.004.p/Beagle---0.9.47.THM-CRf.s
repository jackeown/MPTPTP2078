%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:42 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   47 (  98 expanded)
%              Number of leaves         :   17 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   66 ( 224 expanded)
%              Number of equality atoms :   10 (  33 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ( r1_xboole_0(B,C)
                & r1_xboole_0(k3_subset_1(A,B),k3_subset_1(A,C)) )
             => B = k3_subset_1(A,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,k3_subset_1(A,C))
          <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_18,plain,(
    k3_subset_1('#skF_1','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_29,plain,(
    ! [B_15,A_16] :
      ( r1_xboole_0(B_15,A_16)
      | ~ r1_xboole_0(A_16,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_29])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k3_subset_1(A_5,B_6),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    r1_xboole_0(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_126,plain,(
    ! [B_25,C_26,A_27] :
      ( r1_tarski(B_25,C_26)
      | ~ r1_xboole_0(B_25,k3_subset_1(A_27,C_26))
      | ~ m1_subset_1(C_26,k1_zfmisc_1(A_27))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_141,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_20,c_126])).

tff(c_147,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_3')
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_141])).

tff(c_148,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_151,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_148])).

tff(c_155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_151])).

tff(c_157,plain,(
    m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_52,plain,(
    ! [A_21,B_22] :
      ( k3_subset_1(A_21,k3_subset_1(A_21,B_22)) = B_22
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_60,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_52])).

tff(c_135,plain,(
    ! [B_25] :
      ( r1_tarski(B_25,k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_xboole_0(B_25,'#skF_2')
      | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(B_25,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_126])).

tff(c_161,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_161])).

tff(c_293,plain,(
    ! [B_36] :
      ( r1_tarski(B_36,k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_xboole_0(B_36,'#skF_2')
      | ~ m1_subset_1(B_36,k1_zfmisc_1('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_156,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_160,plain,
    ( k3_subset_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_156,c_4])).

tff(c_175,plain,(
    ~ r1_tarski('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_299,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_293,c_175])).

tff(c_306,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_32,c_299])).

tff(c_307,plain,(
    k3_subset_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_311,plain,(
    k3_subset_1('#skF_1','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_60])).

tff(c_317,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_311])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:01:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.36  
% 2.17/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.36  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.17/1.36  
% 2.17/1.36  %Foreground sorts:
% 2.17/1.36  
% 2.17/1.36  
% 2.17/1.36  %Background operators:
% 2.17/1.36  
% 2.17/1.36  
% 2.17/1.36  %Foreground operators:
% 2.17/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.36  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.17/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.17/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.36  
% 2.17/1.37  tff(f_64, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_xboole_0(B, C) & r1_xboole_0(k3_subset_1(A, B), k3_subset_1(A, C))) => (B = k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_subset_1)).
% 2.17/1.37  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.17/1.37  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.17/1.37  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_subset_1)).
% 2.17/1.37  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.17/1.37  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.17/1.37  tff(c_18, plain, (k3_subset_1('#skF_1', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.17/1.37  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.17/1.37  tff(c_22, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.17/1.37  tff(c_29, plain, (![B_15, A_16]: (r1_xboole_0(B_15, A_16) | ~r1_xboole_0(A_16, B_15))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.17/1.37  tff(c_32, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_29])).
% 2.17/1.37  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.17/1.37  tff(c_10, plain, (![A_5, B_6]: (m1_subset_1(k3_subset_1(A_5, B_6), k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.17/1.37  tff(c_20, plain, (r1_xboole_0(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.17/1.37  tff(c_126, plain, (![B_25, C_26, A_27]: (r1_tarski(B_25, C_26) | ~r1_xboole_0(B_25, k3_subset_1(A_27, C_26)) | ~m1_subset_1(C_26, k1_zfmisc_1(A_27)) | ~m1_subset_1(B_25, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.17/1.37  tff(c_141, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_126])).
% 2.17/1.37  tff(c_147, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_3') | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_141])).
% 2.17/1.37  tff(c_148, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_147])).
% 2.17/1.37  tff(c_151, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_148])).
% 2.17/1.37  tff(c_155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_151])).
% 2.17/1.37  tff(c_157, plain, (m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_147])).
% 2.17/1.37  tff(c_52, plain, (![A_21, B_22]: (k3_subset_1(A_21, k3_subset_1(A_21, B_22))=B_22 | ~m1_subset_1(B_22, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.17/1.37  tff(c_60, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_26, c_52])).
% 2.17/1.37  tff(c_135, plain, (![B_25]: (r1_tarski(B_25, k3_subset_1('#skF_1', '#skF_2')) | ~r1_xboole_0(B_25, '#skF_2') | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(B_25, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_60, c_126])).
% 2.17/1.37  tff(c_161, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_135])).
% 2.17/1.37  tff(c_167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_157, c_161])).
% 2.17/1.37  tff(c_293, plain, (![B_36]: (r1_tarski(B_36, k3_subset_1('#skF_1', '#skF_2')) | ~r1_xboole_0(B_36, '#skF_2') | ~m1_subset_1(B_36, k1_zfmisc_1('#skF_1')))), inference(splitRight, [status(thm)], [c_135])).
% 2.17/1.37  tff(c_156, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_147])).
% 2.17/1.37  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.17/1.37  tff(c_160, plain, (k3_subset_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski('#skF_3', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_156, c_4])).
% 2.17/1.37  tff(c_175, plain, (~r1_tarski('#skF_3', k3_subset_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_160])).
% 2.17/1.37  tff(c_299, plain, (~r1_xboole_0('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_293, c_175])).
% 2.17/1.37  tff(c_306, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_32, c_299])).
% 2.17/1.37  tff(c_307, plain, (k3_subset_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_160])).
% 2.17/1.37  tff(c_311, plain, (k3_subset_1('#skF_1', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_307, c_60])).
% 2.17/1.37  tff(c_317, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_311])).
% 2.17/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.37  
% 2.17/1.37  Inference rules
% 2.17/1.37  ----------------------
% 2.17/1.37  #Ref     : 0
% 2.17/1.37  #Sup     : 60
% 2.17/1.37  #Fact    : 0
% 2.17/1.37  #Define  : 0
% 2.17/1.37  #Split   : 5
% 2.17/1.37  #Chain   : 0
% 2.17/1.37  #Close   : 0
% 2.17/1.37  
% 2.17/1.37  Ordering : KBO
% 2.17/1.37  
% 2.17/1.37  Simplification rules
% 2.17/1.37  ----------------------
% 2.17/1.37  #Subsume      : 3
% 2.17/1.37  #Demod        : 44
% 2.17/1.37  #Tautology    : 33
% 2.17/1.37  #SimpNegUnit  : 3
% 2.17/1.37  #BackRed      : 5
% 2.17/1.37  
% 2.17/1.37  #Partial instantiations: 0
% 2.17/1.37  #Strategies tried      : 1
% 2.17/1.37  
% 2.17/1.37  Timing (in seconds)
% 2.17/1.37  ----------------------
% 2.17/1.37  Preprocessing        : 0.30
% 2.17/1.37  Parsing              : 0.17
% 2.17/1.38  CNF conversion       : 0.02
% 2.17/1.38  Main loop            : 0.24
% 2.17/1.38  Inferencing          : 0.09
% 2.17/1.38  Reduction            : 0.07
% 2.17/1.38  Demodulation         : 0.05
% 2.17/1.38  BG Simplification    : 0.01
% 2.17/1.38  Subsumption          : 0.06
% 2.17/1.38  Abstraction          : 0.01
% 2.17/1.38  MUC search           : 0.00
% 2.17/1.38  Cooper               : 0.00
% 2.17/1.38  Total                : 0.58
% 2.17/1.38  Index Insertion      : 0.00
% 2.17/1.38  Index Deletion       : 0.00
% 2.17/1.38  Index Matching       : 0.00
% 2.17/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
