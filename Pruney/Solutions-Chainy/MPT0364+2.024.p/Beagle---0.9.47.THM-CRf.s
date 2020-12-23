%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:42 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   48 (  92 expanded)
%              Number of leaves         :   15 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :   74 ( 193 expanded)
%              Number of equality atoms :    5 (  15 expanded)
%              Maximal formula depth    :    8 (   3 average)
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

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,k3_subset_1(A,C))
            <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

tff(c_12,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,
    ( ~ r1_tarski('#skF_2','#skF_3')
    | ~ r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_21,plain,(
    ~ r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_20,plain,
    ( r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3'))
    | r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_22,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_21,c_20])).

tff(c_10,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k3_subset_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_23,plain,(
    ! [A_10,B_11] :
      ( k3_subset_1(A_10,k3_subset_1(A_10,B_11)) = B_11
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_10,c_23])).

tff(c_50,plain,(
    ! [B_14,A_15,C_16] :
      ( r1_tarski(B_14,k3_subset_1(A_15,C_16))
      | ~ r1_xboole_0(B_14,C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(A_15))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_56,plain,(
    ! [B_14] :
      ( r1_tarski(B_14,'#skF_3')
      | ~ r1_xboole_0(B_14,k3_subset_1('#skF_1','#skF_3'))
      | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(B_14,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_50])).

tff(c_122,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_125,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2,c_122])).

tff(c_129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_125])).

tff(c_131,plain,(
    m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_108,plain,(
    ! [B_19,C_20,A_21] :
      ( r1_xboole_0(B_19,C_20)
      | ~ r1_tarski(B_19,k3_subset_1(A_21,C_20))
      | ~ m1_subset_1(C_20,k1_zfmisc_1(A_21))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_120,plain,(
    ! [B_19] :
      ( r1_xboole_0(B_19,k3_subset_1('#skF_1','#skF_3'))
      | ~ r1_tarski(B_19,'#skF_3')
      | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(B_19,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_108])).

tff(c_139,plain,(
    ! [B_23] :
      ( r1_xboole_0(B_23,k3_subset_1('#skF_1','#skF_3'))
      | ~ r1_tarski(B_23,'#skF_3')
      | ~ m1_subset_1(B_23,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_120])).

tff(c_145,plain,
    ( ~ r1_tarski('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_139,c_21])).

tff(c_150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_22,c_145])).

tff(c_151,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_152,plain,(
    r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_156,plain,(
    ! [A_26,B_27] :
      ( k3_subset_1(A_26,k3_subset_1(A_26,B_27)) = B_27
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_164,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_10,c_156])).

tff(c_230,plain,(
    ! [B_30,A_31,C_32] :
      ( r1_tarski(B_30,k3_subset_1(A_31,C_32))
      | ~ r1_xboole_0(B_30,C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(A_31))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_239,plain,(
    ! [B_30] :
      ( r1_tarski(B_30,'#skF_3')
      | ~ r1_xboole_0(B_30,k3_subset_1('#skF_1','#skF_3'))
      | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(B_30,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_230])).

tff(c_254,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_239])).

tff(c_257,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2,c_254])).

tff(c_261,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_257])).

tff(c_287,plain,(
    ! [B_37] :
      ( r1_tarski(B_37,'#skF_3')
      | ~ r1_xboole_0(B_37,k3_subset_1('#skF_1','#skF_3'))
      | ~ m1_subset_1(B_37,k1_zfmisc_1('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_290,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_152,c_287])).

tff(c_293,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_290])).

tff(c_295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_293])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:10:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.29  
% 1.99/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.29  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.99/1.29  
% 1.99/1.29  %Foreground sorts:
% 1.99/1.29  
% 1.99/1.29  
% 1.99/1.29  %Background operators:
% 1.99/1.29  
% 1.99/1.29  
% 1.99/1.29  %Foreground operators:
% 1.99/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.99/1.29  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.99/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.99/1.29  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.29  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.29  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.99/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.99/1.29  
% 2.17/1.30  tff(f_52, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_subset_1)).
% 2.17/1.30  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.17/1.30  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.17/1.30  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_subset_1)).
% 2.17/1.30  tff(c_12, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.17/1.30  tff(c_14, plain, (~r1_tarski('#skF_2', '#skF_3') | ~r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.17/1.30  tff(c_21, plain, (~r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_14])).
% 2.17/1.30  tff(c_20, plain, (r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3')) | r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.17/1.30  tff(c_22, plain, (r1_tarski('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_21, c_20])).
% 2.17/1.30  tff(c_10, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.17/1.30  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.17/1.30  tff(c_23, plain, (![A_10, B_11]: (k3_subset_1(A_10, k3_subset_1(A_10, B_11))=B_11 | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.17/1.30  tff(c_28, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_10, c_23])).
% 2.17/1.30  tff(c_50, plain, (![B_14, A_15, C_16]: (r1_tarski(B_14, k3_subset_1(A_15, C_16)) | ~r1_xboole_0(B_14, C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(A_15)) | ~m1_subset_1(B_14, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.17/1.30  tff(c_56, plain, (![B_14]: (r1_tarski(B_14, '#skF_3') | ~r1_xboole_0(B_14, k3_subset_1('#skF_1', '#skF_3')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(B_14, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_28, c_50])).
% 2.17/1.30  tff(c_122, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_56])).
% 2.17/1.30  tff(c_125, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_2, c_122])).
% 2.17/1.30  tff(c_129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_125])).
% 2.17/1.30  tff(c_131, plain, (m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_56])).
% 2.17/1.30  tff(c_108, plain, (![B_19, C_20, A_21]: (r1_xboole_0(B_19, C_20) | ~r1_tarski(B_19, k3_subset_1(A_21, C_20)) | ~m1_subset_1(C_20, k1_zfmisc_1(A_21)) | ~m1_subset_1(B_19, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.17/1.30  tff(c_120, plain, (![B_19]: (r1_xboole_0(B_19, k3_subset_1('#skF_1', '#skF_3')) | ~r1_tarski(B_19, '#skF_3') | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(B_19, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_28, c_108])).
% 2.17/1.30  tff(c_139, plain, (![B_23]: (r1_xboole_0(B_23, k3_subset_1('#skF_1', '#skF_3')) | ~r1_tarski(B_23, '#skF_3') | ~m1_subset_1(B_23, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_120])).
% 2.17/1.30  tff(c_145, plain, (~r1_tarski('#skF_2', '#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_139, c_21])).
% 2.17/1.30  tff(c_150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_22, c_145])).
% 2.17/1.30  tff(c_151, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_14])).
% 2.17/1.30  tff(c_152, plain, (r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_14])).
% 2.17/1.30  tff(c_156, plain, (![A_26, B_27]: (k3_subset_1(A_26, k3_subset_1(A_26, B_27))=B_27 | ~m1_subset_1(B_27, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.17/1.30  tff(c_164, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_10, c_156])).
% 2.17/1.30  tff(c_230, plain, (![B_30, A_31, C_32]: (r1_tarski(B_30, k3_subset_1(A_31, C_32)) | ~r1_xboole_0(B_30, C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(A_31)) | ~m1_subset_1(B_30, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.17/1.30  tff(c_239, plain, (![B_30]: (r1_tarski(B_30, '#skF_3') | ~r1_xboole_0(B_30, k3_subset_1('#skF_1', '#skF_3')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(B_30, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_164, c_230])).
% 2.17/1.30  tff(c_254, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_239])).
% 2.17/1.30  tff(c_257, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_2, c_254])).
% 2.17/1.30  tff(c_261, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_257])).
% 2.17/1.30  tff(c_287, plain, (![B_37]: (r1_tarski(B_37, '#skF_3') | ~r1_xboole_0(B_37, k3_subset_1('#skF_1', '#skF_3')) | ~m1_subset_1(B_37, k1_zfmisc_1('#skF_1')))), inference(splitRight, [status(thm)], [c_239])).
% 2.17/1.30  tff(c_290, plain, (r1_tarski('#skF_2', '#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_152, c_287])).
% 2.17/1.30  tff(c_293, plain, (r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_290])).
% 2.17/1.30  tff(c_295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_151, c_293])).
% 2.17/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.30  
% 2.17/1.30  Inference rules
% 2.17/1.30  ----------------------
% 2.17/1.30  #Ref     : 0
% 2.17/1.30  #Sup     : 64
% 2.17/1.30  #Fact    : 0
% 2.17/1.30  #Define  : 0
% 2.17/1.30  #Split   : 4
% 2.17/1.30  #Chain   : 0
% 2.17/1.30  #Close   : 0
% 2.17/1.30  
% 2.17/1.30  Ordering : KBO
% 2.17/1.30  
% 2.17/1.30  Simplification rules
% 2.17/1.30  ----------------------
% 2.17/1.30  #Subsume      : 2
% 2.17/1.30  #Demod        : 28
% 2.17/1.30  #Tautology    : 42
% 2.17/1.30  #SimpNegUnit  : 3
% 2.17/1.30  #BackRed      : 0
% 2.17/1.30  
% 2.17/1.30  #Partial instantiations: 0
% 2.17/1.30  #Strategies tried      : 1
% 2.17/1.30  
% 2.17/1.30  Timing (in seconds)
% 2.17/1.30  ----------------------
% 2.17/1.31  Preprocessing        : 0.27
% 2.17/1.31  Parsing              : 0.15
% 2.17/1.31  CNF conversion       : 0.02
% 2.17/1.31  Main loop            : 0.25
% 2.17/1.31  Inferencing          : 0.11
% 2.17/1.31  Reduction            : 0.07
% 2.17/1.31  Demodulation         : 0.04
% 2.17/1.31  BG Simplification    : 0.01
% 2.17/1.31  Subsumption          : 0.05
% 2.17/1.31  Abstraction          : 0.01
% 2.17/1.31  MUC search           : 0.00
% 2.17/1.31  Cooper               : 0.00
% 2.17/1.31  Total                : 0.56
% 2.17/1.31  Index Insertion      : 0.00
% 2.17/1.31  Index Deletion       : 0.00
% 2.17/1.31  Index Matching       : 0.00
% 2.17/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
