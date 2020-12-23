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
% DateTime   : Thu Dec  3 09:55:52 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   53 (  87 expanded)
%              Number of leaves         :   19 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   62 ( 144 expanded)
%              Number of equality atoms :   17 (  26 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_53,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,C)
            <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(C,B)
     => k4_xboole_0(A,C) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,k4_xboole_0(B,C))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_22,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_37,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_16,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_50,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_16])).

tff(c_14,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_42,plain,(
    ! [A_17,B_18] :
      ( k3_subset_1(A_17,k3_subset_1(A_17,B_18)) = B_18
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_48,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_14,c_42])).

tff(c_59,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k3_subset_1(A_19,B_20),k1_zfmisc_1(A_19))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = k3_subset_1(A_6,B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_123,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,k3_subset_1(A_23,B_24)) = k3_subset_1(A_23,k3_subset_1(A_23,B_24))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(A_23)) ) ),
    inference(resolution,[status(thm)],[c_59,c_6])).

tff(c_129,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_14,c_123])).

tff(c_134,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_129])).

tff(c_12,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_47,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_12,c_42])).

tff(c_127,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_123])).

tff(c_132,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_127])).

tff(c_135,plain,(
    ! [A_25,B_26,C_27] :
      ( k2_xboole_0(k4_xboole_0(A_25,B_26),k3_xboole_0(A_25,k4_xboole_0(B_26,C_27))) = k4_xboole_0(A_25,C_27)
      | ~ r1_tarski(C_27,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(A_4,k2_xboole_0(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_179,plain,(
    ! [A_28,B_29,C_30] :
      ( r1_tarski(k4_xboole_0(A_28,B_29),k4_xboole_0(A_28,C_30))
      | ~ r1_tarski(C_30,B_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_4])).

tff(c_297,plain,(
    ! [B_38] :
      ( r1_tarski(k4_xboole_0('#skF_1',B_38),'#skF_3')
      | ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),B_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_179])).

tff(c_300,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_297])).

tff(c_311,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_300])).

tff(c_313,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_311])).

tff(c_314,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_321,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_16])).

tff(c_24,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,B_16) = k3_subset_1(A_15,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_31,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_24])).

tff(c_32,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_24])).

tff(c_353,plain,(
    ! [A_43,B_44,C_45] :
      ( k2_xboole_0(k4_xboole_0(A_43,B_44),k3_xboole_0(A_43,k4_xboole_0(B_44,C_45))) = k4_xboole_0(A_43,C_45)
      | ~ r1_tarski(C_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_377,plain,(
    ! [A_46,B_47,C_48] :
      ( r1_tarski(k4_xboole_0(A_46,B_47),k4_xboole_0(A_46,C_48))
      | ~ r1_tarski(C_48,B_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_4])).

tff(c_397,plain,(
    ! [B_50] :
      ( r1_tarski(k4_xboole_0('#skF_1',B_50),k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_tarski('#skF_2',B_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_377])).

tff(c_403,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_397])).

tff(c_405,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_403])).

tff(c_407,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_321,c_405])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:20:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.35  
% 2.29/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.35  %$ r1_tarski > m1_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.29/1.35  
% 2.29/1.35  %Foreground sorts:
% 2.29/1.35  
% 2.29/1.35  
% 2.29/1.35  %Background operators:
% 2.29/1.35  
% 2.29/1.35  
% 2.29/1.35  %Foreground operators:
% 2.29/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.29/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.29/1.35  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.29/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.29/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.29/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.29/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.29/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.29/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.29/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.29/1.35  
% 2.29/1.36  tff(f_53, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 2.29/1.36  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.29/1.36  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.29/1.36  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.29/1.36  tff(f_29, axiom, (![A, B, C]: (r1_tarski(C, B) => (k4_xboole_0(A, C) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, k4_xboole_0(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_xboole_1)).
% 2.29/1.36  tff(f_31, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.29/1.36  tff(c_22, plain, (r1_tarski('#skF_2', '#skF_3') | r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.29/1.36  tff(c_37, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_22])).
% 2.29/1.36  tff(c_16, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.29/1.36  tff(c_50, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_37, c_16])).
% 2.29/1.36  tff(c_14, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.29/1.36  tff(c_42, plain, (![A_17, B_18]: (k3_subset_1(A_17, k3_subset_1(A_17, B_18))=B_18 | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.29/1.36  tff(c_48, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_14, c_42])).
% 2.29/1.36  tff(c_59, plain, (![A_19, B_20]: (m1_subset_1(k3_subset_1(A_19, B_20), k1_zfmisc_1(A_19)) | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.29/1.36  tff(c_6, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=k3_subset_1(A_6, B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.29/1.36  tff(c_123, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k3_subset_1(A_23, B_24))=k3_subset_1(A_23, k3_subset_1(A_23, B_24)) | ~m1_subset_1(B_24, k1_zfmisc_1(A_23)))), inference(resolution, [status(thm)], [c_59, c_6])).
% 2.29/1.36  tff(c_129, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_14, c_123])).
% 2.29/1.36  tff(c_134, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_129])).
% 2.29/1.36  tff(c_12, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.29/1.36  tff(c_47, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_12, c_42])).
% 2.29/1.36  tff(c_127, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_123])).
% 2.29/1.36  tff(c_132, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_47, c_127])).
% 2.29/1.36  tff(c_135, plain, (![A_25, B_26, C_27]: (k2_xboole_0(k4_xboole_0(A_25, B_26), k3_xboole_0(A_25, k4_xboole_0(B_26, C_27)))=k4_xboole_0(A_25, C_27) | ~r1_tarski(C_27, B_26))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.29/1.36  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, k2_xboole_0(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.29/1.36  tff(c_179, plain, (![A_28, B_29, C_30]: (r1_tarski(k4_xboole_0(A_28, B_29), k4_xboole_0(A_28, C_30)) | ~r1_tarski(C_30, B_29))), inference(superposition, [status(thm), theory('equality')], [c_135, c_4])).
% 2.29/1.36  tff(c_297, plain, (![B_38]: (r1_tarski(k4_xboole_0('#skF_1', B_38), '#skF_3') | ~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), B_38))), inference(superposition, [status(thm), theory('equality')], [c_132, c_179])).
% 2.29/1.36  tff(c_300, plain, (r1_tarski('#skF_2', '#skF_3') | ~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_134, c_297])).
% 2.29/1.36  tff(c_311, plain, (r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_37, c_300])).
% 2.29/1.36  tff(c_313, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_311])).
% 2.29/1.36  tff(c_314, plain, (r1_tarski('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_22])).
% 2.29/1.36  tff(c_321, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_314, c_16])).
% 2.29/1.36  tff(c_24, plain, (![A_15, B_16]: (k4_xboole_0(A_15, B_16)=k3_subset_1(A_15, B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.29/1.36  tff(c_31, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_12, c_24])).
% 2.29/1.36  tff(c_32, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_14, c_24])).
% 2.29/1.36  tff(c_353, plain, (![A_43, B_44, C_45]: (k2_xboole_0(k4_xboole_0(A_43, B_44), k3_xboole_0(A_43, k4_xboole_0(B_44, C_45)))=k4_xboole_0(A_43, C_45) | ~r1_tarski(C_45, B_44))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.29/1.36  tff(c_377, plain, (![A_46, B_47, C_48]: (r1_tarski(k4_xboole_0(A_46, B_47), k4_xboole_0(A_46, C_48)) | ~r1_tarski(C_48, B_47))), inference(superposition, [status(thm), theory('equality')], [c_353, c_4])).
% 2.29/1.36  tff(c_397, plain, (![B_50]: (r1_tarski(k4_xboole_0('#skF_1', B_50), k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', B_50))), inference(superposition, [status(thm), theory('equality')], [c_32, c_377])).
% 2.29/1.36  tff(c_403, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_31, c_397])).
% 2.29/1.36  tff(c_405, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_314, c_403])).
% 2.29/1.36  tff(c_407, plain, $false, inference(negUnitSimplification, [status(thm)], [c_321, c_405])).
% 2.29/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.36  
% 2.29/1.36  Inference rules
% 2.29/1.36  ----------------------
% 2.29/1.36  #Ref     : 0
% 2.29/1.36  #Sup     : 108
% 2.29/1.36  #Fact    : 0
% 2.29/1.36  #Define  : 0
% 2.29/1.36  #Split   : 8
% 2.29/1.36  #Chain   : 0
% 2.29/1.36  #Close   : 0
% 2.29/1.36  
% 2.29/1.36  Ordering : KBO
% 2.29/1.36  
% 2.29/1.36  Simplification rules
% 2.29/1.36  ----------------------
% 2.29/1.36  #Subsume      : 9
% 2.29/1.36  #Demod        : 18
% 2.29/1.36  #Tautology    : 45
% 2.29/1.36  #SimpNegUnit  : 5
% 2.29/1.36  #BackRed      : 0
% 2.29/1.36  
% 2.29/1.36  #Partial instantiations: 0
% 2.29/1.36  #Strategies tried      : 1
% 2.29/1.36  
% 2.29/1.36  Timing (in seconds)
% 2.29/1.36  ----------------------
% 2.29/1.36  Preprocessing        : 0.27
% 2.29/1.36  Parsing              : 0.14
% 2.29/1.36  CNF conversion       : 0.02
% 2.29/1.36  Main loop            : 0.27
% 2.29/1.36  Inferencing          : 0.10
% 2.29/1.36  Reduction            : 0.08
% 2.29/1.36  Demodulation         : 0.06
% 2.29/1.37  BG Simplification    : 0.02
% 2.29/1.37  Subsumption          : 0.05
% 2.29/1.37  Abstraction          : 0.01
% 2.29/1.37  MUC search           : 0.00
% 2.29/1.37  Cooper               : 0.00
% 2.29/1.37  Total                : 0.57
% 2.43/1.37  Index Insertion      : 0.00
% 2.43/1.37  Index Deletion       : 0.00
% 2.43/1.37  Index Matching       : 0.00
% 2.43/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
