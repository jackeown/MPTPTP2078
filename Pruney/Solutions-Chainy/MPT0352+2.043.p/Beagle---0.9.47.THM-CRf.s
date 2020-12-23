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
% DateTime   : Thu Dec  3 09:55:52 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   47 (  76 expanded)
%              Number of leaves         :   16 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   56 ( 129 expanded)
%              Number of equality atoms :   14 (  22 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_51,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,C)
            <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

tff(c_20,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_38,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_14,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_55,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_14])).

tff(c_12,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_44,plain,(
    ! [A_15,B_16] :
      ( k3_subset_1(A_15,k3_subset_1(A_15,B_16)) = B_16
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_53,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_12,c_44])).

tff(c_39,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k3_subset_1(A_13,B_14),k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k4_xboole_0(A_4,B_5) = k3_subset_1(A_4,B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_166,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(A_26,k3_subset_1(A_26,B_27)) = k3_subset_1(A_26,k3_subset_1(A_26,B_27))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_26)) ) ),
    inference(resolution,[status(thm)],[c_39,c_4])).

tff(c_172,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_12,c_166])).

tff(c_177,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_172])).

tff(c_10,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_52,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_10,c_44])).

tff(c_170,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_10,c_166])).

tff(c_175,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_170])).

tff(c_2,plain,(
    ! [C_3,B_2,A_1] :
      ( r1_tarski(k4_xboole_0(C_3,B_2),k4_xboole_0(C_3,A_1))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_222,plain,(
    ! [B_28] :
      ( r1_tarski(k4_xboole_0('#skF_1',B_28),'#skF_3')
      | ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),B_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_2])).

tff(c_225,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_222])).

tff(c_236,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_225])).

tff(c_238,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_236])).

tff(c_240,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_239,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_21,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = k3_subset_1(A_11,B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_21])).

tff(c_29,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_21])).

tff(c_278,plain,(
    ! [C_33,B_34,A_35] :
      ( r1_tarski(k4_xboole_0(C_33,B_34),k4_xboole_0(C_33,A_35))
      | ~ r1_tarski(A_35,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_298,plain,(
    ! [B_37] :
      ( r1_tarski(k4_xboole_0('#skF_1',B_37),k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_tarski('#skF_2',B_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29,c_278])).

tff(c_304,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_298])).

tff(c_306,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_304])).

tff(c_308,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_306])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:15:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.24  
% 2.04/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.24  %$ r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.04/1.24  
% 2.04/1.24  %Foreground sorts:
% 2.04/1.24  
% 2.04/1.24  
% 2.04/1.24  %Background operators:
% 2.04/1.24  
% 2.04/1.24  
% 2.04/1.24  %Foreground operators:
% 2.04/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.04/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.04/1.24  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.04/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.04/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.04/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.04/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.04/1.24  
% 2.04/1.25  tff(f_51, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 2.04/1.25  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.04/1.25  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.04/1.25  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.04/1.25  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_xboole_1)).
% 2.04/1.25  tff(c_20, plain, (r1_tarski('#skF_2', '#skF_3') | r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.04/1.25  tff(c_38, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_20])).
% 2.04/1.25  tff(c_14, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.04/1.25  tff(c_55, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_14])).
% 2.04/1.25  tff(c_12, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.04/1.25  tff(c_44, plain, (![A_15, B_16]: (k3_subset_1(A_15, k3_subset_1(A_15, B_16))=B_16 | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.04/1.25  tff(c_53, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_12, c_44])).
% 2.04/1.25  tff(c_39, plain, (![A_13, B_14]: (m1_subset_1(k3_subset_1(A_13, B_14), k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.04/1.25  tff(c_4, plain, (![A_4, B_5]: (k4_xboole_0(A_4, B_5)=k3_subset_1(A_4, B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.04/1.25  tff(c_166, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k3_subset_1(A_26, B_27))=k3_subset_1(A_26, k3_subset_1(A_26, B_27)) | ~m1_subset_1(B_27, k1_zfmisc_1(A_26)))), inference(resolution, [status(thm)], [c_39, c_4])).
% 2.04/1.25  tff(c_172, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_12, c_166])).
% 2.04/1.25  tff(c_177, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_53, c_172])).
% 2.04/1.25  tff(c_10, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.04/1.25  tff(c_52, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_10, c_44])).
% 2.04/1.25  tff(c_170, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_10, c_166])).
% 2.04/1.25  tff(c_175, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_170])).
% 2.04/1.25  tff(c_2, plain, (![C_3, B_2, A_1]: (r1_tarski(k4_xboole_0(C_3, B_2), k4_xboole_0(C_3, A_1)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.04/1.25  tff(c_222, plain, (![B_28]: (r1_tarski(k4_xboole_0('#skF_1', B_28), '#skF_3') | ~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), B_28))), inference(superposition, [status(thm), theory('equality')], [c_175, c_2])).
% 2.04/1.25  tff(c_225, plain, (r1_tarski('#skF_2', '#skF_3') | ~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_177, c_222])).
% 2.04/1.25  tff(c_236, plain, (r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_225])).
% 2.04/1.25  tff(c_238, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_236])).
% 2.04/1.25  tff(c_240, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_20])).
% 2.04/1.25  tff(c_239, plain, (r1_tarski('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_20])).
% 2.04/1.25  tff(c_21, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=k3_subset_1(A_11, B_12) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.04/1.25  tff(c_28, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_10, c_21])).
% 2.04/1.25  tff(c_29, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_12, c_21])).
% 2.04/1.25  tff(c_278, plain, (![C_33, B_34, A_35]: (r1_tarski(k4_xboole_0(C_33, B_34), k4_xboole_0(C_33, A_35)) | ~r1_tarski(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.04/1.25  tff(c_298, plain, (![B_37]: (r1_tarski(k4_xboole_0('#skF_1', B_37), k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', B_37))), inference(superposition, [status(thm), theory('equality')], [c_29, c_278])).
% 2.04/1.25  tff(c_304, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_298])).
% 2.04/1.25  tff(c_306, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_239, c_304])).
% 2.04/1.25  tff(c_308, plain, $false, inference(negUnitSimplification, [status(thm)], [c_240, c_306])).
% 2.04/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.25  
% 2.04/1.25  Inference rules
% 2.04/1.25  ----------------------
% 2.04/1.25  #Ref     : 0
% 2.04/1.25  #Sup     : 80
% 2.04/1.25  #Fact    : 0
% 2.04/1.25  #Define  : 0
% 2.04/1.25  #Split   : 5
% 2.04/1.25  #Chain   : 0
% 2.04/1.25  #Close   : 0
% 2.04/1.25  
% 2.04/1.25  Ordering : KBO
% 2.04/1.25  
% 2.04/1.25  Simplification rules
% 2.04/1.25  ----------------------
% 2.04/1.25  #Subsume      : 5
% 2.04/1.25  #Demod        : 19
% 2.04/1.25  #Tautology    : 37
% 2.04/1.25  #SimpNegUnit  : 2
% 2.04/1.25  #BackRed      : 0
% 2.04/1.25  
% 2.04/1.25  #Partial instantiations: 0
% 2.04/1.25  #Strategies tried      : 1
% 2.04/1.25  
% 2.04/1.25  Timing (in seconds)
% 2.04/1.25  ----------------------
% 2.04/1.25  Preprocessing        : 0.28
% 2.04/1.25  Parsing              : 0.15
% 2.04/1.25  CNF conversion       : 0.02
% 2.04/1.25  Main loop            : 0.21
% 2.04/1.25  Inferencing          : 0.08
% 2.04/1.25  Reduction            : 0.06
% 2.04/1.25  Demodulation         : 0.04
% 2.04/1.25  BG Simplification    : 0.01
% 2.04/1.25  Subsumption          : 0.04
% 2.04/1.25  Abstraction          : 0.01
% 2.04/1.25  MUC search           : 0.00
% 2.04/1.25  Cooper               : 0.00
% 2.04/1.25  Total                : 0.52
% 2.04/1.25  Index Insertion      : 0.00
% 2.04/1.25  Index Deletion       : 0.00
% 2.04/1.25  Index Matching       : 0.00
% 2.04/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
