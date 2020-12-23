%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:39 EST 2020

% Result     : Theorem 4.59s
% Output     : CNFRefutation 4.59s
% Verified   : 
% Statistics : Number of formulae       :   53 (  77 expanded)
%              Number of leaves         :   20 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   69 ( 131 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,k3_subset_1(A,C))
            <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_32,plain,
    ( r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3'))
    | r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_71,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_123,plain,(
    ! [A_53,B_54] :
      ( k4_xboole_0(A_53,B_54) = k3_subset_1(A_53,B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_131,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_123])).

tff(c_12,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_xboole_0(A_6,k4_xboole_0(C_8,B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_338,plain,(
    ! [A_68] :
      ( r1_xboole_0(A_68,k3_subset_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_68,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_12])).

tff(c_26,plain,
    ( ~ r1_tarski('#skF_2','#skF_3')
    | ~ r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_91,plain,(
    ~ r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_26])).

tff(c_344,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_338,c_91])).

tff(c_349,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_344])).

tff(c_351,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_372,plain,(
    ! [A_74,B_75] :
      ( k3_subset_1(A_74,k3_subset_1(A_74,B_75)) = B_75
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_377,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_24,c_372])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k3_subset_1(A_14,B_15),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_415,plain,(
    ! [A_88,B_89] :
      ( k4_xboole_0(A_88,B_89) = k3_subset_1(A_88,B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1024,plain,(
    ! [A_114,B_115] :
      ( k4_xboole_0(A_114,k3_subset_1(A_114,B_115)) = k3_subset_1(A_114,k3_subset_1(A_114,B_115))
      | ~ m1_subset_1(B_115,k1_zfmisc_1(A_114)) ) ),
    inference(resolution,[status(thm)],[c_18,c_415])).

tff(c_1028,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_1024])).

tff(c_1033,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_1028])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ! [A_25,B_26,C_27] :
      ( r1_tarski(A_25,B_26)
      | ~ r1_tarski(A_25,k4_xboole_0(B_26,C_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_47,plain,(
    ! [B_26,C_27] : r1_tarski(k4_xboole_0(B_26,C_27),B_26) ),
    inference(resolution,[status(thm)],[c_6,c_42])).

tff(c_1063,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1033,c_47])).

tff(c_350,plain,(
    r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_378,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_22,c_372])).

tff(c_1030,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_1024])).

tff(c_1035,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_1030])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] :
      ( r1_tarski(A_9,k4_xboole_0(B_10,C_11))
      | ~ r1_xboole_0(A_9,C_11)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3713,plain,(
    ! [A_173] :
      ( r1_tarski(A_173,'#skF_3')
      | ~ r1_xboole_0(A_173,k3_subset_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_173,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1035,c_14])).

tff(c_3741,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_350,c_3713])).

tff(c_3770,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1063,c_3741])).

tff(c_3772,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_351,c_3770])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:46:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.59/1.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.59/1.87  
% 4.59/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.59/1.87  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 4.59/1.87  
% 4.59/1.87  %Foreground sorts:
% 4.59/1.87  
% 4.59/1.87  
% 4.59/1.87  %Background operators:
% 4.59/1.87  
% 4.59/1.87  
% 4.59/1.87  %Foreground operators:
% 4.59/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.59/1.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.59/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.59/1.87  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.59/1.87  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.59/1.87  tff('#skF_2', type, '#skF_2': $i).
% 4.59/1.87  tff('#skF_3', type, '#skF_3': $i).
% 4.59/1.87  tff('#skF_1', type, '#skF_1': $i).
% 4.59/1.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.59/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.59/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.59/1.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.59/1.87  
% 4.59/1.88  tff(f_69, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_subset_1)).
% 4.59/1.88  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.59/1.88  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 4.59/1.88  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.59/1.88  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.59/1.88  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.59/1.88  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 4.59/1.88  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 4.59/1.88  tff(c_32, plain, (r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3')) | r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.59/1.88  tff(c_71, plain, (r1_tarski('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_32])).
% 4.59/1.88  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.59/1.88  tff(c_123, plain, (![A_53, B_54]: (k4_xboole_0(A_53, B_54)=k3_subset_1(A_53, B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.59/1.88  tff(c_131, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_123])).
% 4.59/1.88  tff(c_12, plain, (![A_6, C_8, B_7]: (r1_xboole_0(A_6, k4_xboole_0(C_8, B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.59/1.88  tff(c_338, plain, (![A_68]: (r1_xboole_0(A_68, k3_subset_1('#skF_1', '#skF_3')) | ~r1_tarski(A_68, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_12])).
% 4.59/1.88  tff(c_26, plain, (~r1_tarski('#skF_2', '#skF_3') | ~r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.59/1.88  tff(c_91, plain, (~r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_26])).
% 4.59/1.88  tff(c_344, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_338, c_91])).
% 4.59/1.88  tff(c_349, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_344])).
% 4.59/1.88  tff(c_351, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_32])).
% 4.59/1.88  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.59/1.88  tff(c_372, plain, (![A_74, B_75]: (k3_subset_1(A_74, k3_subset_1(A_74, B_75))=B_75 | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.59/1.88  tff(c_377, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_24, c_372])).
% 4.59/1.88  tff(c_18, plain, (![A_14, B_15]: (m1_subset_1(k3_subset_1(A_14, B_15), k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.59/1.88  tff(c_415, plain, (![A_88, B_89]: (k4_xboole_0(A_88, B_89)=k3_subset_1(A_88, B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(A_88)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.59/1.88  tff(c_1024, plain, (![A_114, B_115]: (k4_xboole_0(A_114, k3_subset_1(A_114, B_115))=k3_subset_1(A_114, k3_subset_1(A_114, B_115)) | ~m1_subset_1(B_115, k1_zfmisc_1(A_114)))), inference(resolution, [status(thm)], [c_18, c_415])).
% 4.59/1.88  tff(c_1028, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_1024])).
% 4.59/1.88  tff(c_1033, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_377, c_1028])).
% 4.59/1.88  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.59/1.88  tff(c_42, plain, (![A_25, B_26, C_27]: (r1_tarski(A_25, B_26) | ~r1_tarski(A_25, k4_xboole_0(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.59/1.88  tff(c_47, plain, (![B_26, C_27]: (r1_tarski(k4_xboole_0(B_26, C_27), B_26))), inference(resolution, [status(thm)], [c_6, c_42])).
% 4.59/1.88  tff(c_1063, plain, (r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1033, c_47])).
% 4.59/1.88  tff(c_350, plain, (r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_32])).
% 4.59/1.88  tff(c_378, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_22, c_372])).
% 4.59/1.88  tff(c_1030, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_1024])).
% 4.59/1.88  tff(c_1035, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_378, c_1030])).
% 4.59/1.88  tff(c_14, plain, (![A_9, B_10, C_11]: (r1_tarski(A_9, k4_xboole_0(B_10, C_11)) | ~r1_xboole_0(A_9, C_11) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.59/1.88  tff(c_3713, plain, (![A_173]: (r1_tarski(A_173, '#skF_3') | ~r1_xboole_0(A_173, k3_subset_1('#skF_1', '#skF_3')) | ~r1_tarski(A_173, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1035, c_14])).
% 4.59/1.88  tff(c_3741, plain, (r1_tarski('#skF_2', '#skF_3') | ~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_350, c_3713])).
% 4.59/1.88  tff(c_3770, plain, (r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1063, c_3741])).
% 4.59/1.88  tff(c_3772, plain, $false, inference(negUnitSimplification, [status(thm)], [c_351, c_3770])).
% 4.59/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.59/1.88  
% 4.59/1.88  Inference rules
% 4.59/1.88  ----------------------
% 4.59/1.88  #Ref     : 0
% 4.59/1.88  #Sup     : 886
% 4.59/1.88  #Fact    : 0
% 4.59/1.88  #Define  : 0
% 4.59/1.88  #Split   : 8
% 4.59/1.88  #Chain   : 0
% 4.59/1.88  #Close   : 0
% 4.59/1.88  
% 4.59/1.88  Ordering : KBO
% 4.59/1.88  
% 4.59/1.88  Simplification rules
% 4.59/1.88  ----------------------
% 4.59/1.88  #Subsume      : 92
% 4.59/1.88  #Demod        : 535
% 4.59/1.88  #Tautology    : 468
% 4.59/1.88  #SimpNegUnit  : 1
% 4.59/1.88  #BackRed      : 0
% 4.59/1.88  
% 4.59/1.88  #Partial instantiations: 0
% 4.59/1.88  #Strategies tried      : 1
% 4.59/1.88  
% 4.59/1.88  Timing (in seconds)
% 4.59/1.88  ----------------------
% 4.59/1.88  Preprocessing        : 0.30
% 4.59/1.88  Parsing              : 0.17
% 4.59/1.88  CNF conversion       : 0.02
% 4.59/1.88  Main loop            : 0.77
% 4.59/1.88  Inferencing          : 0.24
% 4.59/1.88  Reduction            : 0.28
% 4.59/1.88  Demodulation         : 0.22
% 4.59/1.88  BG Simplification    : 0.03
% 4.59/1.88  Subsumption          : 0.17
% 4.59/1.89  Abstraction          : 0.04
% 4.59/1.89  MUC search           : 0.00
% 4.59/1.89  Cooper               : 0.00
% 4.59/1.89  Total                : 1.10
% 4.59/1.89  Index Insertion      : 0.00
% 4.59/1.89  Index Deletion       : 0.00
% 4.59/1.89  Index Matching       : 0.00
% 4.59/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
