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
% DateTime   : Thu Dec  3 09:55:57 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   45 (  55 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   57 (  85 expanded)
%              Number of equality atoms :   11 (  14 expanded)
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

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,k3_subset_1(A,C))
             => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_101,plain,(
    ! [A_36,B_37] :
      ( k3_subset_1(A_36,k3_subset_1(A_36,B_37)) = B_37
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_106,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_22,c_101])).

tff(c_147,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(k3_subset_1(A_47,B_48),k1_zfmisc_1(A_47))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = k3_subset_1(A_11,B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_313,plain,(
    ! [A_76,B_77] :
      ( k4_xboole_0(A_76,k3_subset_1(A_76,B_77)) = k3_subset_1(A_76,k3_subset_1(A_76,B_77))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_76)) ) ),
    inference(resolution,[status(thm)],[c_147,c_12])).

tff(c_317,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_313])).

tff(c_322,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_317])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_355,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_8])).

tff(c_20,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_50,plain,(
    ! [A_31,B_32] :
      ( k4_xboole_0(A_31,B_32) = k3_subset_1(A_31,B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_57,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_50])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,C_5)
      | ~ r1_tarski(A_3,k4_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_205,plain,(
    ! [A_52] :
      ( r1_xboole_0(A_52,'#skF_3')
      | ~ r1_tarski(A_52,k3_subset_1('#skF_1','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_4])).

tff(c_218,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_205])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_223,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_218,c_2])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_58,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_50])).

tff(c_228,plain,(
    ! [A_53,B_54,C_55] :
      ( r1_tarski(A_53,k4_xboole_0(B_54,C_55))
      | ~ r1_xboole_0(A_53,C_55)
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_503,plain,(
    ! [A_92] :
      ( r1_tarski(A_92,k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_xboole_0(A_92,'#skF_2')
      | ~ r1_tarski(A_92,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_228])).

tff(c_18,plain,(
    ~ r1_tarski('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_512,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_2')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_503,c_18])).

tff(c_518,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_223,c_512])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:45:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.89  
% 3.31/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.89  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.31/1.89  
% 3.31/1.89  %Foreground sorts:
% 3.31/1.89  
% 3.31/1.89  
% 3.31/1.89  %Background operators:
% 3.31/1.89  
% 3.31/1.89  
% 3.31/1.89  %Foreground operators:
% 3.31/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.89  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.31/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.31/1.89  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.31/1.89  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.31/1.89  tff('#skF_2', type, '#skF_2': $i).
% 3.31/1.89  tff('#skF_3', type, '#skF_3': $i).
% 3.31/1.89  tff('#skF_1', type, '#skF_1': $i).
% 3.31/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.31/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.31/1.89  
% 3.31/1.91  tff(f_65, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 3.31/1.91  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.31/1.91  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.31/1.91  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.31/1.91  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.31/1.91  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.31/1.91  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.31/1.91  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 3.31/1.91  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.31/1.91  tff(c_101, plain, (![A_36, B_37]: (k3_subset_1(A_36, k3_subset_1(A_36, B_37))=B_37 | ~m1_subset_1(B_37, k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.31/1.91  tff(c_106, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_22, c_101])).
% 3.31/1.91  tff(c_147, plain, (![A_47, B_48]: (m1_subset_1(k3_subset_1(A_47, B_48), k1_zfmisc_1(A_47)) | ~m1_subset_1(B_48, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.31/1.91  tff(c_12, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=k3_subset_1(A_11, B_12) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.31/1.91  tff(c_313, plain, (![A_76, B_77]: (k4_xboole_0(A_76, k3_subset_1(A_76, B_77))=k3_subset_1(A_76, k3_subset_1(A_76, B_77)) | ~m1_subset_1(B_77, k1_zfmisc_1(A_76)))), inference(resolution, [status(thm)], [c_147, c_12])).
% 3.31/1.91  tff(c_317, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_313])).
% 3.31/1.91  tff(c_322, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_317])).
% 3.31/1.91  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.31/1.91  tff(c_355, plain, (r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_322, c_8])).
% 3.31/1.91  tff(c_20, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.31/1.91  tff(c_50, plain, (![A_31, B_32]: (k4_xboole_0(A_31, B_32)=k3_subset_1(A_31, B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.31/1.91  tff(c_57, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_50])).
% 3.31/1.91  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, C_5) | ~r1_tarski(A_3, k4_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.31/1.91  tff(c_205, plain, (![A_52]: (r1_xboole_0(A_52, '#skF_3') | ~r1_tarski(A_52, k3_subset_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_57, c_4])).
% 3.31/1.91  tff(c_218, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_205])).
% 3.31/1.91  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.31/1.91  tff(c_223, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_218, c_2])).
% 3.31/1.91  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.31/1.91  tff(c_58, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_50])).
% 3.31/1.91  tff(c_228, plain, (![A_53, B_54, C_55]: (r1_tarski(A_53, k4_xboole_0(B_54, C_55)) | ~r1_xboole_0(A_53, C_55) | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.31/1.91  tff(c_503, plain, (![A_92]: (r1_tarski(A_92, k3_subset_1('#skF_1', '#skF_2')) | ~r1_xboole_0(A_92, '#skF_2') | ~r1_tarski(A_92, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_228])).
% 3.31/1.91  tff(c_18, plain, (~r1_tarski('#skF_3', k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.31/1.91  tff(c_512, plain, (~r1_xboole_0('#skF_3', '#skF_2') | ~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_503, c_18])).
% 3.31/1.91  tff(c_518, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_355, c_223, c_512])).
% 3.31/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.91  
% 3.31/1.91  Inference rules
% 3.31/1.91  ----------------------
% 3.31/1.91  #Ref     : 0
% 3.31/1.91  #Sup     : 121
% 3.31/1.91  #Fact    : 0
% 3.31/1.91  #Define  : 0
% 3.31/1.91  #Split   : 0
% 3.31/1.91  #Chain   : 0
% 3.31/1.91  #Close   : 0
% 3.31/1.91  
% 3.31/1.91  Ordering : KBO
% 3.31/1.91  
% 3.31/1.91  Simplification rules
% 3.31/1.91  ----------------------
% 3.31/1.91  #Subsume      : 1
% 3.31/1.91  #Demod        : 35
% 3.31/1.91  #Tautology    : 51
% 3.31/1.91  #SimpNegUnit  : 0
% 3.31/1.91  #BackRed      : 0
% 3.31/1.91  
% 3.31/1.91  #Partial instantiations: 0
% 3.31/1.91  #Strategies tried      : 1
% 3.31/1.91  
% 3.31/1.91  Timing (in seconds)
% 3.31/1.91  ----------------------
% 3.53/1.92  Preprocessing        : 0.46
% 3.53/1.92  Parsing              : 0.24
% 3.53/1.92  CNF conversion       : 0.03
% 3.53/1.92  Main loop            : 0.53
% 3.53/1.92  Inferencing          : 0.20
% 3.53/1.92  Reduction            : 0.17
% 3.53/1.92  Demodulation         : 0.13
% 3.53/1.92  BG Simplification    : 0.02
% 3.53/1.92  Subsumption          : 0.09
% 3.53/1.92  Abstraction          : 0.02
% 3.53/1.92  MUC search           : 0.00
% 3.53/1.92  Cooper               : 0.00
% 3.53/1.92  Total                : 1.04
% 3.53/1.92  Index Insertion      : 0.00
% 3.53/1.92  Index Deletion       : 0.00
% 3.53/1.92  Index Matching       : 0.00
% 3.53/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
