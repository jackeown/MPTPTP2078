%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:16 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 142 expanded)
%              Number of leaves         :   20 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :   71 ( 202 expanded)
%              Number of equality atoms :   29 ( 102 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_41,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_43,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k1_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

tff(f_55,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(c_12,plain,(
    ! [A_7] : k1_subset_1(A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_9] : m1_subset_1(k1_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [A_14] : k3_subset_1(A_14,k1_subset_1(A_14)) = k2_subset_1(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_30,plain,(
    ! [A_23] :
      ( r1_tarski(k1_subset_1(A_23),k3_subset_1(A_23,k1_subset_1(A_23)))
      | ~ m1_subset_1(k1_subset_1(A_23),k1_zfmisc_1(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_43,plain,(
    ! [A_23] :
      ( r1_tarski(k1_subset_1(A_23),k2_subset_1(A_23))
      | ~ m1_subset_1(k1_subset_1(A_23),k1_zfmisc_1(A_23)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_30])).

tff(c_45,plain,(
    ! [A_23] : r1_tarski(k1_subset_1(A_23),k2_subset_1(A_23)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_43])).

tff(c_46,plain,(
    ! [A_23] : r1_tarski(k1_subset_1(A_23),A_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_45])).

tff(c_52,plain,(
    ! [A_23] : r1_tarski(k1_xboole_0,A_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_46])).

tff(c_48,plain,(
    ! [A_14] : k3_subset_1(A_14,k1_subset_1(A_14)) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_22])).

tff(c_50,plain,(
    ! [A_14] : k3_subset_1(A_14,k1_xboole_0) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_48])).

tff(c_51,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16])).

tff(c_141,plain,(
    ! [A_42,B_43] :
      ( k3_subset_1(A_42,k3_subset_1(A_42,B_43)) = B_43
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_147,plain,(
    ! [A_9] : k3_subset_1(A_9,k3_subset_1(A_9,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_51,c_141])).

tff(c_151,plain,(
    ! [A_9] : k3_subset_1(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_147])).

tff(c_36,plain,
    ( k2_subset_1('#skF_1') != '#skF_2'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_47,plain,
    ( '#skF_2' != '#skF_1'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_36])).

tff(c_84,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_47])).

tff(c_42,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | k2_subset_1('#skF_1') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_49,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_42])).

tff(c_85,plain,(
    '#skF_2' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_49])).

tff(c_86,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_85,c_84])).

tff(c_169,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_86])).

tff(c_172,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_169])).

tff(c_173,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_47])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(k3_subset_1(A_10,B_11),k1_zfmisc_1(A_10))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_174,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_47])).

tff(c_238,plain,(
    ! [A_56,B_57] :
      ( k3_subset_1(A_56,k3_subset_1(A_56,B_57)) = B_57
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_245,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_34,c_238])).

tff(c_32,plain,(
    ! [A_23,B_24] :
      ( k1_subset_1(A_23) = B_24
      | ~ r1_tarski(B_24,k3_subset_1(A_23,B_24))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_284,plain,(
    ! [B_61,A_62] :
      ( k1_xboole_0 = B_61
      | ~ r1_tarski(B_61,k3_subset_1(A_62,B_61))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_62)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_32])).

tff(c_287,plain,
    ( k3_subset_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_284])).

tff(c_299,plain,
    ( k3_subset_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_287])).

tff(c_312,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_299])).

tff(c_315,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_18,c_312])).

tff(c_319,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_315])).

tff(c_320,plain,(
    k3_subset_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_322,plain,(
    k3_subset_1('#skF_1',k1_xboole_0) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_245])).

tff(c_326,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_322])).

tff(c_328,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_326])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:45:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.25  
% 2.12/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.25  %$ r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.12/1.25  
% 2.12/1.25  %Foreground sorts:
% 2.12/1.25  
% 2.12/1.25  
% 2.12/1.25  %Background operators:
% 2.12/1.25  
% 2.12/1.25  
% 2.12/1.25  %Foreground operators:
% 2.12/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.12/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.25  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.12/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.12/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.12/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.12/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.25  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.12/1.25  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.12/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.12/1.25  
% 2.21/1.27  tff(f_41, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.21/1.27  tff(f_43, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.21/1.27  tff(f_45, axiom, (![A]: m1_subset_1(k1_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 2.21/1.27  tff(f_55, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.21/1.27  tff(f_79, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 2.21/1.27  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.21/1.27  tff(f_86, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 2.21/1.27  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.21/1.27  tff(c_12, plain, (![A_7]: (k1_subset_1(A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.21/1.27  tff(c_14, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.21/1.27  tff(c_16, plain, (![A_9]: (m1_subset_1(k1_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.21/1.27  tff(c_22, plain, (![A_14]: (k3_subset_1(A_14, k1_subset_1(A_14))=k2_subset_1(A_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.21/1.27  tff(c_30, plain, (![A_23]: (r1_tarski(k1_subset_1(A_23), k3_subset_1(A_23, k1_subset_1(A_23))) | ~m1_subset_1(k1_subset_1(A_23), k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.21/1.27  tff(c_43, plain, (![A_23]: (r1_tarski(k1_subset_1(A_23), k2_subset_1(A_23)) | ~m1_subset_1(k1_subset_1(A_23), k1_zfmisc_1(A_23)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_30])).
% 2.21/1.27  tff(c_45, plain, (![A_23]: (r1_tarski(k1_subset_1(A_23), k2_subset_1(A_23)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_43])).
% 2.21/1.27  tff(c_46, plain, (![A_23]: (r1_tarski(k1_subset_1(A_23), A_23))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_45])).
% 2.21/1.27  tff(c_52, plain, (![A_23]: (r1_tarski(k1_xboole_0, A_23))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_46])).
% 2.21/1.27  tff(c_48, plain, (![A_14]: (k3_subset_1(A_14, k1_subset_1(A_14))=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_22])).
% 2.21/1.27  tff(c_50, plain, (![A_14]: (k3_subset_1(A_14, k1_xboole_0)=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_48])).
% 2.21/1.27  tff(c_51, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16])).
% 2.21/1.27  tff(c_141, plain, (![A_42, B_43]: (k3_subset_1(A_42, k3_subset_1(A_42, B_43))=B_43 | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.21/1.27  tff(c_147, plain, (![A_9]: (k3_subset_1(A_9, k3_subset_1(A_9, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_51, c_141])).
% 2.21/1.27  tff(c_151, plain, (![A_9]: (k3_subset_1(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_147])).
% 2.21/1.27  tff(c_36, plain, (k2_subset_1('#skF_1')!='#skF_2' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.21/1.27  tff(c_47, plain, ('#skF_2'!='#skF_1' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_36])).
% 2.21/1.27  tff(c_84, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_47])).
% 2.21/1.27  tff(c_42, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | k2_subset_1('#skF_1')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.21/1.27  tff(c_49, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_42])).
% 2.21/1.27  tff(c_85, plain, ('#skF_2'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_84, c_49])).
% 2.21/1.27  tff(c_86, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_85, c_84])).
% 2.21/1.27  tff(c_169, plain, (~r1_tarski(k1_xboole_0, '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_86])).
% 2.21/1.27  tff(c_172, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_169])).
% 2.21/1.27  tff(c_173, plain, ('#skF_2'!='#skF_1'), inference(splitRight, [status(thm)], [c_47])).
% 2.21/1.27  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.21/1.27  tff(c_18, plain, (![A_10, B_11]: (m1_subset_1(k3_subset_1(A_10, B_11), k1_zfmisc_1(A_10)) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.21/1.27  tff(c_174, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_47])).
% 2.21/1.27  tff(c_238, plain, (![A_56, B_57]: (k3_subset_1(A_56, k3_subset_1(A_56, B_57))=B_57 | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.21/1.27  tff(c_245, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_34, c_238])).
% 2.21/1.27  tff(c_32, plain, (![A_23, B_24]: (k1_subset_1(A_23)=B_24 | ~r1_tarski(B_24, k3_subset_1(A_23, B_24)) | ~m1_subset_1(B_24, k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.21/1.27  tff(c_284, plain, (![B_61, A_62]: (k1_xboole_0=B_61 | ~r1_tarski(B_61, k3_subset_1(A_62, B_61)) | ~m1_subset_1(B_61, k1_zfmisc_1(A_62)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_32])).
% 2.21/1.27  tff(c_287, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_245, c_284])).
% 2.21/1.27  tff(c_299, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0 | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_287])).
% 2.21/1.27  tff(c_312, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_299])).
% 2.21/1.27  tff(c_315, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_312])).
% 2.21/1.27  tff(c_319, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_315])).
% 2.21/1.27  tff(c_320, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_299])).
% 2.21/1.27  tff(c_322, plain, (k3_subset_1('#skF_1', k1_xboole_0)='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_320, c_245])).
% 2.21/1.27  tff(c_326, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_322])).
% 2.21/1.27  tff(c_328, plain, $false, inference(negUnitSimplification, [status(thm)], [c_173, c_326])).
% 2.21/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.27  
% 2.21/1.27  Inference rules
% 2.21/1.27  ----------------------
% 2.21/1.27  #Ref     : 0
% 2.21/1.27  #Sup     : 54
% 2.21/1.27  #Fact    : 0
% 2.21/1.27  #Define  : 0
% 2.21/1.27  #Split   : 3
% 2.21/1.27  #Chain   : 0
% 2.21/1.27  #Close   : 0
% 2.21/1.27  
% 2.21/1.27  Ordering : KBO
% 2.21/1.27  
% 2.21/1.27  Simplification rules
% 2.21/1.27  ----------------------
% 2.21/1.27  #Subsume      : 1
% 2.21/1.27  #Demod        : 48
% 2.21/1.27  #Tautology    : 39
% 2.21/1.27  #SimpNegUnit  : 3
% 2.21/1.27  #BackRed      : 7
% 2.21/1.27  
% 2.21/1.27  #Partial instantiations: 0
% 2.21/1.27  #Strategies tried      : 1
% 2.21/1.27  
% 2.21/1.27  Timing (in seconds)
% 2.21/1.27  ----------------------
% 2.21/1.27  Preprocessing        : 0.28
% 2.21/1.27  Parsing              : 0.15
% 2.21/1.27  CNF conversion       : 0.02
% 2.21/1.27  Main loop            : 0.20
% 2.21/1.27  Inferencing          : 0.06
% 2.21/1.27  Reduction            : 0.07
% 2.21/1.27  Demodulation         : 0.06
% 2.21/1.27  BG Simplification    : 0.01
% 2.21/1.27  Subsumption          : 0.04
% 2.21/1.27  Abstraction          : 0.01
% 2.21/1.27  MUC search           : 0.00
% 2.21/1.27  Cooper               : 0.00
% 2.21/1.27  Total                : 0.52
% 2.21/1.27  Index Insertion      : 0.00
% 2.21/1.27  Index Deletion       : 0.00
% 2.21/1.27  Index Matching       : 0.00
% 2.21/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
