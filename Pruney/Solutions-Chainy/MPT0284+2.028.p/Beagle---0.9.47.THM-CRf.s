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
% DateTime   : Thu Dec  3 09:53:30 EST 2020

% Result     : Theorem 4.34s
% Output     : CNFRefutation 4.34s
% Verified   : 
% Statistics : Number of formulae       :   44 (  51 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 (  68 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k5_xboole_0(B,C))
    <=> ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A,B)),k1_zfmisc_1(k4_xboole_0(B,A))),k1_zfmisc_1(k5_xboole_0(A,B))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_zfmisc_1)).

tff(c_18,plain,(
    ! [A_15,B_16] : r1_tarski(k4_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(A_7,k2_xboole_0(C_9,B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_tarski(k3_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_91,plain,(
    ! [C_65,B_66,A_67] :
      ( r1_tarski(k4_xboole_0(C_65,B_66),k4_xboole_0(C_65,A_67))
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_xboole_0(A_1,C_3)
      | ~ r1_tarski(A_1,k4_xboole_0(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_100,plain,(
    ! [C_65,B_66,A_67] :
      ( r1_xboole_0(k4_xboole_0(C_65,B_66),A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(resolution,[status(thm)],[c_91,c_2])).

tff(c_173,plain,(
    ! [A_96,B_97,C_98] :
      ( r1_tarski(A_96,k5_xboole_0(B_97,C_98))
      | ~ r1_xboole_0(A_96,k3_xboole_0(B_97,C_98))
      | ~ r1_tarski(A_96,k2_xboole_0(B_97,C_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1945,plain,(
    ! [C_374,B_375,B_376,C_377] :
      ( r1_tarski(k4_xboole_0(C_374,B_375),k5_xboole_0(B_376,C_377))
      | ~ r1_tarski(k4_xboole_0(C_374,B_375),k2_xboole_0(B_376,C_377))
      | ~ r1_tarski(k3_xboole_0(B_376,C_377),B_375) ) ),
    inference(resolution,[status(thm)],[c_100,c_173])).

tff(c_24,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(k1_zfmisc_1(A_22),k1_zfmisc_1(B_23))
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    ! [A_20,B_21] : r1_tarski(k4_xboole_0(A_20,B_21),k5_xboole_0(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_152,plain,(
    ! [A_89,C_90,B_91] :
      ( r1_tarski(k2_xboole_0(A_89,C_90),B_91)
      | ~ r1_tarski(C_90,B_91)
      | ~ r1_tarski(A_89,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1'))),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_169,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_152,c_26])).

tff(c_226,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_229,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_226])).

tff(c_233,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_229])).

tff(c_234,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_239,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_2','#skF_1'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_234])).

tff(c_1956,plain,
    ( ~ r1_tarski(k4_xboole_0('#skF_2','#skF_1'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1945,c_239])).

tff(c_1968,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_2','#skF_1'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1956])).

tff(c_1972,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_2','#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_1968])).

tff(c_1976,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1972])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:56:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.34/1.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.34/1.76  
% 4.34/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.34/1.77  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_1
% 4.34/1.77  
% 4.34/1.77  %Foreground sorts:
% 4.34/1.77  
% 4.34/1.77  
% 4.34/1.77  %Background operators:
% 4.34/1.77  
% 4.34/1.77  
% 4.34/1.77  %Foreground operators:
% 4.34/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.34/1.77  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.34/1.77  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.34/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.34/1.77  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.34/1.77  tff('#skF_2', type, '#skF_2': $i).
% 4.34/1.77  tff('#skF_1', type, '#skF_1': $i).
% 4.34/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.34/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.34/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.34/1.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.34/1.77  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.34/1.77  
% 4.34/1.78  tff(f_49, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.34/1.78  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 4.34/1.78  tff(f_43, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.34/1.78  tff(f_47, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_xboole_1)).
% 4.34/1.78  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 4.34/1.78  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k5_xboole_0(B, C)) <=> (r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, k3_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_xboole_1)).
% 4.34/1.78  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 4.34/1.78  tff(f_57, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_xboole_1)).
% 4.34/1.78  tff(f_55, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 4.34/1.78  tff(f_64, negated_conjecture, ~(![A, B]: r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A, B)), k1_zfmisc_1(k4_xboole_0(B, A))), k1_zfmisc_1(k5_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_zfmisc_1)).
% 4.34/1.78  tff(c_18, plain, (![A_15, B_16]: (r1_tarski(k4_xboole_0(A_15, B_16), A_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.34/1.78  tff(c_12, plain, (![A_7, C_9, B_8]: (r1_tarski(A_7, k2_xboole_0(C_9, B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.34/1.78  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(k3_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.34/1.78  tff(c_91, plain, (![C_65, B_66, A_67]: (r1_tarski(k4_xboole_0(C_65, B_66), k4_xboole_0(C_65, A_67)) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.34/1.78  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_xboole_0(A_1, C_3) | ~r1_tarski(A_1, k4_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.34/1.78  tff(c_100, plain, (![C_65, B_66, A_67]: (r1_xboole_0(k4_xboole_0(C_65, B_66), A_67) | ~r1_tarski(A_67, B_66))), inference(resolution, [status(thm)], [c_91, c_2])).
% 4.34/1.78  tff(c_173, plain, (![A_96, B_97, C_98]: (r1_tarski(A_96, k5_xboole_0(B_97, C_98)) | ~r1_xboole_0(A_96, k3_xboole_0(B_97, C_98)) | ~r1_tarski(A_96, k2_xboole_0(B_97, C_98)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.34/1.78  tff(c_1945, plain, (![C_374, B_375, B_376, C_377]: (r1_tarski(k4_xboole_0(C_374, B_375), k5_xboole_0(B_376, C_377)) | ~r1_tarski(k4_xboole_0(C_374, B_375), k2_xboole_0(B_376, C_377)) | ~r1_tarski(k3_xboole_0(B_376, C_377), B_375))), inference(resolution, [status(thm)], [c_100, c_173])).
% 4.34/1.78  tff(c_24, plain, (![A_22, B_23]: (r1_tarski(k1_zfmisc_1(A_22), k1_zfmisc_1(B_23)) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.34/1.78  tff(c_22, plain, (![A_20, B_21]: (r1_tarski(k4_xboole_0(A_20, B_21), k5_xboole_0(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.34/1.78  tff(c_152, plain, (![A_89, C_90, B_91]: (r1_tarski(k2_xboole_0(A_89, C_90), B_91) | ~r1_tarski(C_90, B_91) | ~r1_tarski(A_89, B_91))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.34/1.78  tff(c_26, plain, (~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1'))), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.34/1.78  tff(c_169, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2'))) | ~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_152, c_26])).
% 4.34/1.78  tff(c_226, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_169])).
% 4.34/1.78  tff(c_229, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_226])).
% 4.34/1.78  tff(c_233, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_229])).
% 4.34/1.78  tff(c_234, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_169])).
% 4.34/1.78  tff(c_239, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_1'), k5_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_234])).
% 4.34/1.78  tff(c_1956, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_1'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_1945, c_239])).
% 4.34/1.78  tff(c_1968, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_1'), k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1956])).
% 4.34/1.78  tff(c_1972, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_12, c_1968])).
% 4.34/1.78  tff(c_1976, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_1972])).
% 4.34/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.34/1.78  
% 4.34/1.78  Inference rules
% 4.34/1.78  ----------------------
% 4.34/1.78  #Ref     : 0
% 4.34/1.78  #Sup     : 471
% 4.34/1.78  #Fact    : 0
% 4.34/1.78  #Define  : 0
% 4.34/1.78  #Split   : 1
% 4.34/1.78  #Chain   : 0
% 4.34/1.78  #Close   : 0
% 4.34/1.78  
% 4.34/1.78  Ordering : KBO
% 4.34/1.78  
% 4.34/1.78  Simplification rules
% 4.34/1.78  ----------------------
% 4.34/1.78  #Subsume      : 2
% 4.34/1.78  #Demod        : 25
% 4.34/1.78  #Tautology    : 24
% 4.34/1.78  #SimpNegUnit  : 0
% 4.34/1.78  #BackRed      : 0
% 4.34/1.78  
% 4.34/1.78  #Partial instantiations: 0
% 4.34/1.78  #Strategies tried      : 1
% 4.34/1.78  
% 4.34/1.78  Timing (in seconds)
% 4.34/1.78  ----------------------
% 4.34/1.78  Preprocessing        : 0.27
% 4.34/1.78  Parsing              : 0.16
% 4.34/1.78  CNF conversion       : 0.02
% 4.34/1.78  Main loop            : 0.71
% 4.34/1.78  Inferencing          : 0.22
% 4.34/1.78  Reduction            : 0.22
% 4.34/1.78  Demodulation         : 0.17
% 4.34/1.78  BG Simplification    : 0.02
% 4.34/1.78  Subsumption          : 0.18
% 4.34/1.78  Abstraction          : 0.03
% 4.34/1.78  MUC search           : 0.00
% 4.34/1.78  Cooper               : 0.00
% 4.34/1.78  Total                : 1.01
% 4.34/1.78  Index Insertion      : 0.00
% 4.34/1.78  Index Deletion       : 0.00
% 4.34/1.78  Index Matching       : 0.00
% 4.34/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
