%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:43 EST 2020

% Result     : Theorem 7.01s
% Output     : CNFRefutation 7.01s
% Verified   : 
% Statistics : Number of formulae       :   51 (  59 expanded)
%              Number of leaves         :   25 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   58 (  75 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,k2_zfmisc_1(C,D))
          & r1_tarski(B,k2_zfmisc_1(E,F)) )
       => r1_tarski(k2_xboole_0(A,B),k2_zfmisc_1(k2_xboole_0(C,E),k2_xboole_0(D,F))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).

tff(c_1497,plain,(
    ! [C_133,A_134,B_135] : k2_xboole_0(k2_zfmisc_1(C_133,A_134),k2_zfmisc_1(C_133,B_135)) = k2_zfmisc_1(C_133,k2_xboole_0(A_134,B_135)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_36,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_49,plain,(
    ! [A_36,B_37] :
      ( k2_xboole_0(A_36,B_37) = B_37
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_64,plain,(
    k2_xboole_0('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_49])).

tff(c_22,plain,(
    ! [A_21,B_22] : r1_tarski(A_21,k2_xboole_0(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_79,plain,(
    ! [A_39,C_40,B_41] :
      ( r1_tarski(A_39,C_40)
      | ~ r1_tarski(k2_xboole_0(A_39,B_41),C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_91,plain,(
    ! [A_39,B_41,B_22] : r1_tarski(A_39,k2_xboole_0(k2_xboole_0(A_39,B_41),B_22)) ),
    inference(resolution,[status(thm)],[c_22,c_79])).

tff(c_318,plain,(
    ! [B_22] : r1_tarski('#skF_1',k2_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),B_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_91])).

tff(c_1557,plain,(
    ! [B_135] : r1_tarski('#skF_1',k2_zfmisc_1('#skF_3',k2_xboole_0('#skF_4',B_135))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1497,c_318])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_120,plain,(
    ! [A_50,B_51,C_52] :
      ( r1_tarski(A_50,B_51)
      | ~ r1_tarski(A_50,k4_xboole_0(B_51,C_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_125,plain,(
    ! [B_51,C_52] : r1_tarski(k4_xboole_0(B_51,C_52),B_51) ),
    inference(resolution,[status(thm)],[c_6,c_120])).

tff(c_801,plain,(
    ! [A_101,B_102,C_103] :
      ( r1_tarski(A_101,k2_xboole_0(B_102,C_103))
      | ~ r1_tarski(k4_xboole_0(A_101,B_102),C_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_861,plain,(
    ! [B_104,C_105] : r1_tarski(B_104,k2_xboole_0(C_105,B_104)) ),
    inference(resolution,[status(thm)],[c_125,c_801])).

tff(c_34,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_63,plain,(
    k2_xboole_0('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) = k2_zfmisc_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_49])).

tff(c_12,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(k2_xboole_0(A_6,B_7),C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_226,plain,(
    ! [C_8] :
      ( r1_tarski('#skF_2',C_8)
      | ~ r1_tarski(k2_zfmisc_1('#skF_5','#skF_6'),C_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_12])).

tff(c_904,plain,(
    ! [C_105] : r1_tarski('#skF_2',k2_xboole_0(C_105,k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_861,c_226])).

tff(c_1525,plain,(
    ! [A_134] : r1_tarski('#skF_2',k2_zfmisc_1('#skF_5',k2_xboole_0(A_134,'#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1497,c_904])).

tff(c_28,plain,(
    ! [A_28,C_30,B_29] : k2_xboole_0(k2_zfmisc_1(A_28,C_30),k2_zfmisc_1(B_29,C_30)) = k2_zfmisc_1(k2_xboole_0(A_28,B_29),C_30) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2099,plain,(
    ! [A_150,C_151,B_152,D_153] :
      ( r1_tarski(k2_xboole_0(A_150,C_151),k2_xboole_0(B_152,D_153))
      | ~ r1_tarski(C_151,D_153)
      | ~ r1_tarski(A_150,B_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8788,plain,(
    ! [C_375,A_374,C_373,A_377,B_376] :
      ( r1_tarski(k2_xboole_0(A_377,C_373),k2_zfmisc_1(k2_xboole_0(A_374,B_376),C_375))
      | ~ r1_tarski(C_373,k2_zfmisc_1(B_376,C_375))
      | ~ r1_tarski(A_377,k2_zfmisc_1(A_374,C_375)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2099])).

tff(c_32,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_8806,plain,
    ( ~ r1_tarski('#skF_2',k2_zfmisc_1('#skF_5',k2_xboole_0('#skF_4','#skF_6')))
    | ~ r1_tarski('#skF_1',k2_zfmisc_1('#skF_3',k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_8788,c_32])).

tff(c_8899,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1557,c_1525,c_8806])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:32:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.01/2.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.01/2.71  
% 7.01/2.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.01/2.71  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.01/2.71  
% 7.01/2.71  %Foreground sorts:
% 7.01/2.71  
% 7.01/2.71  
% 7.01/2.71  %Background operators:
% 7.01/2.71  
% 7.01/2.71  
% 7.01/2.71  %Foreground operators:
% 7.01/2.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.01/2.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.01/2.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.01/2.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.01/2.71  tff('#skF_5', type, '#skF_5': $i).
% 7.01/2.71  tff('#skF_6', type, '#skF_6': $i).
% 7.01/2.71  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.01/2.71  tff('#skF_2', type, '#skF_2': $i).
% 7.01/2.71  tff('#skF_3', type, '#skF_3': $i).
% 7.01/2.71  tff('#skF_1', type, '#skF_1': $i).
% 7.01/2.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.01/2.71  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.01/2.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.01/2.71  tff('#skF_4', type, '#skF_4': $i).
% 7.01/2.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.01/2.71  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.01/2.71  
% 7.01/2.72  tff(f_73, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 7.01/2.72  tff(f_80, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 7.01/2.72  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.01/2.72  tff(f_63, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.01/2.72  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 7.01/2.72  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.01/2.72  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 7.01/2.72  tff(f_61, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 7.01/2.72  tff(f_51, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_xboole_1)).
% 7.01/2.72  tff(c_1497, plain, (![C_133, A_134, B_135]: (k2_xboole_0(k2_zfmisc_1(C_133, A_134), k2_zfmisc_1(C_133, B_135))=k2_zfmisc_1(C_133, k2_xboole_0(A_134, B_135)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.01/2.72  tff(c_36, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.01/2.72  tff(c_49, plain, (![A_36, B_37]: (k2_xboole_0(A_36, B_37)=B_37 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.01/2.72  tff(c_64, plain, (k2_xboole_0('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_36, c_49])).
% 7.01/2.72  tff(c_22, plain, (![A_21, B_22]: (r1_tarski(A_21, k2_xboole_0(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.01/2.72  tff(c_79, plain, (![A_39, C_40, B_41]: (r1_tarski(A_39, C_40) | ~r1_tarski(k2_xboole_0(A_39, B_41), C_40))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.01/2.72  tff(c_91, plain, (![A_39, B_41, B_22]: (r1_tarski(A_39, k2_xboole_0(k2_xboole_0(A_39, B_41), B_22)))), inference(resolution, [status(thm)], [c_22, c_79])).
% 7.01/2.72  tff(c_318, plain, (![B_22]: (r1_tarski('#skF_1', k2_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), B_22)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_91])).
% 7.01/2.72  tff(c_1557, plain, (![B_135]: (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', k2_xboole_0('#skF_4', B_135))))), inference(superposition, [status(thm), theory('equality')], [c_1497, c_318])).
% 7.01/2.72  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.01/2.72  tff(c_120, plain, (![A_50, B_51, C_52]: (r1_tarski(A_50, B_51) | ~r1_tarski(A_50, k4_xboole_0(B_51, C_52)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.01/2.72  tff(c_125, plain, (![B_51, C_52]: (r1_tarski(k4_xboole_0(B_51, C_52), B_51))), inference(resolution, [status(thm)], [c_6, c_120])).
% 7.01/2.72  tff(c_801, plain, (![A_101, B_102, C_103]: (r1_tarski(A_101, k2_xboole_0(B_102, C_103)) | ~r1_tarski(k4_xboole_0(A_101, B_102), C_103))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.01/2.72  tff(c_861, plain, (![B_104, C_105]: (r1_tarski(B_104, k2_xboole_0(C_105, B_104)))), inference(resolution, [status(thm)], [c_125, c_801])).
% 7.01/2.72  tff(c_34, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.01/2.72  tff(c_63, plain, (k2_xboole_0('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))=k2_zfmisc_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_34, c_49])).
% 7.01/2.72  tff(c_12, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(k2_xboole_0(A_6, B_7), C_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.01/2.72  tff(c_226, plain, (![C_8]: (r1_tarski('#skF_2', C_8) | ~r1_tarski(k2_zfmisc_1('#skF_5', '#skF_6'), C_8))), inference(superposition, [status(thm), theory('equality')], [c_63, c_12])).
% 7.01/2.72  tff(c_904, plain, (![C_105]: (r1_tarski('#skF_2', k2_xboole_0(C_105, k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(resolution, [status(thm)], [c_861, c_226])).
% 7.01/2.72  tff(c_1525, plain, (![A_134]: (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', k2_xboole_0(A_134, '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_1497, c_904])).
% 7.01/2.72  tff(c_28, plain, (![A_28, C_30, B_29]: (k2_xboole_0(k2_zfmisc_1(A_28, C_30), k2_zfmisc_1(B_29, C_30))=k2_zfmisc_1(k2_xboole_0(A_28, B_29), C_30))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.01/2.72  tff(c_2099, plain, (![A_150, C_151, B_152, D_153]: (r1_tarski(k2_xboole_0(A_150, C_151), k2_xboole_0(B_152, D_153)) | ~r1_tarski(C_151, D_153) | ~r1_tarski(A_150, B_152))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.01/2.72  tff(c_8788, plain, (![C_375, A_374, C_373, A_377, B_376]: (r1_tarski(k2_xboole_0(A_377, C_373), k2_zfmisc_1(k2_xboole_0(A_374, B_376), C_375)) | ~r1_tarski(C_373, k2_zfmisc_1(B_376, C_375)) | ~r1_tarski(A_377, k2_zfmisc_1(A_374, C_375)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2099])).
% 7.01/2.72  tff(c_32, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.01/2.72  tff(c_8806, plain, (~r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', k2_xboole_0('#skF_4', '#skF_6'))) | ~r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', k2_xboole_0('#skF_4', '#skF_6')))), inference(resolution, [status(thm)], [c_8788, c_32])).
% 7.01/2.72  tff(c_8899, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1557, c_1525, c_8806])).
% 7.01/2.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.01/2.72  
% 7.01/2.72  Inference rules
% 7.01/2.72  ----------------------
% 7.01/2.72  #Ref     : 0
% 7.01/2.72  #Sup     : 2193
% 7.01/2.72  #Fact    : 0
% 7.01/2.72  #Define  : 0
% 7.01/2.72  #Split   : 3
% 7.01/2.72  #Chain   : 0
% 7.01/2.72  #Close   : 0
% 7.01/2.72  
% 7.01/2.72  Ordering : KBO
% 7.01/2.72  
% 7.01/2.72  Simplification rules
% 7.01/2.72  ----------------------
% 7.01/2.72  #Subsume      : 97
% 7.01/2.72  #Demod        : 923
% 7.01/2.72  #Tautology    : 869
% 7.01/2.72  #SimpNegUnit  : 0
% 7.01/2.72  #BackRed      : 0
% 7.01/2.72  
% 7.01/2.72  #Partial instantiations: 0
% 7.01/2.72  #Strategies tried      : 1
% 7.01/2.72  
% 7.01/2.72  Timing (in seconds)
% 7.01/2.72  ----------------------
% 7.01/2.72  Preprocessing        : 0.37
% 7.01/2.72  Parsing              : 0.22
% 7.01/2.72  CNF conversion       : 0.02
% 7.01/2.72  Main loop            : 1.54
% 7.01/2.72  Inferencing          : 0.40
% 7.01/2.72  Reduction            : 0.66
% 7.01/2.72  Demodulation         : 0.55
% 7.01/2.72  BG Simplification    : 0.05
% 7.01/2.72  Subsumption          : 0.33
% 7.01/2.72  Abstraction          : 0.07
% 7.01/2.72  MUC search           : 0.00
% 7.01/2.72  Cooper               : 0.00
% 7.01/2.72  Total                : 1.94
% 7.01/2.72  Index Insertion      : 0.00
% 7.01/2.72  Index Deletion       : 0.00
% 7.01/2.72  Index Matching       : 0.00
% 7.01/2.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
