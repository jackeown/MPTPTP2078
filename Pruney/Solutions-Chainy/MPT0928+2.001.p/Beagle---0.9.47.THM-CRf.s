%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:24 EST 2020

% Result     : Theorem 53.66s
% Output     : CNFRefutation 53.66s
% Verified   : 
% Statistics : Number of formulae       :   50 (  73 expanded)
%              Number of leaves         :   20 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :   71 ( 132 expanded)
%              Number of equality atoms :    5 (  12 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D)
          & r1_tarski(E,F)
          & r1_tarski(G,H) )
       => r1_tarski(k4_zfmisc_1(A,C,E,G),k4_zfmisc_1(B,D,F,H)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_mcart_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(c_18,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [C_6,A_4,B_5] :
      ( r1_tarski(k2_zfmisc_1(C_6,A_4),k2_zfmisc_1(C_6,B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_95,plain,(
    ! [A_32,C_33,B_34] :
      ( r1_tarski(k2_zfmisc_1(A_32,C_33),k2_zfmisc_1(B_34,C_33))
      | ~ r1_tarski(A_32,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_206,plain,(
    ! [A_55,B_56,C_57,A_58] :
      ( r1_tarski(A_55,k2_zfmisc_1(B_56,C_57))
      | ~ r1_tarski(A_55,k2_zfmisc_1(A_58,C_57))
      | ~ r1_tarski(A_58,B_56) ) ),
    inference(resolution,[status(thm)],[c_95,c_2])).

tff(c_219,plain,(
    ! [C_6,A_4,B_56,B_5] :
      ( r1_tarski(k2_zfmisc_1(C_6,A_4),k2_zfmisc_1(B_56,B_5))
      | ~ r1_tarski(C_6,B_56)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(resolution,[status(thm)],[c_4,c_206])).

tff(c_16,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] : k2_zfmisc_1(k2_zfmisc_1(A_7,B_8),C_9) = k3_zfmisc_1(A_7,B_8,C_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_102,plain,(
    ! [A_7,B_8,C_9,B_34] :
      ( r1_tarski(k3_zfmisc_1(A_7,B_8,C_9),k2_zfmisc_1(B_34,C_9))
      | ~ r1_tarski(k2_zfmisc_1(A_7,B_8),B_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_95])).

tff(c_75,plain,(
    ! [C_26,A_27,B_28] :
      ( r1_tarski(k2_zfmisc_1(C_26,A_27),k2_zfmisc_1(C_26,B_28))
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_225,plain,(
    ! [A_62,C_63,B_64,A_65] :
      ( r1_tarski(A_62,k2_zfmisc_1(C_63,B_64))
      | ~ r1_tarski(A_62,k2_zfmisc_1(C_63,A_65))
      | ~ r1_tarski(A_65,B_64) ) ),
    inference(resolution,[status(thm)],[c_75,c_2])).

tff(c_5531,plain,(
    ! [C_406,B_408,A_407,B_405,B_409] :
      ( r1_tarski(k3_zfmisc_1(A_407,B_405,C_406),k2_zfmisc_1(B_409,B_408))
      | ~ r1_tarski(C_406,B_408)
      | ~ r1_tarski(k2_zfmisc_1(A_407,B_405),B_409) ) ),
    inference(resolution,[status(thm)],[c_102,c_225])).

tff(c_5583,plain,(
    ! [C_406,A_7,A_407,B_405,B_8,C_9] :
      ( r1_tarski(k3_zfmisc_1(A_407,B_405,C_406),k3_zfmisc_1(A_7,B_8,C_9))
      | ~ r1_tarski(C_406,C_9)
      | ~ r1_tarski(k2_zfmisc_1(A_407,B_405),k2_zfmisc_1(A_7,B_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_5531])).

tff(c_14,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10,plain,(
    ! [A_10,B_11,C_12,D_13] : k2_zfmisc_1(k3_zfmisc_1(A_10,B_11,C_12),D_13) = k4_zfmisc_1(A_10,B_11,C_12,D_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_108,plain,(
    ! [A_35,B_36,C_37,D_38] : k2_zfmisc_1(k3_zfmisc_1(A_35,B_36,C_37),D_38) = k4_zfmisc_1(A_35,B_36,C_37,D_38) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_4,C_6,B_5] :
      ( r1_tarski(k2_zfmisc_1(A_4,C_6),k2_zfmisc_1(B_5,C_6))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1183,plain,(
    ! [C_143,A_141,D_144,B_142,B_145] :
      ( r1_tarski(k4_zfmisc_1(A_141,B_145,C_143,D_144),k2_zfmisc_1(B_142,D_144))
      | ~ r1_tarski(k3_zfmisc_1(A_141,B_145,C_143),B_142) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_6])).

tff(c_17805,plain,(
    ! [D_869,C_870,A_867,A_868,B_866,C_864,B_865] :
      ( r1_tarski(k4_zfmisc_1(A_867,B_865,C_864,D_869),k4_zfmisc_1(A_868,B_866,C_870,D_869))
      | ~ r1_tarski(k3_zfmisc_1(A_867,B_865,C_864),k3_zfmisc_1(A_868,B_866,C_870)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1183])).

tff(c_229,plain,(
    ! [B_11,A_10,C_12,B_64,D_13,A_62] :
      ( r1_tarski(A_62,k2_zfmisc_1(k3_zfmisc_1(A_10,B_11,C_12),B_64))
      | ~ r1_tarski(A_62,k4_zfmisc_1(A_10,B_11,C_12,D_13))
      | ~ r1_tarski(D_13,B_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_225])).

tff(c_237,plain,(
    ! [B_11,A_10,C_12,B_64,D_13,A_62] :
      ( r1_tarski(A_62,k4_zfmisc_1(A_10,B_11,C_12,B_64))
      | ~ r1_tarski(A_62,k4_zfmisc_1(A_10,B_11,C_12,D_13))
      | ~ r1_tarski(D_13,B_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_229])).

tff(c_133978,plain,(
    ! [A_2563,B_2564,B_2561,C_2562,B_2566,D_2565,C_2560,A_2559] :
      ( r1_tarski(k4_zfmisc_1(A_2563,B_2564,C_2562,D_2565),k4_zfmisc_1(A_2559,B_2566,C_2560,B_2561))
      | ~ r1_tarski(D_2565,B_2561)
      | ~ r1_tarski(k3_zfmisc_1(A_2563,B_2564,C_2562),k3_zfmisc_1(A_2559,B_2566,C_2560)) ) ),
    inference(resolution,[status(thm)],[c_17805,c_237])).

tff(c_12,plain,(
    ~ r1_tarski(k4_zfmisc_1('#skF_1','#skF_3','#skF_5','#skF_7'),k4_zfmisc_1('#skF_2','#skF_4','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_134095,plain,
    ( ~ r1_tarski('#skF_7','#skF_8')
    | ~ r1_tarski(k3_zfmisc_1('#skF_1','#skF_3','#skF_5'),k3_zfmisc_1('#skF_2','#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_133978,c_12])).

tff(c_134169,plain,(
    ~ r1_tarski(k3_zfmisc_1('#skF_1','#skF_3','#skF_5'),k3_zfmisc_1('#skF_2','#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_134095])).

tff(c_134177,plain,
    ( ~ r1_tarski('#skF_5','#skF_6')
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_3'),k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_5583,c_134169])).

tff(c_134180,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_3'),k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_134177])).

tff(c_134240,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_219,c_134180])).

tff(c_134283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_134240])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:41:52 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 53.66/43.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 53.66/43.86  
% 53.66/43.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 53.66/43.86  %$ r1_tarski > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 53.66/43.86  
% 53.66/43.86  %Foreground sorts:
% 53.66/43.86  
% 53.66/43.86  
% 53.66/43.86  %Background operators:
% 53.66/43.86  
% 53.66/43.86  
% 53.66/43.86  %Foreground operators:
% 53.66/43.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 53.66/43.86  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 53.66/43.86  tff('#skF_7', type, '#skF_7': $i).
% 53.66/43.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 53.66/43.86  tff('#skF_5', type, '#skF_5': $i).
% 53.66/43.86  tff('#skF_6', type, '#skF_6': $i).
% 53.66/43.86  tff('#skF_2', type, '#skF_2': $i).
% 53.66/43.86  tff('#skF_3', type, '#skF_3': $i).
% 53.66/43.86  tff('#skF_1', type, '#skF_1': $i).
% 53.66/43.86  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 53.66/43.86  tff('#skF_8', type, '#skF_8': $i).
% 53.66/43.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 53.66/43.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 53.66/43.86  tff('#skF_4', type, '#skF_4': $i).
% 53.66/43.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 53.66/43.86  
% 53.66/43.87  tff(f_52, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: ((((r1_tarski(A, B) & r1_tarski(C, D)) & r1_tarski(E, F)) & r1_tarski(G, H)) => r1_tarski(k4_zfmisc_1(A, C, E, G), k4_zfmisc_1(B, D, F, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_mcart_1)).
% 53.66/43.87  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 53.66/43.87  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 53.66/43.87  tff(f_39, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 53.66/43.87  tff(f_41, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 53.66/43.87  tff(c_18, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_52])).
% 53.66/43.87  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 53.66/43.87  tff(c_4, plain, (![C_6, A_4, B_5]: (r1_tarski(k2_zfmisc_1(C_6, A_4), k2_zfmisc_1(C_6, B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 53.66/43.87  tff(c_95, plain, (![A_32, C_33, B_34]: (r1_tarski(k2_zfmisc_1(A_32, C_33), k2_zfmisc_1(B_34, C_33)) | ~r1_tarski(A_32, B_34))), inference(cnfTransformation, [status(thm)], [f_37])).
% 53.66/43.87  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 53.66/43.87  tff(c_206, plain, (![A_55, B_56, C_57, A_58]: (r1_tarski(A_55, k2_zfmisc_1(B_56, C_57)) | ~r1_tarski(A_55, k2_zfmisc_1(A_58, C_57)) | ~r1_tarski(A_58, B_56))), inference(resolution, [status(thm)], [c_95, c_2])).
% 53.66/43.87  tff(c_219, plain, (![C_6, A_4, B_56, B_5]: (r1_tarski(k2_zfmisc_1(C_6, A_4), k2_zfmisc_1(B_56, B_5)) | ~r1_tarski(C_6, B_56) | ~r1_tarski(A_4, B_5))), inference(resolution, [status(thm)], [c_4, c_206])).
% 53.66/43.87  tff(c_16, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_52])).
% 53.66/43.87  tff(c_8, plain, (![A_7, B_8, C_9]: (k2_zfmisc_1(k2_zfmisc_1(A_7, B_8), C_9)=k3_zfmisc_1(A_7, B_8, C_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 53.66/43.87  tff(c_102, plain, (![A_7, B_8, C_9, B_34]: (r1_tarski(k3_zfmisc_1(A_7, B_8, C_9), k2_zfmisc_1(B_34, C_9)) | ~r1_tarski(k2_zfmisc_1(A_7, B_8), B_34))), inference(superposition, [status(thm), theory('equality')], [c_8, c_95])).
% 53.66/43.87  tff(c_75, plain, (![C_26, A_27, B_28]: (r1_tarski(k2_zfmisc_1(C_26, A_27), k2_zfmisc_1(C_26, B_28)) | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_37])).
% 53.66/43.87  tff(c_225, plain, (![A_62, C_63, B_64, A_65]: (r1_tarski(A_62, k2_zfmisc_1(C_63, B_64)) | ~r1_tarski(A_62, k2_zfmisc_1(C_63, A_65)) | ~r1_tarski(A_65, B_64))), inference(resolution, [status(thm)], [c_75, c_2])).
% 53.66/43.87  tff(c_5531, plain, (![C_406, B_408, A_407, B_405, B_409]: (r1_tarski(k3_zfmisc_1(A_407, B_405, C_406), k2_zfmisc_1(B_409, B_408)) | ~r1_tarski(C_406, B_408) | ~r1_tarski(k2_zfmisc_1(A_407, B_405), B_409))), inference(resolution, [status(thm)], [c_102, c_225])).
% 53.66/43.87  tff(c_5583, plain, (![C_406, A_7, A_407, B_405, B_8, C_9]: (r1_tarski(k3_zfmisc_1(A_407, B_405, C_406), k3_zfmisc_1(A_7, B_8, C_9)) | ~r1_tarski(C_406, C_9) | ~r1_tarski(k2_zfmisc_1(A_407, B_405), k2_zfmisc_1(A_7, B_8)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_5531])).
% 53.66/43.87  tff(c_14, plain, (r1_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_52])).
% 53.66/43.87  tff(c_10, plain, (![A_10, B_11, C_12, D_13]: (k2_zfmisc_1(k3_zfmisc_1(A_10, B_11, C_12), D_13)=k4_zfmisc_1(A_10, B_11, C_12, D_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 53.66/43.87  tff(c_108, plain, (![A_35, B_36, C_37, D_38]: (k2_zfmisc_1(k3_zfmisc_1(A_35, B_36, C_37), D_38)=k4_zfmisc_1(A_35, B_36, C_37, D_38))), inference(cnfTransformation, [status(thm)], [f_41])).
% 53.66/43.87  tff(c_6, plain, (![A_4, C_6, B_5]: (r1_tarski(k2_zfmisc_1(A_4, C_6), k2_zfmisc_1(B_5, C_6)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 53.66/43.87  tff(c_1183, plain, (![C_143, A_141, D_144, B_142, B_145]: (r1_tarski(k4_zfmisc_1(A_141, B_145, C_143, D_144), k2_zfmisc_1(B_142, D_144)) | ~r1_tarski(k3_zfmisc_1(A_141, B_145, C_143), B_142))), inference(superposition, [status(thm), theory('equality')], [c_108, c_6])).
% 53.66/43.87  tff(c_17805, plain, (![D_869, C_870, A_867, A_868, B_866, C_864, B_865]: (r1_tarski(k4_zfmisc_1(A_867, B_865, C_864, D_869), k4_zfmisc_1(A_868, B_866, C_870, D_869)) | ~r1_tarski(k3_zfmisc_1(A_867, B_865, C_864), k3_zfmisc_1(A_868, B_866, C_870)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1183])).
% 53.66/43.87  tff(c_229, plain, (![B_11, A_10, C_12, B_64, D_13, A_62]: (r1_tarski(A_62, k2_zfmisc_1(k3_zfmisc_1(A_10, B_11, C_12), B_64)) | ~r1_tarski(A_62, k4_zfmisc_1(A_10, B_11, C_12, D_13)) | ~r1_tarski(D_13, B_64))), inference(superposition, [status(thm), theory('equality')], [c_10, c_225])).
% 53.66/43.87  tff(c_237, plain, (![B_11, A_10, C_12, B_64, D_13, A_62]: (r1_tarski(A_62, k4_zfmisc_1(A_10, B_11, C_12, B_64)) | ~r1_tarski(A_62, k4_zfmisc_1(A_10, B_11, C_12, D_13)) | ~r1_tarski(D_13, B_64))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_229])).
% 53.66/43.87  tff(c_133978, plain, (![A_2563, B_2564, B_2561, C_2562, B_2566, D_2565, C_2560, A_2559]: (r1_tarski(k4_zfmisc_1(A_2563, B_2564, C_2562, D_2565), k4_zfmisc_1(A_2559, B_2566, C_2560, B_2561)) | ~r1_tarski(D_2565, B_2561) | ~r1_tarski(k3_zfmisc_1(A_2563, B_2564, C_2562), k3_zfmisc_1(A_2559, B_2566, C_2560)))), inference(resolution, [status(thm)], [c_17805, c_237])).
% 53.66/43.87  tff(c_12, plain, (~r1_tarski(k4_zfmisc_1('#skF_1', '#skF_3', '#skF_5', '#skF_7'), k4_zfmisc_1('#skF_2', '#skF_4', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 53.66/43.87  tff(c_134095, plain, (~r1_tarski('#skF_7', '#skF_8') | ~r1_tarski(k3_zfmisc_1('#skF_1', '#skF_3', '#skF_5'), k3_zfmisc_1('#skF_2', '#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_133978, c_12])).
% 53.66/43.87  tff(c_134169, plain, (~r1_tarski(k3_zfmisc_1('#skF_1', '#skF_3', '#skF_5'), k3_zfmisc_1('#skF_2', '#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_134095])).
% 53.66/43.87  tff(c_134177, plain, (~r1_tarski('#skF_5', '#skF_6') | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_3'), k2_zfmisc_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_5583, c_134169])).
% 53.66/43.87  tff(c_134180, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_3'), k2_zfmisc_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_134177])).
% 53.66/43.87  tff(c_134240, plain, (~r1_tarski('#skF_1', '#skF_2') | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_219, c_134180])).
% 53.66/43.87  tff(c_134283, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_134240])).
% 53.66/43.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 53.66/43.87  
% 53.66/43.87  Inference rules
% 53.66/43.87  ----------------------
% 53.66/43.87  #Ref     : 0
% 53.66/43.87  #Sup     : 40888
% 53.66/43.87  #Fact    : 0
% 53.66/43.87  #Define  : 0
% 53.66/43.87  #Split   : 41
% 53.66/43.87  #Chain   : 0
% 53.66/43.87  #Close   : 0
% 53.66/43.87  
% 53.66/43.87  Ordering : KBO
% 53.66/43.87  
% 53.66/43.87  Simplification rules
% 53.66/43.87  ----------------------
% 53.66/43.87  #Subsume      : 8267
% 53.66/43.87  #Demod        : 10771
% 53.66/43.87  #Tautology    : 23
% 53.66/43.87  #SimpNegUnit  : 0
% 53.66/43.87  #BackRed      : 0
% 53.66/43.87  
% 53.66/43.87  #Partial instantiations: 0
% 53.66/43.87  #Strategies tried      : 1
% 53.66/43.87  
% 53.66/43.87  Timing (in seconds)
% 53.66/43.87  ----------------------
% 53.66/43.88  Preprocessing        : 0.28
% 53.66/43.88  Parsing              : 0.16
% 53.66/43.88  CNF conversion       : 0.02
% 53.66/43.88  Main loop            : 42.79
% 53.66/43.88  Inferencing          : 2.64
% 53.66/43.88  Reduction            : 5.23
% 53.66/43.88  Demodulation         : 3.36
% 53.66/43.88  BG Simplification    : 0.50
% 53.66/43.88  Subsumption          : 32.46
% 53.66/43.88  Abstraction          : 0.63
% 53.66/43.88  MUC search           : 0.00
% 53.66/43.88  Cooper               : 0.00
% 53.66/43.88  Total                : 43.09
% 53.66/43.88  Index Insertion      : 0.00
% 53.66/43.88  Index Deletion       : 0.00
% 53.66/43.88  Index Matching       : 0.00
% 53.66/43.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
