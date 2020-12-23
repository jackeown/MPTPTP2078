%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:44 EST 2020

% Result     : Theorem 20.89s
% Output     : CNFRefutation 20.89s
% Verified   : 
% Statistics : Number of formulae       :   45 (  65 expanded)
%              Number of leaves         :   21 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   57 (  98 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,k2_zfmisc_1(C,D))
          & r1_tarski(B,k2_zfmisc_1(E,F)) )
       => r1_tarski(k2_xboole_0(A,B),k2_zfmisc_1(k2_xboole_0(C,E),k2_xboole_0(D,F))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_184,plain,(
    ! [A_52,B_53,C_54] :
      ( r1_tarski(A_52,k2_xboole_0(B_53,C_54))
      | ~ r1_tarski(k4_xboole_0(A_52,B_53),C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_215,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(B_12,A_11)) ),
    inference(resolution,[status(thm)],[c_14,c_184])).

tff(c_22,plain,(
    ! [A_21,C_23,B_22,D_24] :
      ( r1_tarski(k2_zfmisc_1(A_21,C_23),k2_zfmisc_1(B_22,D_24))
      | ~ r1_tarski(C_23,D_24)
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_26,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_33,plain,(
    ! [A_30,B_31] :
      ( k2_xboole_0(A_30,B_31) = B_31
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_52,plain,(
    k2_xboole_0('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) = k2_zfmisc_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_33])).

tff(c_10,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(k2_xboole_0(A_6,B_7),C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_648,plain,(
    ! [C_83] :
      ( r1_tarski('#skF_2',C_83)
      | ~ r1_tarski(k2_zfmisc_1('#skF_5','#skF_6'),C_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_10])).

tff(c_74036,plain,(
    ! [B_1205,D_1206] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(B_1205,D_1206))
      | ~ r1_tarski('#skF_6',D_1206)
      | ~ r1_tarski('#skF_5',B_1205) ) ),
    inference(resolution,[status(thm)],[c_22,c_648])).

tff(c_18,plain,(
    ! [A_16,B_17] : r1_tarski(A_16,k2_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_50,plain,(
    k2_xboole_0('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_33])).

tff(c_710,plain,(
    ! [C_87] :
      ( r1_tarski('#skF_1',C_87)
      | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),C_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_10])).

tff(c_36742,plain,(
    ! [B_651,D_652] :
      ( r1_tarski('#skF_1',k2_zfmisc_1(B_651,D_652))
      | ~ r1_tarski('#skF_4',D_652)
      | ~ r1_tarski('#skF_3',B_651) ) ),
    inference(resolution,[status(thm)],[c_22,c_710])).

tff(c_395,plain,(
    ! [A_68,C_69,B_70] :
      ( r1_tarski(k2_xboole_0(A_68,C_69),B_70)
      | ~ r1_tarski(C_69,B_70)
      | ~ r1_tarski(A_68,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_418,plain,
    ( ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6')))
    | ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_395,c_24])).

tff(c_2076,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_418])).

tff(c_36751,plain,
    ( ~ r1_tarski('#skF_4',k2_xboole_0('#skF_4','#skF_6'))
    | ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_36742,c_2076])).

tff(c_36766,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_36751])).

tff(c_36767,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_418])).

tff(c_74045,plain,
    ( ~ r1_tarski('#skF_6',k2_xboole_0('#skF_4','#skF_6'))
    | ~ r1_tarski('#skF_5',k2_xboole_0('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_74036,c_36767])).

tff(c_74060,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_215,c_74045])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:44:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.89/12.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.89/12.22  
% 20.89/12.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.89/12.22  %$ r1_tarski > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 20.89/12.22  
% 20.89/12.22  %Foreground sorts:
% 20.89/12.22  
% 20.89/12.22  
% 20.89/12.22  %Background operators:
% 20.89/12.22  
% 20.89/12.22  
% 20.89/12.22  %Foreground operators:
% 20.89/12.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.89/12.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 20.89/12.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.89/12.22  tff('#skF_5', type, '#skF_5': $i).
% 20.89/12.22  tff('#skF_6', type, '#skF_6': $i).
% 20.89/12.22  tff('#skF_2', type, '#skF_2': $i).
% 20.89/12.22  tff('#skF_3', type, '#skF_3': $i).
% 20.89/12.22  tff('#skF_1', type, '#skF_1': $i).
% 20.89/12.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.89/12.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 20.89/12.22  tff('#skF_4', type, '#skF_4': $i).
% 20.89/12.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.89/12.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 20.89/12.22  
% 20.89/12.23  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 20.89/12.23  tff(f_49, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 20.89/12.23  tff(f_63, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_zfmisc_1)).
% 20.89/12.23  tff(f_70, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 20.89/12.23  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 20.89/12.23  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 20.89/12.23  tff(f_51, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 20.89/12.23  tff(f_57, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 20.89/12.23  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 20.89/12.23  tff(c_184, plain, (![A_52, B_53, C_54]: (r1_tarski(A_52, k2_xboole_0(B_53, C_54)) | ~r1_tarski(k4_xboole_0(A_52, B_53), C_54))), inference(cnfTransformation, [status(thm)], [f_49])).
% 20.89/12.23  tff(c_215, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(B_12, A_11)))), inference(resolution, [status(thm)], [c_14, c_184])).
% 20.89/12.23  tff(c_22, plain, (![A_21, C_23, B_22, D_24]: (r1_tarski(k2_zfmisc_1(A_21, C_23), k2_zfmisc_1(B_22, D_24)) | ~r1_tarski(C_23, D_24) | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_63])).
% 20.89/12.23  tff(c_26, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 20.89/12.23  tff(c_33, plain, (![A_30, B_31]: (k2_xboole_0(A_30, B_31)=B_31 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_43])).
% 20.89/12.23  tff(c_52, plain, (k2_xboole_0('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))=k2_zfmisc_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_26, c_33])).
% 20.89/12.23  tff(c_10, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(k2_xboole_0(A_6, B_7), C_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 20.89/12.23  tff(c_648, plain, (![C_83]: (r1_tarski('#skF_2', C_83) | ~r1_tarski(k2_zfmisc_1('#skF_5', '#skF_6'), C_83))), inference(superposition, [status(thm), theory('equality')], [c_52, c_10])).
% 20.89/12.23  tff(c_74036, plain, (![B_1205, D_1206]: (r1_tarski('#skF_2', k2_zfmisc_1(B_1205, D_1206)) | ~r1_tarski('#skF_6', D_1206) | ~r1_tarski('#skF_5', B_1205))), inference(resolution, [status(thm)], [c_22, c_648])).
% 20.89/12.23  tff(c_18, plain, (![A_16, B_17]: (r1_tarski(A_16, k2_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 20.89/12.23  tff(c_28, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 20.89/12.23  tff(c_50, plain, (k2_xboole_0('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_33])).
% 20.89/12.23  tff(c_710, plain, (![C_87]: (r1_tarski('#skF_1', C_87) | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), C_87))), inference(superposition, [status(thm), theory('equality')], [c_50, c_10])).
% 20.89/12.23  tff(c_36742, plain, (![B_651, D_652]: (r1_tarski('#skF_1', k2_zfmisc_1(B_651, D_652)) | ~r1_tarski('#skF_4', D_652) | ~r1_tarski('#skF_3', B_651))), inference(resolution, [status(thm)], [c_22, c_710])).
% 20.89/12.23  tff(c_395, plain, (![A_68, C_69, B_70]: (r1_tarski(k2_xboole_0(A_68, C_69), B_70) | ~r1_tarski(C_69, B_70) | ~r1_tarski(A_68, B_70))), inference(cnfTransformation, [status(thm)], [f_57])).
% 20.89/12.23  tff(c_24, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 20.89/12.23  tff(c_418, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6'))) | ~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(resolution, [status(thm)], [c_395, c_24])).
% 20.89/12.23  tff(c_2076, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(splitLeft, [status(thm)], [c_418])).
% 20.89/12.23  tff(c_36751, plain, (~r1_tarski('#skF_4', k2_xboole_0('#skF_4', '#skF_6')) | ~r1_tarski('#skF_3', k2_xboole_0('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_36742, c_2076])).
% 20.89/12.23  tff(c_36766, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_36751])).
% 20.89/12.23  tff(c_36767, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(splitRight, [status(thm)], [c_418])).
% 20.89/12.23  tff(c_74045, plain, (~r1_tarski('#skF_6', k2_xboole_0('#skF_4', '#skF_6')) | ~r1_tarski('#skF_5', k2_xboole_0('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_74036, c_36767])).
% 20.89/12.23  tff(c_74060, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_215, c_215, c_74045])).
% 20.89/12.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.89/12.23  
% 20.89/12.23  Inference rules
% 20.89/12.23  ----------------------
% 20.89/12.23  #Ref     : 0
% 20.89/12.23  #Sup     : 18196
% 20.89/12.23  #Fact    : 0
% 20.89/12.23  #Define  : 0
% 20.89/12.23  #Split   : 7
% 20.89/12.23  #Chain   : 0
% 20.89/12.23  #Close   : 0
% 20.89/12.23  
% 20.89/12.23  Ordering : KBO
% 20.89/12.23  
% 20.89/12.23  Simplification rules
% 20.89/12.23  ----------------------
% 20.89/12.23  #Subsume      : 3173
% 20.89/12.23  #Demod        : 6528
% 20.89/12.23  #Tautology    : 5398
% 20.89/12.23  #SimpNegUnit  : 0
% 20.89/12.23  #BackRed      : 0
% 20.89/12.23  
% 20.89/12.23  #Partial instantiations: 0
% 20.89/12.23  #Strategies tried      : 1
% 20.89/12.23  
% 20.89/12.23  Timing (in seconds)
% 20.89/12.23  ----------------------
% 20.89/12.23  Preprocessing        : 0.28
% 20.89/12.23  Parsing              : 0.16
% 20.89/12.23  CNF conversion       : 0.02
% 20.89/12.23  Main loop            : 11.18
% 20.89/12.23  Inferencing          : 1.42
% 20.89/12.23  Reduction            : 5.26
% 20.89/12.23  Demodulation         : 4.70
% 20.89/12.23  BG Simplification    : 0.19
% 20.89/12.23  Subsumption          : 3.77
% 20.89/12.23  Abstraction          : 0.27
% 20.89/12.23  MUC search           : 0.00
% 20.89/12.23  Cooper               : 0.00
% 20.89/12.23  Total                : 11.49
% 20.89/12.23  Index Insertion      : 0.00
% 20.89/12.23  Index Deletion       : 0.00
% 20.89/12.24  Index Matching       : 0.00
% 20.89/12.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
