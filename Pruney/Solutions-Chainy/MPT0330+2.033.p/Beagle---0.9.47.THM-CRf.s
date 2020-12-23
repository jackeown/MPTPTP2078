%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:44 EST 2020

% Result     : Theorem 5.15s
% Output     : CNFRefutation 5.15s
% Verified   : 
% Statistics : Number of formulae       :   41 (  59 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :    5
%              Number of atoms          :   57 (  96 expanded)
%              Number of equality atoms :    0 (   0 expanded)
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

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,k2_zfmisc_1(C,D))
          & r1_tarski(B,k2_zfmisc_1(E,F)) )
       => r1_tarski(k2_xboole_0(A,B),k2_zfmisc_1(k2_xboole_0(C,E),k2_xboole_0(D,F))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_126,plain,(
    ! [A_45,B_46,C_47] :
      ( r1_tarski(A_45,k2_xboole_0(B_46,C_47))
      | ~ r1_tarski(k4_xboole_0(A_45,B_46),C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_158,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(B_7,A_6)) ),
    inference(resolution,[status(thm)],[c_10,c_126])).

tff(c_22,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_562,plain,(
    ! [A_76,C_77,B_78,D_79] :
      ( r1_tarski(k2_zfmisc_1(A_76,C_77),k2_zfmisc_1(B_78,D_79))
      | ~ r1_tarski(C_77,D_79)
      | ~ r1_tarski(A_76,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5798,plain,(
    ! [C_238,A_239,D_240,B_236,A_237] :
      ( r1_tarski(A_237,k2_zfmisc_1(B_236,D_240))
      | ~ r1_tarski(A_237,k2_zfmisc_1(A_239,C_238))
      | ~ r1_tarski(C_238,D_240)
      | ~ r1_tarski(A_239,B_236) ) ),
    inference(resolution,[status(thm)],[c_562,c_8])).

tff(c_6105,plain,(
    ! [B_257,D_258] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(B_257,D_258))
      | ~ r1_tarski('#skF_6',D_258)
      | ~ r1_tarski('#skF_5',B_257) ) ),
    inference(resolution,[status(thm)],[c_22,c_5798])).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2808,plain,(
    ! [C_141,A_142,D_143,B_139,A_140] :
      ( r1_tarski(A_140,k2_zfmisc_1(B_139,D_143))
      | ~ r1_tarski(A_140,k2_zfmisc_1(A_142,C_141))
      | ~ r1_tarski(C_141,D_143)
      | ~ r1_tarski(A_142,B_139) ) ),
    inference(resolution,[status(thm)],[c_562,c_8])).

tff(c_3501,plain,(
    ! [B_175,D_176] :
      ( r1_tarski('#skF_1',k2_zfmisc_1(B_175,D_176))
      | ~ r1_tarski('#skF_4',D_176)
      | ~ r1_tarski('#skF_3',B_175) ) ),
    inference(resolution,[status(thm)],[c_24,c_2808])).

tff(c_238,plain,(
    ! [A_64,C_65,B_66] :
      ( r1_tarski(k2_xboole_0(A_64,C_65),B_66)
      | ~ r1_tarski(C_65,B_66)
      | ~ r1_tarski(A_64,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_263,plain,
    ( ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6')))
    | ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_238,c_20])).

tff(c_645,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_263])).

tff(c_3509,plain,
    ( ~ r1_tarski('#skF_4',k2_xboole_0('#skF_4','#skF_6'))
    | ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_3501,c_645])).

tff(c_3522,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_3509])).

tff(c_3523,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_263])).

tff(c_6115,plain,
    ( ~ r1_tarski('#skF_6',k2_xboole_0('#skF_4','#skF_6'))
    | ~ r1_tarski('#skF_5',k2_xboole_0('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_6105,c_3523])).

tff(c_6130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_158,c_6115])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.09  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.08/0.28  % Computer   : n019.cluster.edu
% 0.08/0.28  % Model      : x86_64 x86_64
% 0.08/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.28  % Memory     : 8042.1875MB
% 0.08/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.28  % CPULimit   : 60
% 0.08/0.28  % DateTime   : Tue Dec  1 13:27:37 EST 2020
% 0.08/0.28  % CPUTime    : 
% 0.08/0.29  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.15/2.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.15/2.11  
% 5.15/2.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.15/2.12  %$ r1_tarski > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.15/2.12  
% 5.15/2.12  %Foreground sorts:
% 5.15/2.12  
% 5.15/2.12  
% 5.15/2.12  %Background operators:
% 5.15/2.12  
% 5.15/2.12  
% 5.15/2.12  %Foreground operators:
% 5.15/2.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.15/2.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.15/2.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.15/2.12  tff('#skF_5', type, '#skF_5': $i).
% 5.15/2.12  tff('#skF_6', type, '#skF_6': $i).
% 5.15/2.12  tff('#skF_2', type, '#skF_2': $i).
% 5.15/2.12  tff('#skF_3', type, '#skF_3': $i).
% 5.15/2.12  tff('#skF_1', type, '#skF_1': $i).
% 5.15/2.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.15/2.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.15/2.12  tff('#skF_4', type, '#skF_4': $i).
% 5.15/2.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.15/2.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.15/2.12  
% 5.15/2.13  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.15/2.13  tff(f_43, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 5.15/2.13  tff(f_64, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 5.15/2.13  tff(f_57, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_zfmisc_1)).
% 5.15/2.13  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.15/2.13  tff(f_45, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.15/2.13  tff(f_51, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 5.15/2.13  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.15/2.13  tff(c_126, plain, (![A_45, B_46, C_47]: (r1_tarski(A_45, k2_xboole_0(B_46, C_47)) | ~r1_tarski(k4_xboole_0(A_45, B_46), C_47))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.15/2.13  tff(c_158, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(B_7, A_6)))), inference(resolution, [status(thm)], [c_10, c_126])).
% 5.15/2.13  tff(c_22, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.15/2.13  tff(c_562, plain, (![A_76, C_77, B_78, D_79]: (r1_tarski(k2_zfmisc_1(A_76, C_77), k2_zfmisc_1(B_78, D_79)) | ~r1_tarski(C_77, D_79) | ~r1_tarski(A_76, B_78))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.15/2.13  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.15/2.13  tff(c_5798, plain, (![C_238, A_239, D_240, B_236, A_237]: (r1_tarski(A_237, k2_zfmisc_1(B_236, D_240)) | ~r1_tarski(A_237, k2_zfmisc_1(A_239, C_238)) | ~r1_tarski(C_238, D_240) | ~r1_tarski(A_239, B_236))), inference(resolution, [status(thm)], [c_562, c_8])).
% 5.15/2.13  tff(c_6105, plain, (![B_257, D_258]: (r1_tarski('#skF_2', k2_zfmisc_1(B_257, D_258)) | ~r1_tarski('#skF_6', D_258) | ~r1_tarski('#skF_5', B_257))), inference(resolution, [status(thm)], [c_22, c_5798])).
% 5.15/2.13  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.15/2.13  tff(c_24, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.15/2.13  tff(c_2808, plain, (![C_141, A_142, D_143, B_139, A_140]: (r1_tarski(A_140, k2_zfmisc_1(B_139, D_143)) | ~r1_tarski(A_140, k2_zfmisc_1(A_142, C_141)) | ~r1_tarski(C_141, D_143) | ~r1_tarski(A_142, B_139))), inference(resolution, [status(thm)], [c_562, c_8])).
% 5.15/2.13  tff(c_3501, plain, (![B_175, D_176]: (r1_tarski('#skF_1', k2_zfmisc_1(B_175, D_176)) | ~r1_tarski('#skF_4', D_176) | ~r1_tarski('#skF_3', B_175))), inference(resolution, [status(thm)], [c_24, c_2808])).
% 5.15/2.13  tff(c_238, plain, (![A_64, C_65, B_66]: (r1_tarski(k2_xboole_0(A_64, C_65), B_66) | ~r1_tarski(C_65, B_66) | ~r1_tarski(A_64, B_66))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.15/2.13  tff(c_20, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.15/2.13  tff(c_263, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6'))) | ~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(resolution, [status(thm)], [c_238, c_20])).
% 5.15/2.13  tff(c_645, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(splitLeft, [status(thm)], [c_263])).
% 5.15/2.13  tff(c_3509, plain, (~r1_tarski('#skF_4', k2_xboole_0('#skF_4', '#skF_6')) | ~r1_tarski('#skF_3', k2_xboole_0('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_3501, c_645])).
% 5.15/2.13  tff(c_3522, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_3509])).
% 5.15/2.13  tff(c_3523, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(splitRight, [status(thm)], [c_263])).
% 5.15/2.13  tff(c_6115, plain, (~r1_tarski('#skF_6', k2_xboole_0('#skF_4', '#skF_6')) | ~r1_tarski('#skF_5', k2_xboole_0('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_6105, c_3523])).
% 5.15/2.13  tff(c_6130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_158, c_158, c_6115])).
% 5.15/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.15/2.13  
% 5.15/2.13  Inference rules
% 5.15/2.13  ----------------------
% 5.15/2.13  #Ref     : 0
% 5.15/2.13  #Sup     : 1513
% 5.15/2.13  #Fact    : 0
% 5.15/2.13  #Define  : 0
% 5.15/2.13  #Split   : 4
% 5.15/2.13  #Chain   : 0
% 5.15/2.13  #Close   : 0
% 5.15/2.13  
% 5.15/2.13  Ordering : KBO
% 5.15/2.13  
% 5.15/2.13  Simplification rules
% 5.15/2.13  ----------------------
% 5.15/2.13  #Subsume      : 169
% 5.15/2.13  #Demod        : 795
% 5.15/2.13  #Tautology    : 717
% 5.15/2.13  #SimpNegUnit  : 0
% 5.15/2.13  #BackRed      : 0
% 5.15/2.13  
% 5.15/2.13  #Partial instantiations: 0
% 5.15/2.13  #Strategies tried      : 1
% 5.15/2.13  
% 5.15/2.13  Timing (in seconds)
% 5.15/2.13  ----------------------
% 5.15/2.13  Preprocessing        : 0.38
% 5.15/2.13  Parsing              : 0.20
% 5.15/2.13  CNF conversion       : 0.03
% 5.15/2.13  Main loop            : 1.02
% 5.15/2.13  Inferencing          : 0.32
% 5.15/2.13  Reduction            : 0.37
% 5.15/2.13  Demodulation         : 0.30
% 5.15/2.13  BG Simplification    : 0.04
% 5.15/2.13  Subsumption          : 0.21
% 5.15/2.13  Abstraction          : 0.05
% 5.15/2.13  MUC search           : 0.00
% 5.15/2.13  Cooper               : 0.00
% 5.15/2.13  Total                : 1.43
% 5.15/2.13  Index Insertion      : 0.00
% 5.15/2.13  Index Deletion       : 0.00
% 5.15/2.13  Index Matching       : 0.00
% 5.15/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
