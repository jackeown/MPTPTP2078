%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:44 EST 2020

% Result     : Theorem 4.27s
% Output     : CNFRefutation 4.36s
% Verified   : 
% Statistics : Number of formulae       :   49 (  65 expanded)
%              Number of leaves         :   23 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   54 (  88 expanded)
%              Number of equality atoms :    5 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,k2_zfmisc_1(C,D))
          & r1_tarski(B,k2_zfmisc_1(E,F)) )
       => r1_tarski(k2_xboole_0(A,B),k2_zfmisc_1(k2_xboole_0(C,E),k2_xboole_0(D,F))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_24,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_293,plain,(
    ! [C_83,A_84,B_85] : k2_xboole_0(k2_zfmisc_1(C_83,A_84),k2_zfmisc_1(C_83,B_85)) = k2_zfmisc_1(C_83,k2_xboole_0(A_84,B_85)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,k2_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2094,plain,(
    ! [A_215,C_216,A_217,B_218] :
      ( r1_tarski(A_215,k2_zfmisc_1(C_216,k2_xboole_0(A_217,B_218)))
      | ~ r1_tarski(A_215,k2_zfmisc_1(C_216,B_218)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_2])).

tff(c_123,plain,(
    ! [A_57,C_58,B_59] : k2_xboole_0(k2_zfmisc_1(A_57,C_58),k2_zfmisc_1(B_59,C_58)) = k2_zfmisc_1(k2_xboole_0(A_57,B_59),C_58) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1836,plain,(
    ! [A_195,A_196,B_197,C_198] :
      ( r1_tarski(A_195,k2_zfmisc_1(k2_xboole_0(A_196,B_197),C_198))
      | ~ r1_tarski(A_195,k2_zfmisc_1(B_197,C_198)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_2])).

tff(c_20,plain,(
    ! [C_25,A_23,B_24] : k2_xboole_0(k2_zfmisc_1(C_25,A_23),k2_zfmisc_1(C_25,B_24)) = k2_zfmisc_1(C_25,k2_xboole_0(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_138,plain,(
    ! [A_57,C_58,B_59] : r1_tarski(k2_zfmisc_1(A_57,C_58),k2_zfmisc_1(k2_xboole_0(A_57,B_59),C_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_6])).

tff(c_26,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_47,plain,(
    ! [A_35,C_36,B_37] :
      ( r1_tarski(A_35,C_36)
      | ~ r1_tarski(B_37,C_36)
      | ~ r1_tarski(A_35,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_60,plain,(
    ! [A_38,A_39,B_40] :
      ( r1_tarski(A_38,k2_xboole_0(A_39,B_40))
      | ~ r1_tarski(A_38,A_39) ) ),
    inference(resolution,[status(thm)],[c_6,c_47])).

tff(c_4,plain,(
    ! [A_4,C_6,B_5] :
      ( r1_tarski(A_4,C_6)
      | ~ r1_tarski(B_5,C_6)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_689,plain,(
    ! [A_115,A_116,B_117,A_118] :
      ( r1_tarski(A_115,k2_xboole_0(A_116,B_117))
      | ~ r1_tarski(A_115,A_118)
      | ~ r1_tarski(A_118,A_116) ) ),
    inference(resolution,[status(thm)],[c_60,c_4])).

tff(c_952,plain,(
    ! [A_135,B_136] :
      ( r1_tarski('#skF_1',k2_xboole_0(A_135,B_136))
      | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),A_135) ) ),
    inference(resolution,[status(thm)],[c_26,c_689])).

tff(c_1059,plain,(
    ! [B_143,B_144] : r1_tarski('#skF_1',k2_xboole_0(k2_zfmisc_1(k2_xboole_0('#skF_3',B_143),'#skF_4'),B_144)) ),
    inference(resolution,[status(thm)],[c_138,c_952])).

tff(c_1075,plain,(
    ! [B_143,B_24] : r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3',B_143),k2_xboole_0('#skF_4',B_24))) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1059])).

tff(c_81,plain,(
    ! [A_46,C_47,B_48] :
      ( r1_tarski(k2_xboole_0(A_46,C_47),B_48)
      | ~ r1_tarski(C_47,B_48)
      | ~ r1_tarski(A_46,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_87,plain,
    ( ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6')))
    | ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_81,c_22])).

tff(c_394,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_1318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1075,c_394])).

tff(c_1319,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_1882,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1('#skF_5',k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_1836,c_1319])).

tff(c_2103,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_2094,c_1882])).

tff(c_2150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2103])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:02:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.27/1.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.27/1.82  
% 4.27/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.27/1.82  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.27/1.82  
% 4.27/1.82  %Foreground sorts:
% 4.27/1.82  
% 4.27/1.82  
% 4.27/1.82  %Background operators:
% 4.27/1.82  
% 4.27/1.82  
% 4.27/1.82  %Foreground operators:
% 4.27/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.27/1.82  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.27/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.27/1.82  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.27/1.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.27/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.27/1.82  tff('#skF_6', type, '#skF_6': $i).
% 4.27/1.82  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.27/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.27/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.27/1.82  tff('#skF_1', type, '#skF_1': $i).
% 4.27/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.27/1.82  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.27/1.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.27/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.27/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.27/1.82  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.27/1.82  
% 4.36/1.84  tff(f_62, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 4.36/1.84  tff(f_55, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 4.36/1.84  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 4.36/1.84  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.36/1.84  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.36/1.84  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 4.36/1.84  tff(c_24, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.36/1.84  tff(c_293, plain, (![C_83, A_84, B_85]: (k2_xboole_0(k2_zfmisc_1(C_83, A_84), k2_zfmisc_1(C_83, B_85))=k2_zfmisc_1(C_83, k2_xboole_0(A_84, B_85)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.36/1.84  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, k2_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.36/1.84  tff(c_2094, plain, (![A_215, C_216, A_217, B_218]: (r1_tarski(A_215, k2_zfmisc_1(C_216, k2_xboole_0(A_217, B_218))) | ~r1_tarski(A_215, k2_zfmisc_1(C_216, B_218)))), inference(superposition, [status(thm), theory('equality')], [c_293, c_2])).
% 4.36/1.84  tff(c_123, plain, (![A_57, C_58, B_59]: (k2_xboole_0(k2_zfmisc_1(A_57, C_58), k2_zfmisc_1(B_59, C_58))=k2_zfmisc_1(k2_xboole_0(A_57, B_59), C_58))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.36/1.84  tff(c_1836, plain, (![A_195, A_196, B_197, C_198]: (r1_tarski(A_195, k2_zfmisc_1(k2_xboole_0(A_196, B_197), C_198)) | ~r1_tarski(A_195, k2_zfmisc_1(B_197, C_198)))), inference(superposition, [status(thm), theory('equality')], [c_123, c_2])).
% 4.36/1.84  tff(c_20, plain, (![C_25, A_23, B_24]: (k2_xboole_0(k2_zfmisc_1(C_25, A_23), k2_zfmisc_1(C_25, B_24))=k2_zfmisc_1(C_25, k2_xboole_0(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.36/1.84  tff(c_6, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.36/1.84  tff(c_138, plain, (![A_57, C_58, B_59]: (r1_tarski(k2_zfmisc_1(A_57, C_58), k2_zfmisc_1(k2_xboole_0(A_57, B_59), C_58)))), inference(superposition, [status(thm), theory('equality')], [c_123, c_6])).
% 4.36/1.84  tff(c_26, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.36/1.84  tff(c_47, plain, (![A_35, C_36, B_37]: (r1_tarski(A_35, C_36) | ~r1_tarski(B_37, C_36) | ~r1_tarski(A_35, B_37))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.36/1.84  tff(c_60, plain, (![A_38, A_39, B_40]: (r1_tarski(A_38, k2_xboole_0(A_39, B_40)) | ~r1_tarski(A_38, A_39))), inference(resolution, [status(thm)], [c_6, c_47])).
% 4.36/1.84  tff(c_4, plain, (![A_4, C_6, B_5]: (r1_tarski(A_4, C_6) | ~r1_tarski(B_5, C_6) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.36/1.84  tff(c_689, plain, (![A_115, A_116, B_117, A_118]: (r1_tarski(A_115, k2_xboole_0(A_116, B_117)) | ~r1_tarski(A_115, A_118) | ~r1_tarski(A_118, A_116))), inference(resolution, [status(thm)], [c_60, c_4])).
% 4.36/1.84  tff(c_952, plain, (![A_135, B_136]: (r1_tarski('#skF_1', k2_xboole_0(A_135, B_136)) | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), A_135))), inference(resolution, [status(thm)], [c_26, c_689])).
% 4.36/1.84  tff(c_1059, plain, (![B_143, B_144]: (r1_tarski('#skF_1', k2_xboole_0(k2_zfmisc_1(k2_xboole_0('#skF_3', B_143), '#skF_4'), B_144)))), inference(resolution, [status(thm)], [c_138, c_952])).
% 4.36/1.84  tff(c_1075, plain, (![B_143, B_24]: (r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', B_143), k2_xboole_0('#skF_4', B_24))))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1059])).
% 4.36/1.84  tff(c_81, plain, (![A_46, C_47, B_48]: (r1_tarski(k2_xboole_0(A_46, C_47), B_48) | ~r1_tarski(C_47, B_48) | ~r1_tarski(A_46, B_48))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.36/1.84  tff(c_22, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.36/1.84  tff(c_87, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6'))) | ~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(resolution, [status(thm)], [c_81, c_22])).
% 4.36/1.84  tff(c_394, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(splitLeft, [status(thm)], [c_87])).
% 4.36/1.84  tff(c_1318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1075, c_394])).
% 4.36/1.84  tff(c_1319, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(splitRight, [status(thm)], [c_87])).
% 4.36/1.84  tff(c_1882, plain, (~r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', k2_xboole_0('#skF_4', '#skF_6')))), inference(resolution, [status(thm)], [c_1836, c_1319])).
% 4.36/1.84  tff(c_2103, plain, (~r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_2094, c_1882])).
% 4.36/1.84  tff(c_2150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_2103])).
% 4.36/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.36/1.84  
% 4.36/1.84  Inference rules
% 4.36/1.84  ----------------------
% 4.36/1.84  #Ref     : 0
% 4.36/1.84  #Sup     : 589
% 4.36/1.84  #Fact    : 0
% 4.36/1.84  #Define  : 0
% 4.36/1.84  #Split   : 4
% 4.36/1.84  #Chain   : 0
% 4.36/1.84  #Close   : 0
% 4.36/1.84  
% 4.36/1.84  Ordering : KBO
% 4.36/1.84  
% 4.36/1.84  Simplification rules
% 4.36/1.84  ----------------------
% 4.36/1.84  #Subsume      : 23
% 4.36/1.84  #Demod        : 71
% 4.36/1.84  #Tautology    : 89
% 4.36/1.84  #SimpNegUnit  : 0
% 4.36/1.84  #BackRed      : 1
% 4.36/1.84  
% 4.36/1.84  #Partial instantiations: 0
% 4.36/1.84  #Strategies tried      : 1
% 4.36/1.84  
% 4.36/1.84  Timing (in seconds)
% 4.36/1.84  ----------------------
% 4.36/1.84  Preprocessing        : 0.28
% 4.36/1.84  Parsing              : 0.14
% 4.36/1.84  CNF conversion       : 0.02
% 4.36/1.84  Main loop            : 0.75
% 4.36/1.84  Inferencing          : 0.23
% 4.36/1.84  Reduction            : 0.25
% 4.36/1.84  Demodulation         : 0.19
% 4.36/1.84  BG Simplification    : 0.03
% 4.36/1.84  Subsumption          : 0.18
% 4.36/1.84  Abstraction          : 0.04
% 4.36/1.84  MUC search           : 0.00
% 4.36/1.84  Cooper               : 0.00
% 4.36/1.84  Total                : 1.05
% 4.36/1.84  Index Insertion      : 0.00
% 4.36/1.84  Index Deletion       : 0.00
% 4.36/1.84  Index Matching       : 0.00
% 4.36/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
