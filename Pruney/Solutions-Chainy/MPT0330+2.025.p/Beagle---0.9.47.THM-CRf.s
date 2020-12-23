%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:43 EST 2020

% Result     : Theorem 6.38s
% Output     : CNFRefutation 6.38s
% Verified   : 
% Statistics : Number of formulae       :   59 (  91 expanded)
%              Number of leaves         :   24 (  41 expanded)
%              Depth                    :    7
%              Number of atoms          :   60 ( 120 expanded)
%              Number of equality atoms :   29 (  54 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_51,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,k2_zfmisc_1(C,D))
          & r1_tarski(B,k2_zfmisc_1(E,F)) )
       => r1_tarski(k2_xboole_0(A,B),k2_zfmisc_1(k2_xboole_0(C,E),k2_xboole_0(D,F))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

tff(c_338,plain,(
    ! [A_48,B_49,C_50] : k4_xboole_0(k4_xboole_0(A_48,B_49),C_50) = k4_xboole_0(A_48,k2_xboole_0(B_49,C_50)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_113,plain,(
    ! [A_36,B_37] :
      ( k4_xboole_0(A_36,B_37) = k1_xboole_0
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_133,plain,(
    ! [A_12,B_13] : k4_xboole_0(k4_xboole_0(A_12,B_13),A_12) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_113])).

tff(c_406,plain,(
    ! [C_51,B_52] : k4_xboole_0(C_51,k2_xboole_0(B_52,C_51)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_133])).

tff(c_104,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(A_34,B_35)
      | k4_xboole_0(A_34,B_35) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_112,plain,(
    ! [A_34,B_35] :
      ( k2_xboole_0(A_34,B_35) = B_35
      | k4_xboole_0(A_34,B_35) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_104,c_12])).

tff(c_1776,plain,(
    ! [C_90,B_91] : k2_xboole_0(C_90,k2_xboole_0(B_91,C_90)) = k2_xboole_0(B_91,C_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_112])).

tff(c_1232,plain,(
    ! [A_71,C_72,B_73] : k2_xboole_0(k2_zfmisc_1(A_71,C_72),k2_zfmisc_1(B_73,C_72)) = k2_zfmisc_1(k2_xboole_0(A_71,B_73),C_72) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_137,plain,(
    ! [A_11] : k4_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_113])).

tff(c_30,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_134,plain,(
    k4_xboole_0('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_113])).

tff(c_386,plain,(
    ! [C_50] : k4_xboole_0('#skF_2',k2_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'),C_50)) = k4_xboole_0(k1_xboole_0,C_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_338])).

tff(c_403,plain,(
    ! [C_50] : k4_xboole_0('#skF_2',k2_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'),C_50)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_386])).

tff(c_1253,plain,(
    ! [B_73] : k4_xboole_0('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_5',B_73),'#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1232,c_403])).

tff(c_1799,plain,(
    ! [B_91] : k4_xboole_0('#skF_2',k2_zfmisc_1(k2_xboole_0(B_91,'#skF_5'),'#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1776,c_1253])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_135,plain,(
    k4_xboole_0('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_113])).

tff(c_377,plain,(
    ! [C_50] : k4_xboole_0('#skF_1',k2_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),C_50)) = k4_xboole_0(k1_xboole_0,C_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_338])).

tff(c_401,plain,(
    ! [C_50] : k4_xboole_0('#skF_1',k2_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),C_50)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_377])).

tff(c_1242,plain,(
    ! [B_73] : k4_xboole_0('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3',B_73),'#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1232,c_401])).

tff(c_26,plain,(
    ! [C_21,A_19,B_20] : k2_xboole_0(k2_zfmisc_1(C_21,A_19),k2_zfmisc_1(C_21,B_20)) = k2_zfmisc_1(C_21,k2_xboole_0(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1678,plain,(
    ! [A_83,C_84,B_85,D_86] :
      ( r1_tarski(k2_xboole_0(A_83,C_84),k2_xboole_0(B_85,D_86))
      | ~ r1_tarski(C_84,D_86)
      | ~ r1_tarski(A_83,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8859,plain,(
    ! [A_178,C_177,A_179,C_175,B_176] :
      ( r1_tarski(k2_xboole_0(A_179,C_177),k2_zfmisc_1(C_175,k2_xboole_0(A_178,B_176)))
      | ~ r1_tarski(C_177,k2_zfmisc_1(C_175,B_176))
      | ~ r1_tarski(A_179,k2_zfmisc_1(C_175,A_178)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1678])).

tff(c_28,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8937,plain,
    ( ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),'#skF_6'))
    | ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_8859,c_28])).

tff(c_9984,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_8937])).

tff(c_9990,plain,(
    k4_xboole_0('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),'#skF_4')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_9984])).

tff(c_9994,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1242,c_9990])).

tff(c_9995,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),'#skF_6')) ),
    inference(splitRight,[status(thm)],[c_8937])).

tff(c_10002,plain,(
    k4_xboole_0('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),'#skF_6')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_9995])).

tff(c_10008,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1799,c_10002])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:22:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.38/2.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.38/2.32  
% 6.38/2.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.38/2.33  %$ r1_tarski > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.38/2.33  
% 6.38/2.33  %Foreground sorts:
% 6.38/2.33  
% 6.38/2.33  
% 6.38/2.33  %Background operators:
% 6.38/2.33  
% 6.38/2.33  
% 6.38/2.33  %Foreground operators:
% 6.38/2.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.38/2.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.38/2.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.38/2.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.38/2.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.38/2.33  tff('#skF_5', type, '#skF_5': $i).
% 6.38/2.33  tff('#skF_6', type, '#skF_6': $i).
% 6.38/2.33  tff('#skF_2', type, '#skF_2': $i).
% 6.38/2.33  tff('#skF_3', type, '#skF_3': $i).
% 6.38/2.33  tff('#skF_1', type, '#skF_1': $i).
% 6.38/2.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.38/2.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.38/2.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.38/2.33  tff('#skF_4', type, '#skF_4': $i).
% 6.38/2.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.38/2.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.38/2.33  
% 6.38/2.34  tff(f_51, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 6.38/2.34  tff(f_49, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.38/2.34  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.38/2.34  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.38/2.34  tff(f_57, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 6.38/2.34  tff(f_47, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.38/2.34  tff(f_64, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 6.38/2.34  tff(f_45, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_xboole_1)).
% 6.38/2.34  tff(c_338, plain, (![A_48, B_49, C_50]: (k4_xboole_0(k4_xboole_0(A_48, B_49), C_50)=k4_xboole_0(A_48, k2_xboole_0(B_49, C_50)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.38/2.34  tff(c_18, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.38/2.34  tff(c_113, plain, (![A_36, B_37]: (k4_xboole_0(A_36, B_37)=k1_xboole_0 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.38/2.34  tff(c_133, plain, (![A_12, B_13]: (k4_xboole_0(k4_xboole_0(A_12, B_13), A_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_113])).
% 6.38/2.34  tff(c_406, plain, (![C_51, B_52]: (k4_xboole_0(C_51, k2_xboole_0(B_52, C_51))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_338, c_133])).
% 6.38/2.34  tff(c_104, plain, (![A_34, B_35]: (r1_tarski(A_34, B_35) | k4_xboole_0(A_34, B_35)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.38/2.34  tff(c_12, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.38/2.34  tff(c_112, plain, (![A_34, B_35]: (k2_xboole_0(A_34, B_35)=B_35 | k4_xboole_0(A_34, B_35)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_104, c_12])).
% 6.38/2.34  tff(c_1776, plain, (![C_90, B_91]: (k2_xboole_0(C_90, k2_xboole_0(B_91, C_90))=k2_xboole_0(B_91, C_90))), inference(superposition, [status(thm), theory('equality')], [c_406, c_112])).
% 6.38/2.34  tff(c_1232, plain, (![A_71, C_72, B_73]: (k2_xboole_0(k2_zfmisc_1(A_71, C_72), k2_zfmisc_1(B_73, C_72))=k2_zfmisc_1(k2_xboole_0(A_71, B_73), C_72))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.38/2.34  tff(c_16, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.38/2.34  tff(c_137, plain, (![A_11]: (k4_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_113])).
% 6.38/2.34  tff(c_30, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.38/2.34  tff(c_134, plain, (k4_xboole_0('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_113])).
% 6.38/2.34  tff(c_386, plain, (![C_50]: (k4_xboole_0('#skF_2', k2_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'), C_50))=k4_xboole_0(k1_xboole_0, C_50))), inference(superposition, [status(thm), theory('equality')], [c_134, c_338])).
% 6.38/2.34  tff(c_403, plain, (![C_50]: (k4_xboole_0('#skF_2', k2_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'), C_50))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_137, c_386])).
% 6.38/2.34  tff(c_1253, plain, (![B_73]: (k4_xboole_0('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_5', B_73), '#skF_6'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1232, c_403])).
% 6.38/2.34  tff(c_1799, plain, (![B_91]: (k4_xboole_0('#skF_2', k2_zfmisc_1(k2_xboole_0(B_91, '#skF_5'), '#skF_6'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1776, c_1253])).
% 6.38/2.34  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.38/2.34  tff(c_32, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.38/2.34  tff(c_135, plain, (k4_xboole_0('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_113])).
% 6.38/2.34  tff(c_377, plain, (![C_50]: (k4_xboole_0('#skF_1', k2_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), C_50))=k4_xboole_0(k1_xboole_0, C_50))), inference(superposition, [status(thm), theory('equality')], [c_135, c_338])).
% 6.38/2.34  tff(c_401, plain, (![C_50]: (k4_xboole_0('#skF_1', k2_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), C_50))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_137, c_377])).
% 6.38/2.34  tff(c_1242, plain, (![B_73]: (k4_xboole_0('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', B_73), '#skF_4'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1232, c_401])).
% 6.38/2.34  tff(c_26, plain, (![C_21, A_19, B_20]: (k2_xboole_0(k2_zfmisc_1(C_21, A_19), k2_zfmisc_1(C_21, B_20))=k2_zfmisc_1(C_21, k2_xboole_0(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.38/2.34  tff(c_1678, plain, (![A_83, C_84, B_85, D_86]: (r1_tarski(k2_xboole_0(A_83, C_84), k2_xboole_0(B_85, D_86)) | ~r1_tarski(C_84, D_86) | ~r1_tarski(A_83, B_85))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.38/2.34  tff(c_8859, plain, (![A_178, C_177, A_179, C_175, B_176]: (r1_tarski(k2_xboole_0(A_179, C_177), k2_zfmisc_1(C_175, k2_xboole_0(A_178, B_176))) | ~r1_tarski(C_177, k2_zfmisc_1(C_175, B_176)) | ~r1_tarski(A_179, k2_zfmisc_1(C_175, A_178)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1678])).
% 6.38/2.34  tff(c_28, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.38/2.34  tff(c_8937, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), '#skF_6')) | ~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_8859, c_28])).
% 6.38/2.34  tff(c_9984, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4'))), inference(splitLeft, [status(thm)], [c_8937])).
% 6.38/2.34  tff(c_9990, plain, (k4_xboole_0('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_9984])).
% 6.38/2.34  tff(c_9994, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1242, c_9990])).
% 6.38/2.34  tff(c_9995, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), '#skF_6'))), inference(splitRight, [status(thm)], [c_8937])).
% 6.38/2.34  tff(c_10002, plain, (k4_xboole_0('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), '#skF_6'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_9995])).
% 6.38/2.34  tff(c_10008, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1799, c_10002])).
% 6.38/2.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.38/2.34  
% 6.38/2.34  Inference rules
% 6.38/2.34  ----------------------
% 6.38/2.34  #Ref     : 0
% 6.38/2.34  #Sup     : 2534
% 6.38/2.34  #Fact    : 0
% 6.38/2.34  #Define  : 0
% 6.38/2.34  #Split   : 8
% 6.38/2.34  #Chain   : 0
% 6.38/2.34  #Close   : 0
% 6.38/2.34  
% 6.38/2.34  Ordering : KBO
% 6.38/2.34  
% 6.38/2.34  Simplification rules
% 6.38/2.34  ----------------------
% 6.38/2.34  #Subsume      : 253
% 6.38/2.34  #Demod        : 1457
% 6.38/2.34  #Tautology    : 1521
% 6.38/2.34  #SimpNegUnit  : 30
% 6.38/2.34  #BackRed      : 15
% 6.38/2.34  
% 6.38/2.34  #Partial instantiations: 0
% 6.38/2.34  #Strategies tried      : 1
% 6.38/2.34  
% 6.38/2.34  Timing (in seconds)
% 6.38/2.34  ----------------------
% 6.38/2.34  Preprocessing        : 0.29
% 6.38/2.34  Parsing              : 0.16
% 6.38/2.34  CNF conversion       : 0.02
% 6.38/2.34  Main loop            : 1.29
% 6.38/2.34  Inferencing          : 0.37
% 6.38/2.34  Reduction            : 0.55
% 6.38/2.34  Demodulation         : 0.44
% 6.38/2.34  BG Simplification    : 0.04
% 6.38/2.34  Subsumption          : 0.24
% 6.38/2.34  Abstraction          : 0.06
% 6.38/2.34  MUC search           : 0.00
% 6.38/2.34  Cooper               : 0.00
% 6.38/2.34  Total                : 1.61
% 6.38/2.34  Index Insertion      : 0.00
% 6.38/2.34  Index Deletion       : 0.00
% 6.38/2.34  Index Matching       : 0.00
% 6.38/2.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
