%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:41 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :   48 (  72 expanded)
%              Number of leaves         :   22 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   49 ( 100 expanded)
%              Number of equality atoms :   13 (  24 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,k2_zfmisc_1(C,D))
          & r1_tarski(B,k2_zfmisc_1(E,F)) )
       => r1_tarski(k2_xboole_0(A,B),k2_zfmisc_1(k2_xboole_0(C,E),k2_xboole_0(D,F))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

tff(c_18,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_64,plain,(
    ! [A_18,B_19] : k3_tarski(k2_tarski(A_18,B_19)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_79,plain,(
    ! [B_20,A_21] : k3_tarski(k2_tarski(B_20,A_21)) = k2_xboole_0(A_21,B_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_64])).

tff(c_10,plain,(
    ! [A_9,B_10] : k3_tarski(k2_tarski(A_9,B_10)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_85,plain,(
    ! [B_20,A_21] : k2_xboole_0(B_20,A_21) = k2_xboole_0(A_21,B_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_10])).

tff(c_14,plain,(
    ! [C_13,A_11,B_12] : k2_xboole_0(k2_zfmisc_1(C_13,A_11),k2_zfmisc_1(C_13,B_12)) = k2_zfmisc_1(C_13,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_373,plain,(
    ! [A_34,C_35,B_36,D_37] :
      ( r1_tarski(k2_xboole_0(A_34,C_35),k2_xboole_0(B_36,D_37))
      | ~ r1_tarski(C_35,D_37)
      | ~ r1_tarski(A_34,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_406,plain,(
    ! [A_5,B_36,D_37] :
      ( r1_tarski(A_5,k2_xboole_0(B_36,D_37))
      | ~ r1_tarski(k1_xboole_0,D_37)
      | ~ r1_tarski(A_5,B_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_373])).

tff(c_414,plain,(
    ! [A_38,B_39,D_40] :
      ( r1_tarski(A_38,k2_xboole_0(B_39,D_40))
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_406])).

tff(c_960,plain,(
    ! [A_91,C_92,A_93,B_94] :
      ( r1_tarski(A_91,k2_zfmisc_1(C_92,k2_xboole_0(A_93,B_94)))
      | ~ r1_tarski(A_91,k2_zfmisc_1(C_92,A_93)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_414])).

tff(c_997,plain,(
    ! [A_91,C_92,B_20,A_21] :
      ( r1_tarski(A_91,k2_zfmisc_1(C_92,k2_xboole_0(B_20,A_21)))
      | ~ r1_tarski(A_91,k2_zfmisc_1(C_92,A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_960])).

tff(c_20,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_420,plain,(
    ! [A_38,C_13,A_11,B_12] :
      ( r1_tarski(A_38,k2_zfmisc_1(C_13,k2_xboole_0(A_11,B_12)))
      | ~ r1_tarski(A_38,k2_zfmisc_1(C_13,A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_414])).

tff(c_12,plain,(
    ! [A_11,C_13,B_12] : k2_xboole_0(k2_zfmisc_1(A_11,C_13),k2_zfmisc_1(B_12,C_13)) = k2_zfmisc_1(k2_xboole_0(A_11,B_12),C_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_727,plain,(
    ! [A_74,B_75,C_73,C_72,A_71] :
      ( r1_tarski(k2_xboole_0(A_71,C_73),k2_zfmisc_1(k2_xboole_0(A_74,B_75),C_72))
      | ~ r1_tarski(C_73,k2_zfmisc_1(B_75,C_72))
      | ~ r1_tarski(A_71,k2_zfmisc_1(A_74,C_72)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_373])).

tff(c_16,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_774,plain,
    ( ~ r1_tarski('#skF_2',k2_zfmisc_1('#skF_5',k2_xboole_0('#skF_4','#skF_6')))
    | ~ r1_tarski('#skF_1',k2_zfmisc_1('#skF_3',k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_727,c_16])).

tff(c_1311,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1('#skF_3',k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_774])).

tff(c_1317,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_420,c_1311])).

tff(c_1322,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1317])).

tff(c_1323,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1('#skF_5',k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_774])).

tff(c_1327,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_997,c_1323])).

tff(c_1334,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1327])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:49:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.55  
% 3.10/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.55  %$ r1_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.10/1.55  
% 3.10/1.55  %Foreground sorts:
% 3.10/1.55  
% 3.10/1.55  
% 3.10/1.55  %Background operators:
% 3.10/1.55  
% 3.10/1.55  
% 3.10/1.55  %Foreground operators:
% 3.10/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.10/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.10/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.10/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.10/1.55  tff('#skF_6', type, '#skF_6': $i).
% 3.10/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.10/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.10/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.10/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.55  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.10/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.10/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.10/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.10/1.56  
% 3.54/1.57  tff(f_50, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 3.54/1.57  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.54/1.57  tff(f_39, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.54/1.57  tff(f_43, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 3.54/1.57  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.54/1.57  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.54/1.57  tff(f_31, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_xboole_1)).
% 3.54/1.57  tff(c_18, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.54/1.57  tff(c_8, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.54/1.57  tff(c_64, plain, (![A_18, B_19]: (k3_tarski(k2_tarski(A_18, B_19))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.54/1.57  tff(c_79, plain, (![B_20, A_21]: (k3_tarski(k2_tarski(B_20, A_21))=k2_xboole_0(A_21, B_20))), inference(superposition, [status(thm), theory('equality')], [c_8, c_64])).
% 3.54/1.57  tff(c_10, plain, (![A_9, B_10]: (k3_tarski(k2_tarski(A_9, B_10))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.54/1.57  tff(c_85, plain, (![B_20, A_21]: (k2_xboole_0(B_20, A_21)=k2_xboole_0(A_21, B_20))), inference(superposition, [status(thm), theory('equality')], [c_79, c_10])).
% 3.54/1.57  tff(c_14, plain, (![C_13, A_11, B_12]: (k2_xboole_0(k2_zfmisc_1(C_13, A_11), k2_zfmisc_1(C_13, B_12))=k2_zfmisc_1(C_13, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.54/1.57  tff(c_6, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.54/1.57  tff(c_4, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.54/1.57  tff(c_373, plain, (![A_34, C_35, B_36, D_37]: (r1_tarski(k2_xboole_0(A_34, C_35), k2_xboole_0(B_36, D_37)) | ~r1_tarski(C_35, D_37) | ~r1_tarski(A_34, B_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.54/1.57  tff(c_406, plain, (![A_5, B_36, D_37]: (r1_tarski(A_5, k2_xboole_0(B_36, D_37)) | ~r1_tarski(k1_xboole_0, D_37) | ~r1_tarski(A_5, B_36))), inference(superposition, [status(thm), theory('equality')], [c_4, c_373])).
% 3.54/1.57  tff(c_414, plain, (![A_38, B_39, D_40]: (r1_tarski(A_38, k2_xboole_0(B_39, D_40)) | ~r1_tarski(A_38, B_39))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_406])).
% 3.54/1.57  tff(c_960, plain, (![A_91, C_92, A_93, B_94]: (r1_tarski(A_91, k2_zfmisc_1(C_92, k2_xboole_0(A_93, B_94))) | ~r1_tarski(A_91, k2_zfmisc_1(C_92, A_93)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_414])).
% 3.54/1.57  tff(c_997, plain, (![A_91, C_92, B_20, A_21]: (r1_tarski(A_91, k2_zfmisc_1(C_92, k2_xboole_0(B_20, A_21))) | ~r1_tarski(A_91, k2_zfmisc_1(C_92, A_21)))), inference(superposition, [status(thm), theory('equality')], [c_85, c_960])).
% 3.54/1.57  tff(c_20, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.54/1.57  tff(c_420, plain, (![A_38, C_13, A_11, B_12]: (r1_tarski(A_38, k2_zfmisc_1(C_13, k2_xboole_0(A_11, B_12))) | ~r1_tarski(A_38, k2_zfmisc_1(C_13, A_11)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_414])).
% 3.54/1.57  tff(c_12, plain, (![A_11, C_13, B_12]: (k2_xboole_0(k2_zfmisc_1(A_11, C_13), k2_zfmisc_1(B_12, C_13))=k2_zfmisc_1(k2_xboole_0(A_11, B_12), C_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.54/1.57  tff(c_727, plain, (![A_74, B_75, C_73, C_72, A_71]: (r1_tarski(k2_xboole_0(A_71, C_73), k2_zfmisc_1(k2_xboole_0(A_74, B_75), C_72)) | ~r1_tarski(C_73, k2_zfmisc_1(B_75, C_72)) | ~r1_tarski(A_71, k2_zfmisc_1(A_74, C_72)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_373])).
% 3.54/1.57  tff(c_16, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.54/1.57  tff(c_774, plain, (~r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', k2_xboole_0('#skF_4', '#skF_6'))) | ~r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', k2_xboole_0('#skF_4', '#skF_6')))), inference(resolution, [status(thm)], [c_727, c_16])).
% 3.54/1.57  tff(c_1311, plain, (~r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', k2_xboole_0('#skF_4', '#skF_6')))), inference(splitLeft, [status(thm)], [c_774])).
% 3.54/1.57  tff(c_1317, plain, (~r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_420, c_1311])).
% 3.54/1.57  tff(c_1322, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_1317])).
% 3.54/1.57  tff(c_1323, plain, (~r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', k2_xboole_0('#skF_4', '#skF_6')))), inference(splitRight, [status(thm)], [c_774])).
% 3.54/1.57  tff(c_1327, plain, (~r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_997, c_1323])).
% 3.54/1.57  tff(c_1334, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_1327])).
% 3.54/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.57  
% 3.54/1.57  Inference rules
% 3.54/1.57  ----------------------
% 3.54/1.57  #Ref     : 0
% 3.54/1.57  #Sup     : 346
% 3.54/1.57  #Fact    : 0
% 3.54/1.57  #Define  : 0
% 3.54/1.57  #Split   : 5
% 3.54/1.57  #Chain   : 0
% 3.54/1.57  #Close   : 0
% 3.54/1.57  
% 3.54/1.57  Ordering : KBO
% 3.54/1.57  
% 3.54/1.57  Simplification rules
% 3.54/1.57  ----------------------
% 3.54/1.57  #Subsume      : 73
% 3.54/1.57  #Demod        : 53
% 3.54/1.57  #Tautology    : 68
% 3.54/1.57  #SimpNegUnit  : 0
% 3.54/1.57  #BackRed      : 0
% 3.54/1.57  
% 3.54/1.57  #Partial instantiations: 0
% 3.54/1.57  #Strategies tried      : 1
% 3.54/1.57  
% 3.54/1.57  Timing (in seconds)
% 3.54/1.57  ----------------------
% 3.54/1.57  Preprocessing        : 0.28
% 3.54/1.57  Parsing              : 0.16
% 3.54/1.57  CNF conversion       : 0.02
% 3.54/1.57  Main loop            : 0.54
% 3.54/1.57  Inferencing          : 0.19
% 3.54/1.57  Reduction            : 0.20
% 3.54/1.57  Demodulation         : 0.16
% 3.54/1.57  BG Simplification    : 0.02
% 3.54/1.57  Subsumption          : 0.10
% 3.54/1.57  Abstraction          : 0.02
% 3.54/1.57  MUC search           : 0.00
% 3.54/1.57  Cooper               : 0.00
% 3.54/1.57  Total                : 0.85
% 3.54/1.57  Index Insertion      : 0.00
% 3.54/1.57  Index Deletion       : 0.00
% 3.54/1.57  Index Matching       : 0.00
% 3.54/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
