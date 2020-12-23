%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:42 EST 2020

% Result     : Theorem 19.42s
% Output     : CNFRefutation 19.43s
% Verified   : 
% Statistics : Number of formulae       :   58 (  99 expanded)
%              Number of leaves         :   24 (  45 expanded)
%              Depth                    :    7
%              Number of atoms          :   73 ( 148 expanded)
%              Number of equality atoms :   10 (  22 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,k2_zfmisc_1(C,D))
          & r1_tarski(B,k2_zfmisc_1(E,F)) )
       => r1_tarski(k2_xboole_0(A,B),k2_zfmisc_1(k2_xboole_0(C,E),k2_xboole_0(D,F))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_30,plain,(
    ! [B_29,A_30] : k2_xboole_0(B_29,A_30) = k2_xboole_0(A_30,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_45,plain,(
    ! [A_30,B_29] : r1_tarski(A_30,k2_xboole_0(B_29,A_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_8])).

tff(c_312,plain,(
    ! [A_59,C_60,B_61] :
      ( r1_tarski(k2_zfmisc_1(A_59,C_60),k2_zfmisc_1(B_61,C_60))
      | ~ r1_tarski(A_59,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_316,plain,(
    ! [A_59,C_60,B_61] :
      ( k2_xboole_0(k2_zfmisc_1(A_59,C_60),k2_zfmisc_1(B_61,C_60)) = k2_zfmisc_1(B_61,C_60)
      | ~ r1_tarski(A_59,B_61) ) ),
    inference(resolution,[status(thm)],[c_312,c_6])).

tff(c_385,plain,(
    ! [C_64,A_65,B_66] :
      ( r1_tarski(k2_zfmisc_1(C_64,A_65),k2_zfmisc_1(C_64,B_66))
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_41457,plain,(
    ! [C_556,A_557,B_558] :
      ( k2_xboole_0(k2_zfmisc_1(C_556,A_557),k2_zfmisc_1(C_556,B_558)) = k2_zfmisc_1(C_556,B_558)
      | ~ r1_tarski(A_557,B_558) ) ),
    inference(resolution,[status(thm)],[c_385,c_6])).

tff(c_114,plain,(
    ! [A_39,C_40,B_41] :
      ( r1_tarski(A_39,C_40)
      | ~ r1_tarski(k2_xboole_0(A_39,B_41),C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_130,plain,(
    ! [A_39,B_41,B_9] : r1_tarski(A_39,k2_xboole_0(k2_xboole_0(A_39,B_41),B_9)) ),
    inference(resolution,[status(thm)],[c_8,c_114])).

tff(c_43762,plain,(
    ! [C_596,A_597,B_598,B_599] :
      ( r1_tarski(k2_zfmisc_1(C_596,A_597),k2_xboole_0(k2_zfmisc_1(C_596,B_598),B_599))
      | ~ r1_tarski(A_597,B_598) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41457,c_130])).

tff(c_26,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_97,plain,(
    ! [A_37,B_38] :
      ( k2_xboole_0(A_37,B_38) = B_38
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_112,plain,(
    k2_xboole_0('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) = k2_zfmisc_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_97])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_335,plain,(
    ! [C_5] :
      ( r1_tarski('#skF_2',C_5)
      | ~ r1_tarski(k2_zfmisc_1('#skF_5','#skF_6'),C_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_4])).

tff(c_47099,plain,(
    ! [B_638,B_639] :
      ( r1_tarski('#skF_2',k2_xboole_0(k2_zfmisc_1('#skF_5',B_638),B_639))
      | ~ r1_tarski('#skF_6',B_638) ) ),
    inference(resolution,[status(thm)],[c_43762,c_335])).

tff(c_73073,plain,(
    ! [B_878,C_879] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(B_878,C_879))
      | ~ r1_tarski('#skF_6',C_879)
      | ~ r1_tarski('#skF_5',B_878) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_47099])).

tff(c_3190,plain,(
    ! [C_139,A_140,B_141] :
      ( k2_xboole_0(k2_zfmisc_1(C_139,A_140),k2_zfmisc_1(C_139,B_141)) = k2_zfmisc_1(C_139,B_141)
      | ~ r1_tarski(A_140,B_141) ) ),
    inference(resolution,[status(thm)],[c_385,c_6])).

tff(c_4367,plain,(
    ! [C_167,A_168,B_169,B_170] :
      ( r1_tarski(k2_zfmisc_1(C_167,A_168),k2_xboole_0(k2_zfmisc_1(C_167,B_169),B_170))
      | ~ r1_tarski(A_168,B_169) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3190,c_130])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_113,plain,(
    k2_xboole_0('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_97])).

tff(c_262,plain,(
    ! [C_5] :
      ( r1_tarski('#skF_1',C_5)
      | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),C_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_4])).

tff(c_6642,plain,(
    ! [B_204,B_205] :
      ( r1_tarski('#skF_1',k2_xboole_0(k2_zfmisc_1('#skF_3',B_204),B_205))
      | ~ r1_tarski('#skF_4',B_204) ) ),
    inference(resolution,[status(thm)],[c_4367,c_262])).

tff(c_38765,plain,(
    ! [B_496,C_497] :
      ( r1_tarski('#skF_1',k2_zfmisc_1(B_496,C_497))
      | ~ r1_tarski('#skF_4',C_497)
      | ~ r1_tarski('#skF_3',B_496) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_6642])).

tff(c_680,plain,(
    ! [A_77,C_78,B_79] :
      ( r1_tarski(k2_xboole_0(A_77,C_78),B_79)
      | ~ r1_tarski(C_78,B_79)
      | ~ r1_tarski(A_77,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_710,plain,
    ( ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6')))
    | ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_680,c_24])).

tff(c_885,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_710])).

tff(c_38786,plain,
    ( ~ r1_tarski('#skF_4',k2_xboole_0('#skF_4','#skF_6'))
    | ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_38765,c_885])).

tff(c_38807,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_38786])).

tff(c_38808,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_710])).

tff(c_73088,plain,
    ( ~ r1_tarski('#skF_6',k2_xboole_0('#skF_4','#skF_6'))
    | ~ r1_tarski('#skF_5',k2_xboole_0('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_73073,c_38808])).

tff(c_73102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_45,c_73088])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:11:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.42/11.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.43/11.14  
% 19.43/11.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.43/11.15  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 19.43/11.15  
% 19.43/11.15  %Foreground sorts:
% 19.43/11.15  
% 19.43/11.15  
% 19.43/11.15  %Background operators:
% 19.43/11.15  
% 19.43/11.15  
% 19.43/11.15  %Foreground operators:
% 19.43/11.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.43/11.15  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 19.43/11.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.43/11.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 19.43/11.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 19.43/11.15  tff('#skF_5', type, '#skF_5': $i).
% 19.43/11.15  tff('#skF_6', type, '#skF_6': $i).
% 19.43/11.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 19.43/11.15  tff('#skF_2', type, '#skF_2': $i).
% 19.43/11.15  tff('#skF_3', type, '#skF_3': $i).
% 19.43/11.15  tff('#skF_1', type, '#skF_1': $i).
% 19.43/11.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.43/11.15  tff(k3_tarski, type, k3_tarski: $i > $i).
% 19.43/11.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 19.43/11.15  tff('#skF_4', type, '#skF_4': $i).
% 19.43/11.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.43/11.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 19.43/11.15  
% 19.43/11.16  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 19.43/11.16  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 19.43/11.16  tff(f_57, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 19.43/11.16  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 19.43/11.16  tff(f_31, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 19.43/11.16  tff(f_64, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 19.43/11.16  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 19.43/11.16  tff(c_30, plain, (![B_29, A_30]: (k2_xboole_0(B_29, A_30)=k2_xboole_0(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_27])).
% 19.43/11.16  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 19.43/11.16  tff(c_45, plain, (![A_30, B_29]: (r1_tarski(A_30, k2_xboole_0(B_29, A_30)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_8])).
% 19.43/11.16  tff(c_312, plain, (![A_59, C_60, B_61]: (r1_tarski(k2_zfmisc_1(A_59, C_60), k2_zfmisc_1(B_61, C_60)) | ~r1_tarski(A_59, B_61))), inference(cnfTransformation, [status(thm)], [f_57])).
% 19.43/11.16  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 19.43/11.16  tff(c_316, plain, (![A_59, C_60, B_61]: (k2_xboole_0(k2_zfmisc_1(A_59, C_60), k2_zfmisc_1(B_61, C_60))=k2_zfmisc_1(B_61, C_60) | ~r1_tarski(A_59, B_61))), inference(resolution, [status(thm)], [c_312, c_6])).
% 19.43/11.16  tff(c_385, plain, (![C_64, A_65, B_66]: (r1_tarski(k2_zfmisc_1(C_64, A_65), k2_zfmisc_1(C_64, B_66)) | ~r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_57])).
% 19.43/11.16  tff(c_41457, plain, (![C_556, A_557, B_558]: (k2_xboole_0(k2_zfmisc_1(C_556, A_557), k2_zfmisc_1(C_556, B_558))=k2_zfmisc_1(C_556, B_558) | ~r1_tarski(A_557, B_558))), inference(resolution, [status(thm)], [c_385, c_6])).
% 19.43/11.16  tff(c_114, plain, (![A_39, C_40, B_41]: (r1_tarski(A_39, C_40) | ~r1_tarski(k2_xboole_0(A_39, B_41), C_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 19.43/11.16  tff(c_130, plain, (![A_39, B_41, B_9]: (r1_tarski(A_39, k2_xboole_0(k2_xboole_0(A_39, B_41), B_9)))), inference(resolution, [status(thm)], [c_8, c_114])).
% 19.43/11.16  tff(c_43762, plain, (![C_596, A_597, B_598, B_599]: (r1_tarski(k2_zfmisc_1(C_596, A_597), k2_xboole_0(k2_zfmisc_1(C_596, B_598), B_599)) | ~r1_tarski(A_597, B_598))), inference(superposition, [status(thm), theory('equality')], [c_41457, c_130])).
% 19.43/11.16  tff(c_26, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 19.43/11.16  tff(c_97, plain, (![A_37, B_38]: (k2_xboole_0(A_37, B_38)=B_38 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_35])).
% 19.43/11.16  tff(c_112, plain, (k2_xboole_0('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))=k2_zfmisc_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_26, c_97])).
% 19.43/11.16  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 19.43/11.16  tff(c_335, plain, (![C_5]: (r1_tarski('#skF_2', C_5) | ~r1_tarski(k2_zfmisc_1('#skF_5', '#skF_6'), C_5))), inference(superposition, [status(thm), theory('equality')], [c_112, c_4])).
% 19.43/11.16  tff(c_47099, plain, (![B_638, B_639]: (r1_tarski('#skF_2', k2_xboole_0(k2_zfmisc_1('#skF_5', B_638), B_639)) | ~r1_tarski('#skF_6', B_638))), inference(resolution, [status(thm)], [c_43762, c_335])).
% 19.43/11.16  tff(c_73073, plain, (![B_878, C_879]: (r1_tarski('#skF_2', k2_zfmisc_1(B_878, C_879)) | ~r1_tarski('#skF_6', C_879) | ~r1_tarski('#skF_5', B_878))), inference(superposition, [status(thm), theory('equality')], [c_316, c_47099])).
% 19.43/11.16  tff(c_3190, plain, (![C_139, A_140, B_141]: (k2_xboole_0(k2_zfmisc_1(C_139, A_140), k2_zfmisc_1(C_139, B_141))=k2_zfmisc_1(C_139, B_141) | ~r1_tarski(A_140, B_141))), inference(resolution, [status(thm)], [c_385, c_6])).
% 19.43/11.16  tff(c_4367, plain, (![C_167, A_168, B_169, B_170]: (r1_tarski(k2_zfmisc_1(C_167, A_168), k2_xboole_0(k2_zfmisc_1(C_167, B_169), B_170)) | ~r1_tarski(A_168, B_169))), inference(superposition, [status(thm), theory('equality')], [c_3190, c_130])).
% 19.43/11.16  tff(c_28, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 19.43/11.16  tff(c_113, plain, (k2_xboole_0('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_97])).
% 19.43/11.16  tff(c_262, plain, (![C_5]: (r1_tarski('#skF_1', C_5) | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), C_5))), inference(superposition, [status(thm), theory('equality')], [c_113, c_4])).
% 19.43/11.16  tff(c_6642, plain, (![B_204, B_205]: (r1_tarski('#skF_1', k2_xboole_0(k2_zfmisc_1('#skF_3', B_204), B_205)) | ~r1_tarski('#skF_4', B_204))), inference(resolution, [status(thm)], [c_4367, c_262])).
% 19.43/11.16  tff(c_38765, plain, (![B_496, C_497]: (r1_tarski('#skF_1', k2_zfmisc_1(B_496, C_497)) | ~r1_tarski('#skF_4', C_497) | ~r1_tarski('#skF_3', B_496))), inference(superposition, [status(thm), theory('equality')], [c_316, c_6642])).
% 19.43/11.16  tff(c_680, plain, (![A_77, C_78, B_79]: (r1_tarski(k2_xboole_0(A_77, C_78), B_79) | ~r1_tarski(C_78, B_79) | ~r1_tarski(A_77, B_79))), inference(cnfTransformation, [status(thm)], [f_43])).
% 19.43/11.16  tff(c_24, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 19.43/11.16  tff(c_710, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6'))) | ~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(resolution, [status(thm)], [c_680, c_24])).
% 19.43/11.16  tff(c_885, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(splitLeft, [status(thm)], [c_710])).
% 19.43/11.16  tff(c_38786, plain, (~r1_tarski('#skF_4', k2_xboole_0('#skF_4', '#skF_6')) | ~r1_tarski('#skF_3', k2_xboole_0('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_38765, c_885])).
% 19.43/11.16  tff(c_38807, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_38786])).
% 19.43/11.16  tff(c_38808, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(splitRight, [status(thm)], [c_710])).
% 19.43/11.16  tff(c_73088, plain, (~r1_tarski('#skF_6', k2_xboole_0('#skF_4', '#skF_6')) | ~r1_tarski('#skF_5', k2_xboole_0('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_73073, c_38808])).
% 19.43/11.16  tff(c_73102, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_45, c_45, c_73088])).
% 19.43/11.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.43/11.16  
% 19.43/11.16  Inference rules
% 19.43/11.16  ----------------------
% 19.43/11.16  #Ref     : 0
% 19.43/11.16  #Sup     : 17799
% 19.43/11.16  #Fact    : 0
% 19.43/11.16  #Define  : 0
% 19.43/11.16  #Split   : 5
% 19.43/11.16  #Chain   : 0
% 19.43/11.16  #Close   : 0
% 19.43/11.16  
% 19.43/11.16  Ordering : KBO
% 19.43/11.16  
% 19.43/11.16  Simplification rules
% 19.43/11.16  ----------------------
% 19.43/11.16  #Subsume      : 1926
% 19.43/11.16  #Demod        : 11910
% 19.43/11.16  #Tautology    : 8835
% 19.43/11.16  #SimpNegUnit  : 0
% 19.43/11.16  #BackRed      : 0
% 19.43/11.16  
% 19.43/11.16  #Partial instantiations: 0
% 19.43/11.16  #Strategies tried      : 1
% 19.43/11.16  
% 19.43/11.16  Timing (in seconds)
% 19.43/11.16  ----------------------
% 19.43/11.16  Preprocessing        : 0.42
% 19.43/11.16  Parsing              : 0.21
% 19.43/11.16  CNF conversion       : 0.03
% 19.43/11.16  Main loop            : 9.99
% 19.43/11.16  Inferencing          : 1.41
% 19.43/11.16  Reduction            : 6.07
% 19.43/11.16  Demodulation         : 5.60
% 19.43/11.16  BG Simplification    : 0.17
% 19.43/11.16  Subsumption          : 1.92
% 19.43/11.16  Abstraction          : 0.27
% 19.43/11.16  MUC search           : 0.00
% 19.43/11.16  Cooper               : 0.00
% 19.43/11.16  Total                : 10.44
% 19.43/11.16  Index Insertion      : 0.00
% 19.43/11.16  Index Deletion       : 0.00
% 19.43/11.16  Index Matching       : 0.00
% 19.43/11.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
