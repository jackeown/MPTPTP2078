%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:26 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :   58 (  91 expanded)
%              Number of leaves         :   31 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :   46 (  89 expanded)
%              Number of equality atoms :   21 (  43 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k3_enumset1 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_58,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_48,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_52,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_56,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(A),k1_zfmisc_1(B)),k1_zfmisc_1(k2_xboole_0(A,B))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_zfmisc_1)).

tff(c_36,plain,(
    ! [A_21,B_22] : r1_tarski(A_21,k2_xboole_0(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_133,plain,(
    ! [A_56,B_57] :
      ( k4_xboole_0(A_56,B_57) = k1_xboole_0
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_141,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k2_xboole_0(A_21,B_22)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_133])).

tff(c_26,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_315,plain,(
    ! [A_82,B_83] : k4_xboole_0(A_82,k4_xboole_0(A_82,B_83)) = k3_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_465,plain,(
    ! [A_88] : k4_xboole_0(A_88,A_88) = k3_xboole_0(A_88,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_315])).

tff(c_28,plain,(
    ! [A_12,B_13,C_14] : k4_xboole_0(k4_xboole_0(A_12,B_13),C_14) = k4_xboole_0(A_12,k2_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_471,plain,(
    ! [A_88,C_14] : k4_xboole_0(k3_xboole_0(A_88,k1_xboole_0),C_14) = k4_xboole_0(A_88,k2_xboole_0(A_88,C_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_28])).

tff(c_552,plain,(
    ! [A_91,C_92] : k4_xboole_0(k3_xboole_0(A_91,k1_xboole_0),C_92) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_471])).

tff(c_589,plain,(
    ! [A_91] : k3_xboole_0(A_91,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_552,c_26])).

tff(c_346,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k3_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_315])).

tff(c_628,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_589,c_346])).

tff(c_980,plain,(
    ! [A_110,B_111,C_112] : k3_xboole_0(k4_xboole_0(A_110,B_111),k4_xboole_0(A_110,C_112)) = k4_xboole_0(A_110,k2_xboole_0(B_111,C_112)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1009,plain,(
    ! [A_11,B_111] : k4_xboole_0(A_11,k2_xboole_0(B_111,A_11)) = k3_xboole_0(k4_xboole_0(A_11,B_111),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_980])).

tff(c_1055,plain,(
    ! [A_11,B_111] : k4_xboole_0(A_11,k2_xboole_0(B_111,A_11)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_589,c_1009])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | k4_xboole_0(A_9,B_10) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_56,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(k1_zfmisc_1(A_44),k1_zfmisc_1(B_45))
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_813,plain,(
    ! [A_104,C_105,B_106] :
      ( r1_tarski(k2_xboole_0(A_104,C_105),B_106)
      | ~ r1_tarski(C_105,B_106)
      | ~ r1_tarski(A_104,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_58,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1('#skF_4'),k1_zfmisc_1('#skF_5')),k1_zfmisc_1(k2_xboole_0('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_823,plain,
    ( ~ r1_tarski(k1_zfmisc_1('#skF_5'),k1_zfmisc_1(k2_xboole_0('#skF_4','#skF_5')))
    | ~ r1_tarski(k1_zfmisc_1('#skF_4'),k1_zfmisc_1(k2_xboole_0('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_813,c_58])).

tff(c_943,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_4'),k1_zfmisc_1(k2_xboole_0('#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_823])).

tff(c_970,plain,(
    ~ r1_tarski('#skF_4',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_56,c_943])).

tff(c_977,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_970])).

tff(c_978,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_5'),k1_zfmisc_1(k2_xboole_0('#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_823])).

tff(c_1158,plain,(
    ~ r1_tarski('#skF_5',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_56,c_978])).

tff(c_1162,plain,(
    k4_xboole_0('#skF_5',k2_xboole_0('#skF_4','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_1158])).

tff(c_1166,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1055,c_1162])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:35:10 EST 2020
% 0.20/0.33  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.64/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.39  
% 2.89/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.39  %$ r2_hidden > r1_tarski > k6_enumset1 > k3_enumset1 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.89/1.39  
% 2.89/1.39  %Foreground sorts:
% 2.89/1.39  
% 2.89/1.39  
% 2.89/1.39  %Background operators:
% 2.89/1.39  
% 2.89/1.39  
% 2.89/1.39  %Foreground operators:
% 2.89/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.89/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.89/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.89/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.89/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.89/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.89/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.89/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.89/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.89/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.89/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.89/1.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.89/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.89/1.39  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.89/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.89/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.89/1.39  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.89/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.89/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.89/1.39  
% 2.89/1.40  tff(f_58, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.89/1.40  tff(f_46, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.89/1.40  tff(f_48, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.89/1.40  tff(f_52, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.89/1.40  tff(f_50, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.89/1.40  tff(f_56, axiom, (![A, B, C]: (k4_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_xboole_1)).
% 2.89/1.40  tff(f_85, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.89/1.40  tff(f_64, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 2.89/1.40  tff(f_88, negated_conjecture, ~(![A, B]: r1_tarski(k2_xboole_0(k1_zfmisc_1(A), k1_zfmisc_1(B)), k1_zfmisc_1(k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_zfmisc_1)).
% 2.89/1.40  tff(c_36, plain, (![A_21, B_22]: (r1_tarski(A_21, k2_xboole_0(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.89/1.40  tff(c_133, plain, (![A_56, B_57]: (k4_xboole_0(A_56, B_57)=k1_xboole_0 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.89/1.40  tff(c_141, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k2_xboole_0(A_21, B_22))=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_133])).
% 2.89/1.40  tff(c_26, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.89/1.40  tff(c_315, plain, (![A_82, B_83]: (k4_xboole_0(A_82, k4_xboole_0(A_82, B_83))=k3_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.89/1.40  tff(c_465, plain, (![A_88]: (k4_xboole_0(A_88, A_88)=k3_xboole_0(A_88, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_315])).
% 2.89/1.40  tff(c_28, plain, (![A_12, B_13, C_14]: (k4_xboole_0(k4_xboole_0(A_12, B_13), C_14)=k4_xboole_0(A_12, k2_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.89/1.40  tff(c_471, plain, (![A_88, C_14]: (k4_xboole_0(k3_xboole_0(A_88, k1_xboole_0), C_14)=k4_xboole_0(A_88, k2_xboole_0(A_88, C_14)))), inference(superposition, [status(thm), theory('equality')], [c_465, c_28])).
% 2.89/1.40  tff(c_552, plain, (![A_91, C_92]: (k4_xboole_0(k3_xboole_0(A_91, k1_xboole_0), C_92)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_141, c_471])).
% 2.89/1.40  tff(c_589, plain, (![A_91]: (k3_xboole_0(A_91, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_552, c_26])).
% 2.89/1.40  tff(c_346, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k3_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_315])).
% 2.89/1.40  tff(c_628, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_589, c_346])).
% 2.89/1.40  tff(c_980, plain, (![A_110, B_111, C_112]: (k3_xboole_0(k4_xboole_0(A_110, B_111), k4_xboole_0(A_110, C_112))=k4_xboole_0(A_110, k2_xboole_0(B_111, C_112)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.89/1.40  tff(c_1009, plain, (![A_11, B_111]: (k4_xboole_0(A_11, k2_xboole_0(B_111, A_11))=k3_xboole_0(k4_xboole_0(A_11, B_111), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_628, c_980])).
% 2.89/1.40  tff(c_1055, plain, (![A_11, B_111]: (k4_xboole_0(A_11, k2_xboole_0(B_111, A_11))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_589, c_1009])).
% 2.89/1.40  tff(c_22, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | k4_xboole_0(A_9, B_10)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.89/1.40  tff(c_56, plain, (![A_44, B_45]: (r1_tarski(k1_zfmisc_1(A_44), k1_zfmisc_1(B_45)) | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.89/1.40  tff(c_813, plain, (![A_104, C_105, B_106]: (r1_tarski(k2_xboole_0(A_104, C_105), B_106) | ~r1_tarski(C_105, B_106) | ~r1_tarski(A_104, B_106))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.89/1.40  tff(c_58, plain, (~r1_tarski(k2_xboole_0(k1_zfmisc_1('#skF_4'), k1_zfmisc_1('#skF_5')), k1_zfmisc_1(k2_xboole_0('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.89/1.40  tff(c_823, plain, (~r1_tarski(k1_zfmisc_1('#skF_5'), k1_zfmisc_1(k2_xboole_0('#skF_4', '#skF_5'))) | ~r1_tarski(k1_zfmisc_1('#skF_4'), k1_zfmisc_1(k2_xboole_0('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_813, c_58])).
% 2.89/1.40  tff(c_943, plain, (~r1_tarski(k1_zfmisc_1('#skF_4'), k1_zfmisc_1(k2_xboole_0('#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_823])).
% 2.89/1.40  tff(c_970, plain, (~r1_tarski('#skF_4', k2_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_56, c_943])).
% 2.89/1.40  tff(c_977, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_970])).
% 2.89/1.40  tff(c_978, plain, (~r1_tarski(k1_zfmisc_1('#skF_5'), k1_zfmisc_1(k2_xboole_0('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_823])).
% 2.89/1.40  tff(c_1158, plain, (~r1_tarski('#skF_5', k2_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_56, c_978])).
% 2.89/1.40  tff(c_1162, plain, (k4_xboole_0('#skF_5', k2_xboole_0('#skF_4', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_1158])).
% 2.89/1.40  tff(c_1166, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1055, c_1162])).
% 2.89/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.40  
% 2.89/1.40  Inference rules
% 2.89/1.40  ----------------------
% 2.89/1.40  #Ref     : 0
% 2.89/1.40  #Sup     : 267
% 2.89/1.40  #Fact    : 0
% 2.89/1.40  #Define  : 0
% 2.89/1.40  #Split   : 1
% 2.89/1.40  #Chain   : 0
% 2.89/1.40  #Close   : 0
% 2.89/1.40  
% 2.89/1.40  Ordering : KBO
% 2.89/1.40  
% 2.89/1.40  Simplification rules
% 2.89/1.40  ----------------------
% 2.89/1.40  #Subsume      : 11
% 2.89/1.40  #Demod        : 112
% 2.89/1.40  #Tautology    : 161
% 2.89/1.40  #SimpNegUnit  : 6
% 2.89/1.40  #BackRed      : 8
% 2.89/1.40  
% 2.89/1.40  #Partial instantiations: 0
% 2.89/1.40  #Strategies tried      : 1
% 2.89/1.40  
% 2.89/1.40  Timing (in seconds)
% 2.89/1.40  ----------------------
% 2.89/1.41  Preprocessing        : 0.32
% 2.89/1.41  Parsing              : 0.17
% 2.89/1.41  CNF conversion       : 0.02
% 2.89/1.41  Main loop            : 0.33
% 2.89/1.41  Inferencing          : 0.12
% 2.89/1.41  Reduction            : 0.11
% 2.89/1.41  Demodulation         : 0.08
% 2.89/1.41  BG Simplification    : 0.02
% 2.89/1.41  Subsumption          : 0.05
% 2.89/1.41  Abstraction          : 0.02
% 2.89/1.41  MUC search           : 0.00
% 2.89/1.41  Cooper               : 0.00
% 2.89/1.41  Total                : 0.68
% 2.89/1.41  Index Insertion      : 0.00
% 2.89/1.41  Index Deletion       : 0.00
% 2.89/1.41  Index Matching       : 0.00
% 2.89/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
