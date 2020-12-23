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
% DateTime   : Thu Dec  3 10:10:28 EST 2020

% Result     : Theorem 5.78s
% Output     : CNFRefutation 5.84s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 157 expanded)
%              Number of leaves         :   28 (  65 expanded)
%              Depth                    :   11
%              Number of atoms          :   53 ( 204 expanded)
%              Number of equality atoms :   40 ( 176 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_28,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] : k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A,B,C)))) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_mcart_1)).

tff(f_43,axiom,(
    ! [A,B] : ~ v1_xboole_0(k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_xboole_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_184,plain,(
    ! [A_69,B_70,C_71] : k2_zfmisc_1(k2_tarski(A_69,B_70),k1_tarski(C_71)) = k2_tarski(k4_tarski(A_69,C_71),k4_tarski(B_70,C_71)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_243,plain,(
    ! [A_69,C_71] : k2_zfmisc_1(k2_tarski(A_69,A_69),k1_tarski(C_71)) = k1_tarski(k4_tarski(A_69,C_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_184])).

tff(c_267,plain,(
    ! [A_77,C_78] : k2_zfmisc_1(k1_tarski(A_77),k1_tarski(C_78)) = k1_tarski(k4_tarski(A_77,C_78)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_243])).

tff(c_26,plain,(
    ! [A_34,B_35] :
      ( k1_relat_1(k2_zfmisc_1(A_34,B_35)) = A_34
      | k1_xboole_0 = B_35
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_276,plain,(
    ! [A_77,C_78] :
      ( k1_relat_1(k1_tarski(k4_tarski(A_77,C_78))) = k1_tarski(A_77)
      | k1_tarski(C_78) = k1_xboole_0
      | k1_tarski(A_77) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_26])).

tff(c_28,plain,(
    ! [A_36,B_37,C_38] : k4_tarski(k4_tarski(A_36,B_37),C_38) = k3_mcart_1(A_36,B_37,C_38) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_368,plain,(
    ! [A_115,C_116] :
      ( k1_relat_1(k1_tarski(k4_tarski(A_115,C_116))) = k1_tarski(A_115)
      | k1_tarski(C_116) = k1_xboole_0
      | k1_tarski(A_115) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_26])).

tff(c_1839,plain,(
    ! [A_292,B_293,C_294] :
      ( k1_relat_1(k1_tarski(k3_mcart_1(A_292,B_293,C_294))) = k1_tarski(k4_tarski(A_292,B_293))
      | k1_tarski(C_294) = k1_xboole_0
      | k1_tarski(k4_tarski(A_292,B_293)) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_368])).

tff(c_30,plain,(
    k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3')))) != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1845,plain,
    ( k1_relat_1(k1_tarski(k4_tarski('#skF_1','#skF_2'))) != k1_tarski('#skF_1')
    | k1_tarski('#skF_3') = k1_xboole_0
    | k1_tarski(k4_tarski('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1839,c_30])).

tff(c_1855,plain,(
    k1_relat_1(k1_tarski(k4_tarski('#skF_1','#skF_2'))) != k1_tarski('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1845])).

tff(c_1859,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_1855])).

tff(c_1860,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1859])).

tff(c_32,plain,(
    ! [A_41] : k2_tarski(A_41,A_41) = k1_tarski(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_18,plain,(
    ! [A_29,B_30] : ~ v1_xboole_0(k2_tarski(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_37,plain,(
    ! [A_41] : ~ v1_xboole_0(k1_tarski(A_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_18])).

tff(c_2097,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1860,c_37])).

tff(c_2102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2097])).

tff(c_2103,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1859])).

tff(c_2339,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2103,c_37])).

tff(c_2344,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2339])).

tff(c_2345,plain,
    ( k1_tarski(k4_tarski('#skF_1','#skF_2')) = k1_xboole_0
    | k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1845])).

tff(c_2607,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2345])).

tff(c_2848,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2607,c_37])).

tff(c_2853,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2848])).

tff(c_2854,plain,(
    k1_tarski(k4_tarski('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2345])).

tff(c_3088,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2854,c_37])).

tff(c_3095,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3088])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:39:22 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.78/2.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.78/2.10  
% 5.78/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.78/2.10  %$ v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.78/2.10  
% 5.78/2.10  %Foreground sorts:
% 5.78/2.10  
% 5.78/2.10  
% 5.78/2.10  %Background operators:
% 5.78/2.10  
% 5.78/2.10  
% 5.78/2.10  %Foreground operators:
% 5.78/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.78/2.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.78/2.10  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.78/2.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.78/2.10  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 5.78/2.10  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.78/2.10  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.78/2.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.78/2.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.78/2.10  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.78/2.10  tff('#skF_2', type, '#skF_2': $i).
% 5.78/2.10  tff('#skF_3', type, '#skF_3': $i).
% 5.78/2.10  tff('#skF_1', type, '#skF_1': $i).
% 5.78/2.10  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.78/2.10  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.78/2.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.78/2.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.78/2.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.78/2.11  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.78/2.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.78/2.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.78/2.11  
% 5.84/2.12  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.84/2.12  tff(f_28, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.84/2.12  tff(f_47, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 5.84/2.12  tff(f_59, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 5.84/2.12  tff(f_61, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 5.84/2.12  tff(f_64, negated_conjecture, ~(![A, B, C]: (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A, B, C)))) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_mcart_1)).
% 5.84/2.12  tff(f_43, axiom, (![A, B]: ~v1_xboole_0(k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_xboole_0)).
% 5.84/2.12  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.84/2.12  tff(c_4, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 5.84/2.12  tff(c_184, plain, (![A_69, B_70, C_71]: (k2_zfmisc_1(k2_tarski(A_69, B_70), k1_tarski(C_71))=k2_tarski(k4_tarski(A_69, C_71), k4_tarski(B_70, C_71)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.84/2.12  tff(c_243, plain, (![A_69, C_71]: (k2_zfmisc_1(k2_tarski(A_69, A_69), k1_tarski(C_71))=k1_tarski(k4_tarski(A_69, C_71)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_184])).
% 5.84/2.12  tff(c_267, plain, (![A_77, C_78]: (k2_zfmisc_1(k1_tarski(A_77), k1_tarski(C_78))=k1_tarski(k4_tarski(A_77, C_78)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_243])).
% 5.84/2.12  tff(c_26, plain, (![A_34, B_35]: (k1_relat_1(k2_zfmisc_1(A_34, B_35))=A_34 | k1_xboole_0=B_35 | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.84/2.12  tff(c_276, plain, (![A_77, C_78]: (k1_relat_1(k1_tarski(k4_tarski(A_77, C_78)))=k1_tarski(A_77) | k1_tarski(C_78)=k1_xboole_0 | k1_tarski(A_77)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_267, c_26])).
% 5.84/2.12  tff(c_28, plain, (![A_36, B_37, C_38]: (k4_tarski(k4_tarski(A_36, B_37), C_38)=k3_mcart_1(A_36, B_37, C_38))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.84/2.12  tff(c_368, plain, (![A_115, C_116]: (k1_relat_1(k1_tarski(k4_tarski(A_115, C_116)))=k1_tarski(A_115) | k1_tarski(C_116)=k1_xboole_0 | k1_tarski(A_115)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_267, c_26])).
% 5.84/2.12  tff(c_1839, plain, (![A_292, B_293, C_294]: (k1_relat_1(k1_tarski(k3_mcart_1(A_292, B_293, C_294)))=k1_tarski(k4_tarski(A_292, B_293)) | k1_tarski(C_294)=k1_xboole_0 | k1_tarski(k4_tarski(A_292, B_293))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_368])).
% 5.84/2.12  tff(c_30, plain, (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))))!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.84/2.12  tff(c_1845, plain, (k1_relat_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')))!=k1_tarski('#skF_1') | k1_tarski('#skF_3')=k1_xboole_0 | k1_tarski(k4_tarski('#skF_1', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1839, c_30])).
% 5.84/2.12  tff(c_1855, plain, (k1_relat_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')))!=k1_tarski('#skF_1')), inference(splitLeft, [status(thm)], [c_1845])).
% 5.84/2.12  tff(c_1859, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_tarski('#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_276, c_1855])).
% 5.84/2.12  tff(c_1860, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1859])).
% 5.84/2.12  tff(c_32, plain, (![A_41]: (k2_tarski(A_41, A_41)=k1_tarski(A_41))), inference(cnfTransformation, [status(thm)], [f_28])).
% 5.84/2.12  tff(c_18, plain, (![A_29, B_30]: (~v1_xboole_0(k2_tarski(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.84/2.12  tff(c_37, plain, (![A_41]: (~v1_xboole_0(k1_tarski(A_41)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_18])).
% 5.84/2.12  tff(c_2097, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1860, c_37])).
% 5.84/2.12  tff(c_2102, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_2097])).
% 5.84/2.12  tff(c_2103, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1859])).
% 5.84/2.12  tff(c_2339, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2103, c_37])).
% 5.84/2.12  tff(c_2344, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_2339])).
% 5.84/2.12  tff(c_2345, plain, (k1_tarski(k4_tarski('#skF_1', '#skF_2'))=k1_xboole_0 | k1_tarski('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1845])).
% 5.84/2.12  tff(c_2607, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2345])).
% 5.84/2.12  tff(c_2848, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2607, c_37])).
% 5.84/2.12  tff(c_2853, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_2848])).
% 5.84/2.12  tff(c_2854, plain, (k1_tarski(k4_tarski('#skF_1', '#skF_2'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_2345])).
% 5.84/2.12  tff(c_3088, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2854, c_37])).
% 5.84/2.12  tff(c_3095, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_3088])).
% 5.84/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.84/2.12  
% 5.84/2.12  Inference rules
% 5.84/2.12  ----------------------
% 5.84/2.12  #Ref     : 0
% 5.84/2.12  #Sup     : 1168
% 5.84/2.12  #Fact    : 0
% 5.84/2.12  #Define  : 0
% 5.84/2.12  #Split   : 3
% 5.84/2.12  #Chain   : 0
% 5.84/2.12  #Close   : 0
% 5.84/2.12  
% 5.84/2.12  Ordering : KBO
% 5.84/2.12  
% 5.84/2.12  Simplification rules
% 5.84/2.12  ----------------------
% 5.84/2.12  #Subsume      : 225
% 5.84/2.12  #Demod        : 390
% 5.84/2.12  #Tautology    : 135
% 5.84/2.12  #SimpNegUnit  : 0
% 5.84/2.12  #BackRed      : 4
% 5.84/2.12  
% 5.84/2.12  #Partial instantiations: 0
% 5.84/2.12  #Strategies tried      : 1
% 5.84/2.12  
% 5.84/2.12  Timing (in seconds)
% 5.84/2.12  ----------------------
% 5.84/2.12  Preprocessing        : 0.33
% 5.84/2.12  Parsing              : 0.18
% 5.84/2.12  CNF conversion       : 0.02
% 5.84/2.12  Main loop            : 1.00
% 5.84/2.12  Inferencing          : 0.31
% 5.84/2.12  Reduction            : 0.39
% 5.84/2.12  Demodulation         : 0.33
% 5.84/2.12  BG Simplification    : 0.05
% 5.84/2.12  Subsumption          : 0.21
% 5.84/2.12  Abstraction          : 0.06
% 5.84/2.12  MUC search           : 0.00
% 5.84/2.12  Cooper               : 0.00
% 5.84/2.12  Total                : 1.36
% 5.84/2.12  Index Insertion      : 0.00
% 5.84/2.12  Index Deletion       : 0.00
% 5.84/2.12  Index Matching       : 0.00
% 5.84/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
