%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:57 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.39s
% Verified   : 
% Statistics : Number of formulae       :   57 (  88 expanded)
%              Number of leaves         :   20 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   53 (  94 expanded)
%              Number of equality atoms :   33 (  59 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_xboole_0(A,B)
          | r1_xboole_0(C,D) )
       => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,k3_xboole_0(A,B)),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_xboole_1)).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_807,plain,(
    ! [A_64,B_65] : k4_xboole_0(A_64,k4_xboole_0(A_64,B_65)) = k3_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_825,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k3_xboole_0(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_807])).

tff(c_828,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_825])).

tff(c_18,plain,(
    ! [B_10] : k2_zfmisc_1(k1_xboole_0,B_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_108,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k4_xboole_0(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_126,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k3_xboole_0(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_108])).

tff(c_129,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_126])).

tff(c_24,plain,
    ( r1_xboole_0('#skF_3','#skF_4')
    | r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_63,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_75,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(A_24,B_25) = A_24
      | ~ r1_xboole_0(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_92,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_63,c_75])).

tff(c_123,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_108])).

tff(c_287,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_123])).

tff(c_151,plain,(
    ! [A_31,C_32,B_33,D_34] : k3_xboole_0(k2_zfmisc_1(A_31,C_32),k2_zfmisc_1(B_33,D_34)) = k2_zfmisc_1(k3_xboole_0(A_31,B_33),k3_xboole_0(C_32,D_34)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_7,B_8] : r1_xboole_0(k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)),B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_692,plain,(
    ! [A_53,C_54,B_55,D_56] : r1_xboole_0(k4_xboole_0(k2_zfmisc_1(A_53,C_54),k2_zfmisc_1(k3_xboole_0(A_53,B_55),k3_xboole_0(C_54,D_56))),k2_zfmisc_1(B_55,D_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_12])).

tff(c_710,plain,(
    ! [C_54,D_56] : r1_xboole_0(k4_xboole_0(k2_zfmisc_1('#skF_1',C_54),k2_zfmisc_1(k1_xboole_0,k3_xboole_0(C_54,D_56))),k2_zfmisc_1('#skF_2',D_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_692])).

tff(c_755,plain,(
    ! [C_54,D_56] : r1_xboole_0(k2_zfmisc_1('#skF_1',C_54),k2_zfmisc_1('#skF_2',D_56)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_18,c_710])).

tff(c_22,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_1','#skF_3'),k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_767,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_755,c_22])).

tff(c_768,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_776,plain,(
    ! [A_60,B_61] :
      ( k4_xboole_0(A_60,B_61) = A_60
      | ~ r1_xboole_0(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_789,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_768,c_776])).

tff(c_822,plain,(
    k4_xboole_0('#skF_3','#skF_3') = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_789,c_807])).

tff(c_961,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_828,c_822])).

tff(c_1040,plain,(
    ! [A_77,C_78,B_79,D_80] : k3_xboole_0(k2_zfmisc_1(A_77,C_78),k2_zfmisc_1(B_79,D_80)) = k2_zfmisc_1(k3_xboole_0(A_77,B_79),k3_xboole_0(C_78,D_80)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_816,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,k4_xboole_0(A_3,B_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_807])).

tff(c_2692,plain,(
    ! [A_113,C_114,B_115,D_116] : k4_xboole_0(k2_zfmisc_1(A_113,C_114),k2_zfmisc_1(k3_xboole_0(A_113,B_115),k3_xboole_0(C_114,D_116))) = k3_xboole_0(k2_zfmisc_1(A_113,C_114),k4_xboole_0(k2_zfmisc_1(A_113,C_114),k2_zfmisc_1(B_115,D_116))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1040,c_816])).

tff(c_2791,plain,(
    ! [A_113,B_115] : k3_xboole_0(k2_zfmisc_1(A_113,'#skF_3'),k4_xboole_0(k2_zfmisc_1(A_113,'#skF_3'),k2_zfmisc_1(B_115,'#skF_4'))) = k4_xboole_0(k2_zfmisc_1(A_113,'#skF_3'),k2_zfmisc_1(k3_xboole_0(A_113,B_115),k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_961,c_2692])).

tff(c_3079,plain,(
    ! [A_123,B_124] : k3_xboole_0(k2_zfmisc_1(A_123,'#skF_3'),k4_xboole_0(k2_zfmisc_1(A_123,'#skF_3'),k2_zfmisc_1(B_124,'#skF_4'))) = k2_zfmisc_1(A_123,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_16,c_2791])).

tff(c_970,plain,(
    ! [A_7,B_8] : r1_xboole_0(k3_xboole_0(A_7,k4_xboole_0(A_7,B_8)),B_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_816,c_12])).

tff(c_3167,plain,(
    ! [A_123,B_124] : r1_xboole_0(k2_zfmisc_1(A_123,'#skF_3'),k2_zfmisc_1(B_124,'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3079,c_970])).

tff(c_3222,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3167,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:19:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.01/1.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.31/1.76  
% 4.31/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.31/1.76  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.31/1.76  
% 4.31/1.76  %Foreground sorts:
% 4.31/1.76  
% 4.31/1.76  
% 4.31/1.76  %Background operators:
% 4.31/1.76  
% 4.31/1.76  
% 4.31/1.76  %Foreground operators:
% 4.31/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.31/1.76  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.31/1.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.31/1.76  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.31/1.76  tff('#skF_2', type, '#skF_2': $i).
% 4.31/1.76  tff('#skF_3', type, '#skF_3': $i).
% 4.31/1.76  tff('#skF_1', type, '#skF_1': $i).
% 4.31/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.31/1.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.31/1.76  tff('#skF_4', type, '#skF_4': $i).
% 4.31/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.31/1.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.31/1.76  
% 4.39/1.78  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.39/1.78  tff(f_43, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.39/1.78  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.39/1.78  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.39/1.78  tff(f_52, negated_conjecture, ~(![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 4.39/1.78  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.39/1.78  tff(f_45, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 4.39/1.78  tff(f_37, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, k3_xboole_0(A, B)), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_xboole_1)).
% 4.39/1.78  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.39/1.78  tff(c_16, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.39/1.78  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.39/1.78  tff(c_807, plain, (![A_64, B_65]: (k4_xboole_0(A_64, k4_xboole_0(A_64, B_65))=k3_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.39/1.78  tff(c_825, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k3_xboole_0(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_807])).
% 4.39/1.78  tff(c_828, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_825])).
% 4.39/1.78  tff(c_18, plain, (![B_10]: (k2_zfmisc_1(k1_xboole_0, B_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.39/1.78  tff(c_108, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k4_xboole_0(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.39/1.78  tff(c_126, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k3_xboole_0(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_108])).
% 4.39/1.78  tff(c_129, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_126])).
% 4.39/1.78  tff(c_24, plain, (r1_xboole_0('#skF_3', '#skF_4') | r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.39/1.78  tff(c_63, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_24])).
% 4.39/1.78  tff(c_75, plain, (![A_24, B_25]: (k4_xboole_0(A_24, B_25)=A_24 | ~r1_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.39/1.78  tff(c_92, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_63, c_75])).
% 4.39/1.78  tff(c_123, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_92, c_108])).
% 4.39/1.78  tff(c_287, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_129, c_123])).
% 4.39/1.78  tff(c_151, plain, (![A_31, C_32, B_33, D_34]: (k3_xboole_0(k2_zfmisc_1(A_31, C_32), k2_zfmisc_1(B_33, D_34))=k2_zfmisc_1(k3_xboole_0(A_31, B_33), k3_xboole_0(C_32, D_34)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.39/1.78  tff(c_12, plain, (![A_7, B_8]: (r1_xboole_0(k4_xboole_0(A_7, k3_xboole_0(A_7, B_8)), B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.39/1.78  tff(c_692, plain, (![A_53, C_54, B_55, D_56]: (r1_xboole_0(k4_xboole_0(k2_zfmisc_1(A_53, C_54), k2_zfmisc_1(k3_xboole_0(A_53, B_55), k3_xboole_0(C_54, D_56))), k2_zfmisc_1(B_55, D_56)))), inference(superposition, [status(thm), theory('equality')], [c_151, c_12])).
% 4.39/1.78  tff(c_710, plain, (![C_54, D_56]: (r1_xboole_0(k4_xboole_0(k2_zfmisc_1('#skF_1', C_54), k2_zfmisc_1(k1_xboole_0, k3_xboole_0(C_54, D_56))), k2_zfmisc_1('#skF_2', D_56)))), inference(superposition, [status(thm), theory('equality')], [c_287, c_692])).
% 4.39/1.78  tff(c_755, plain, (![C_54, D_56]: (r1_xboole_0(k2_zfmisc_1('#skF_1', C_54), k2_zfmisc_1('#skF_2', D_56)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_18, c_710])).
% 4.39/1.78  tff(c_22, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_3'), k2_zfmisc_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.39/1.78  tff(c_767, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_755, c_22])).
% 4.39/1.78  tff(c_768, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_24])).
% 4.39/1.78  tff(c_776, plain, (![A_60, B_61]: (k4_xboole_0(A_60, B_61)=A_60 | ~r1_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.39/1.78  tff(c_789, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_768, c_776])).
% 4.39/1.78  tff(c_822, plain, (k4_xboole_0('#skF_3', '#skF_3')=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_789, c_807])).
% 4.39/1.78  tff(c_961, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_828, c_822])).
% 4.39/1.78  tff(c_1040, plain, (![A_77, C_78, B_79, D_80]: (k3_xboole_0(k2_zfmisc_1(A_77, C_78), k2_zfmisc_1(B_79, D_80))=k2_zfmisc_1(k3_xboole_0(A_77, B_79), k3_xboole_0(C_78, D_80)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.39/1.78  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.39/1.78  tff(c_816, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k3_xboole_0(A_3, k4_xboole_0(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_807])).
% 4.39/1.78  tff(c_2692, plain, (![A_113, C_114, B_115, D_116]: (k4_xboole_0(k2_zfmisc_1(A_113, C_114), k2_zfmisc_1(k3_xboole_0(A_113, B_115), k3_xboole_0(C_114, D_116)))=k3_xboole_0(k2_zfmisc_1(A_113, C_114), k4_xboole_0(k2_zfmisc_1(A_113, C_114), k2_zfmisc_1(B_115, D_116))))), inference(superposition, [status(thm), theory('equality')], [c_1040, c_816])).
% 4.39/1.78  tff(c_2791, plain, (![A_113, B_115]: (k3_xboole_0(k2_zfmisc_1(A_113, '#skF_3'), k4_xboole_0(k2_zfmisc_1(A_113, '#skF_3'), k2_zfmisc_1(B_115, '#skF_4')))=k4_xboole_0(k2_zfmisc_1(A_113, '#skF_3'), k2_zfmisc_1(k3_xboole_0(A_113, B_115), k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_961, c_2692])).
% 4.39/1.78  tff(c_3079, plain, (![A_123, B_124]: (k3_xboole_0(k2_zfmisc_1(A_123, '#skF_3'), k4_xboole_0(k2_zfmisc_1(A_123, '#skF_3'), k2_zfmisc_1(B_124, '#skF_4')))=k2_zfmisc_1(A_123, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_16, c_2791])).
% 4.39/1.78  tff(c_970, plain, (![A_7, B_8]: (r1_xboole_0(k3_xboole_0(A_7, k4_xboole_0(A_7, B_8)), B_8))), inference(demodulation, [status(thm), theory('equality')], [c_816, c_12])).
% 4.39/1.78  tff(c_3167, plain, (![A_123, B_124]: (r1_xboole_0(k2_zfmisc_1(A_123, '#skF_3'), k2_zfmisc_1(B_124, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_3079, c_970])).
% 4.39/1.78  tff(c_3222, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3167, c_22])).
% 4.39/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.39/1.78  
% 4.39/1.78  Inference rules
% 4.39/1.78  ----------------------
% 4.39/1.78  #Ref     : 0
% 4.39/1.78  #Sup     : 795
% 4.39/1.78  #Fact    : 0
% 4.39/1.78  #Define  : 0
% 4.39/1.78  #Split   : 1
% 4.39/1.78  #Chain   : 0
% 4.39/1.78  #Close   : 0
% 4.39/1.78  
% 4.39/1.78  Ordering : KBO
% 4.39/1.78  
% 4.39/1.78  Simplification rules
% 4.39/1.78  ----------------------
% 4.39/1.78  #Subsume      : 0
% 4.39/1.78  #Demod        : 1732
% 4.39/1.78  #Tautology    : 594
% 4.39/1.78  #SimpNegUnit  : 0
% 4.39/1.78  #BackRed      : 4
% 4.39/1.78  
% 4.39/1.78  #Partial instantiations: 0
% 4.39/1.78  #Strategies tried      : 1
% 4.39/1.78  
% 4.39/1.78  Timing (in seconds)
% 4.39/1.78  ----------------------
% 4.39/1.78  Preprocessing        : 0.28
% 4.39/1.78  Parsing              : 0.15
% 4.39/1.78  CNF conversion       : 0.02
% 4.39/1.78  Main loop            : 0.72
% 4.39/1.78  Inferencing          : 0.24
% 4.39/1.78  Reduction            : 0.33
% 4.39/1.78  Demodulation         : 0.28
% 4.39/1.78  BG Simplification    : 0.03
% 4.39/1.78  Subsumption          : 0.07
% 4.39/1.78  Abstraction          : 0.05
% 4.39/1.78  MUC search           : 0.00
% 4.39/1.78  Cooper               : 0.00
% 4.39/1.78  Total                : 1.04
% 4.39/1.78  Index Insertion      : 0.00
% 4.39/1.78  Index Deletion       : 0.00
% 4.39/1.78  Index Matching       : 0.00
% 4.39/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
