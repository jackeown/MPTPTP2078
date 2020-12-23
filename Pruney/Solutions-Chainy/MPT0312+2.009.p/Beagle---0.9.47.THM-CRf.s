%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:54 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 108 expanded)
%              Number of leaves         :   20 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :   54 ( 140 expanded)
%              Number of equality atoms :   36 (  85 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => k3_xboole_0(k2_zfmisc_1(A,D),k2_zfmisc_1(B,C)) = k2_zfmisc_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(c_16,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_153,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(A_26,B_27) = k1_xboole_0
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_175,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_153])).

tff(c_244,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k4_xboole_0(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_392,plain,(
    ! [B_41] : k4_xboole_0(B_41,k1_xboole_0) = k3_xboole_0(B_41,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_244])).

tff(c_41,plain,(
    ! [B_20,A_21] : k3_xboole_0(B_20,A_21) = k3_xboole_0(A_21,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_59,plain,(
    ! [A_21,B_20] : r1_tarski(k3_xboole_0(A_21,B_20),B_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_14])).

tff(c_421,plain,(
    ! [B_41] : r1_tarski(k4_xboole_0(B_41,k1_xboole_0),B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_392,c_59])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_198,plain,(
    ! [B_31,A_32] :
      ( B_31 = A_32
      | ~ r1_tarski(B_31,A_32)
      | ~ r1_tarski(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_780,plain,(
    ! [B_52,A_53] :
      ( B_52 = A_53
      | ~ r1_tarski(B_52,A_53)
      | k4_xboole_0(A_53,B_52) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_198])).

tff(c_786,plain,(
    ! [B_41] :
      ( k4_xboole_0(B_41,k1_xboole_0) = B_41
      | k4_xboole_0(B_41,k4_xboole_0(B_41,k1_xboole_0)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_421,c_780])).

tff(c_811,plain,(
    ! [B_41] : k4_xboole_0(B_41,k1_xboole_0) = B_41 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18,c_786])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_176,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_153])).

tff(c_270,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_244])).

tff(c_282,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_270])).

tff(c_826,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_811,c_282])).

tff(c_276,plain,(
    ! [B_4] : k4_xboole_0(B_4,k1_xboole_0) = k3_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_244])).

tff(c_825,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_811,c_276])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_177,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_153])).

tff(c_273,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_244])).

tff(c_391,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k3_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_273])).

tff(c_20,plain,(
    ! [A_12,C_14,B_13,D_15] : k3_xboole_0(k2_zfmisc_1(A_12,C_14),k2_zfmisc_1(B_13,D_15)) = k2_zfmisc_1(k3_xboole_0(A_12,B_13),k3_xboole_0(C_14,D_15)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_4'),k2_zfmisc_1('#skF_2','#skF_3')) != k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_27,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_4','#skF_3')) != k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_534,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_1'),k3_xboole_0('#skF_4','#skF_3')) != k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_27])).

tff(c_886,plain,(
    k2_zfmisc_1('#skF_1',k3_xboole_0('#skF_4','#skF_3')) != k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_825,c_534])).

tff(c_978,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_826,c_886])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:17:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.35  
% 2.49/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.35  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.49/1.35  
% 2.49/1.35  %Foreground sorts:
% 2.49/1.35  
% 2.49/1.35  
% 2.49/1.35  %Background operators:
% 2.49/1.35  
% 2.49/1.35  
% 2.49/1.35  %Foreground operators:
% 2.49/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.49/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.49/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.49/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.49/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.49/1.35  
% 2.69/1.36  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.69/1.36  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.69/1.36  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.69/1.36  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.69/1.36  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.69/1.36  tff(f_39, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.69/1.36  tff(f_52, negated_conjecture, ~(![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => (k3_xboole_0(k2_zfmisc_1(A, D), k2_zfmisc_1(B, C)) = k2_zfmisc_1(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t124_zfmisc_1)).
% 2.69/1.36  tff(f_45, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 2.69/1.36  tff(c_16, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.69/1.36  tff(c_18, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.69/1.36  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.69/1.36  tff(c_153, plain, (![A_26, B_27]: (k4_xboole_0(A_26, B_27)=k1_xboole_0 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.69/1.36  tff(c_175, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_153])).
% 2.69/1.36  tff(c_244, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k4_xboole_0(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.69/1.36  tff(c_392, plain, (![B_41]: (k4_xboole_0(B_41, k1_xboole_0)=k3_xboole_0(B_41, B_41))), inference(superposition, [status(thm), theory('equality')], [c_175, c_244])).
% 2.69/1.36  tff(c_41, plain, (![B_20, A_21]: (k3_xboole_0(B_20, A_21)=k3_xboole_0(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.69/1.36  tff(c_14, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.69/1.36  tff(c_59, plain, (![A_21, B_20]: (r1_tarski(k3_xboole_0(A_21, B_20), B_20))), inference(superposition, [status(thm), theory('equality')], [c_41, c_14])).
% 2.69/1.36  tff(c_421, plain, (![B_41]: (r1_tarski(k4_xboole_0(B_41, k1_xboole_0), B_41))), inference(superposition, [status(thm), theory('equality')], [c_392, c_59])).
% 2.69/1.36  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.69/1.36  tff(c_198, plain, (![B_31, A_32]: (B_31=A_32 | ~r1_tarski(B_31, A_32) | ~r1_tarski(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.69/1.36  tff(c_780, plain, (![B_52, A_53]: (B_52=A_53 | ~r1_tarski(B_52, A_53) | k4_xboole_0(A_53, B_52)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_198])).
% 2.69/1.36  tff(c_786, plain, (![B_41]: (k4_xboole_0(B_41, k1_xboole_0)=B_41 | k4_xboole_0(B_41, k4_xboole_0(B_41, k1_xboole_0))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_421, c_780])).
% 2.69/1.36  tff(c_811, plain, (![B_41]: (k4_xboole_0(B_41, k1_xboole_0)=B_41)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18, c_786])).
% 2.69/1.36  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.69/1.36  tff(c_24, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.69/1.36  tff(c_176, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_153])).
% 2.69/1.36  tff(c_270, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_176, c_244])).
% 2.69/1.36  tff(c_282, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k3_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_270])).
% 2.69/1.36  tff(c_826, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_811, c_282])).
% 2.69/1.36  tff(c_276, plain, (![B_4]: (k4_xboole_0(B_4, k1_xboole_0)=k3_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_175, c_244])).
% 2.69/1.36  tff(c_825, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_811, c_276])).
% 2.69/1.36  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.69/1.36  tff(c_177, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_153])).
% 2.69/1.36  tff(c_273, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_177, c_244])).
% 2.69/1.36  tff(c_391, plain, (k3_xboole_0('#skF_1', '#skF_2')=k3_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_276, c_273])).
% 2.69/1.36  tff(c_20, plain, (![A_12, C_14, B_13, D_15]: (k3_xboole_0(k2_zfmisc_1(A_12, C_14), k2_zfmisc_1(B_13, D_15))=k2_zfmisc_1(k3_xboole_0(A_12, B_13), k3_xboole_0(C_14, D_15)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.69/1.36  tff(c_22, plain, (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_2', '#skF_3'))!=k2_zfmisc_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.69/1.36  tff(c_27, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_4', '#skF_3'))!=k2_zfmisc_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 2.69/1.36  tff(c_534, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_1'), k3_xboole_0('#skF_4', '#skF_3'))!=k2_zfmisc_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_391, c_27])).
% 2.69/1.36  tff(c_886, plain, (k2_zfmisc_1('#skF_1', k3_xboole_0('#skF_4', '#skF_3'))!=k2_zfmisc_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_825, c_534])).
% 2.69/1.36  tff(c_978, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_826, c_886])).
% 2.69/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.36  
% 2.69/1.36  Inference rules
% 2.69/1.36  ----------------------
% 2.69/1.36  #Ref     : 0
% 2.69/1.36  #Sup     : 231
% 2.69/1.36  #Fact    : 0
% 2.69/1.36  #Define  : 0
% 2.69/1.36  #Split   : 2
% 2.69/1.36  #Chain   : 0
% 2.69/1.36  #Close   : 0
% 2.69/1.37  
% 2.69/1.37  Ordering : KBO
% 2.69/1.37  
% 2.69/1.37  Simplification rules
% 2.69/1.37  ----------------------
% 2.69/1.37  #Subsume      : 10
% 2.69/1.37  #Demod        : 133
% 2.69/1.37  #Tautology    : 165
% 2.69/1.37  #SimpNegUnit  : 0
% 2.69/1.37  #BackRed      : 13
% 2.69/1.37  
% 2.69/1.37  #Partial instantiations: 0
% 2.69/1.37  #Strategies tried      : 1
% 2.69/1.37  
% 2.69/1.37  Timing (in seconds)
% 2.69/1.37  ----------------------
% 2.69/1.37  Preprocessing        : 0.27
% 2.69/1.37  Parsing              : 0.14
% 2.69/1.37  CNF conversion       : 0.02
% 2.69/1.37  Main loop            : 0.32
% 2.69/1.37  Inferencing          : 0.11
% 2.69/1.37  Reduction            : 0.12
% 2.69/1.37  Demodulation         : 0.10
% 2.69/1.37  BG Simplification    : 0.01
% 2.69/1.37  Subsumption          : 0.05
% 2.69/1.37  Abstraction          : 0.02
% 2.69/1.37  MUC search           : 0.00
% 2.69/1.37  Cooper               : 0.00
% 2.69/1.37  Total                : 0.62
% 2.69/1.37  Index Insertion      : 0.00
% 2.69/1.37  Index Deletion       : 0.00
% 2.69/1.37  Index Matching       : 0.00
% 2.69/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
