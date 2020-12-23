%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:42 EST 2020

% Result     : Theorem 5.44s
% Output     : CNFRefutation 5.44s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 143 expanded)
%              Number of leaves         :   19 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :   74 ( 224 expanded)
%              Number of equality atoms :   19 (  52 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_50,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & ! [D] :
            ( ( r1_tarski(D,B)
              & r1_tarski(D,C) )
           => r1_tarski(D,A) ) )
     => A = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,k3_xboole_0(C,B)) = k3_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

tff(c_12,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_23,plain,(
    ! [A_23,B_24] :
      ( k2_xboole_0(A_23,B_24) = B_24
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_31,plain,(
    ! [A_11] : k2_xboole_0(k1_xboole_0,A_11) = A_11 ),
    inference(resolution,[status(thm)],[c_12,c_23])).

tff(c_80,plain,(
    ! [A_28,C_29,B_30] :
      ( r1_tarski(k2_xboole_0(A_28,C_29),k2_xboole_0(B_30,C_29))
      | ~ r1_tarski(A_28,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_92,plain,(
    ! [A_11,B_30] :
      ( r1_tarski(A_11,k2_xboole_0(B_30,A_11))
      | ~ r1_tarski(k1_xboole_0,B_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_80])).

tff(c_99,plain,(
    ! [A_31,B_32] : r1_tarski(A_31,k2_xboole_0(B_32,A_31)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_92])).

tff(c_108,plain,(
    ! [A_11] : r1_tarski(A_11,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_99])).

tff(c_16,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] :
      ( r1_tarski('#skF_1'(A_7,B_8,C_9),C_9)
      | k3_xboole_0(B_8,C_9) = A_7
      | ~ r1_tarski(A_7,C_9)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_5625,plain,(
    ! [A_173,B_174,C_175] :
      ( ~ r1_tarski('#skF_1'(A_173,B_174,C_175),A_173)
      | k3_xboole_0(B_174,C_175) = A_173
      | ~ r1_tarski(A_173,C_175)
      | ~ r1_tarski(A_173,B_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_5629,plain,(
    ! [B_8,C_9] :
      ( k3_xboole_0(B_8,C_9) = C_9
      | ~ r1_tarski(C_9,C_9)
      | ~ r1_tarski(C_9,B_8) ) ),
    inference(resolution,[status(thm)],[c_8,c_5625])).

tff(c_5645,plain,(
    ! [B_176,C_177] :
      ( k3_xboole_0(B_176,C_177) = C_177
      | ~ r1_tarski(C_177,B_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_5629])).

tff(c_5802,plain,(
    ! [A_180,B_181] : k3_xboole_0(k2_xboole_0(A_180,B_181),A_180) = A_180 ),
    inference(resolution,[status(thm)],[c_16,c_5645])).

tff(c_14,plain,(
    ! [A_12,C_14,B_13] :
      ( k3_xboole_0(k2_xboole_0(A_12,C_14),B_13) = k2_xboole_0(A_12,k3_xboole_0(C_14,B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_5818,plain,(
    ! [A_180,B_181] :
      ( k2_xboole_0(A_180,k3_xboole_0(B_181,A_180)) = A_180
      | ~ r1_tarski(A_180,A_180) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5802,c_14])).

tff(c_5986,plain,(
    ! [A_184,B_185] : k2_xboole_0(A_184,k3_xboole_0(B_185,A_184)) = A_184 ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_5818])).

tff(c_98,plain,(
    ! [A_11,B_30] : r1_tarski(A_11,k2_xboole_0(B_30,A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_92])).

tff(c_6085,plain,(
    ! [B_185,A_184] : r1_tarski(k3_xboole_0(B_185,A_184),A_184) ),
    inference(superposition,[status(thm),theory(equality)],[c_5986,c_98])).

tff(c_2159,plain,(
    ! [A_99,B_100,C_101] :
      ( ~ r1_tarski('#skF_1'(A_99,B_100,C_101),A_99)
      | k3_xboole_0(B_100,C_101) = A_99
      | ~ r1_tarski(A_99,C_101)
      | ~ r1_tarski(A_99,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2167,plain,(
    ! [B_8,C_9] :
      ( k3_xboole_0(B_8,C_9) = C_9
      | ~ r1_tarski(C_9,C_9)
      | ~ r1_tarski(C_9,B_8) ) ),
    inference(resolution,[status(thm)],[c_8,c_2159])).

tff(c_2808,plain,(
    ! [B_114,C_115] :
      ( k3_xboole_0(B_114,C_115) = C_115
      | ~ r1_tarski(C_115,B_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_2167])).

tff(c_3012,plain,(
    ! [A_119,B_120] : k3_xboole_0(k2_xboole_0(A_119,B_120),A_119) = A_119 ),
    inference(resolution,[status(thm)],[c_16,c_2808])).

tff(c_3032,plain,(
    ! [A_119,B_120] :
      ( k2_xboole_0(A_119,k3_xboole_0(B_120,A_119)) = A_119
      | ~ r1_tarski(A_119,A_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3012,c_14])).

tff(c_3105,plain,(
    ! [A_121,B_122] : k2_xboole_0(A_121,k3_xboole_0(B_122,A_121)) = A_121 ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_3032])).

tff(c_3209,plain,(
    ! [B_122,A_121] : r1_tarski(k3_xboole_0(B_122,A_121),A_121) ),
    inference(superposition,[status(thm),theory(equality)],[c_3105,c_98])).

tff(c_333,plain,(
    ! [A_43,C_44,B_45,D_46] :
      ( r1_tarski(k2_xboole_0(A_43,C_44),k2_xboole_0(B_45,D_46))
      | ~ r1_tarski(C_44,D_46)
      | ~ r1_tarski(A_43,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ~ r1_tarski(k2_xboole_0(k3_xboole_0('#skF_2','#skF_3'),k3_xboole_0('#skF_2','#skF_4')),k2_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_370,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_4'),'#skF_4')
    | ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_333,c_20])).

tff(c_490,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_370])).

tff(c_3521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3209,c_490])).

tff(c_3522,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_2','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_370])).

tff(c_6170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6085,c_3522])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:48:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.44/2.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.44/2.05  
% 5.44/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.44/2.05  %$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 5.44/2.05  
% 5.44/2.05  %Foreground sorts:
% 5.44/2.05  
% 5.44/2.05  
% 5.44/2.05  %Background operators:
% 5.44/2.05  
% 5.44/2.05  
% 5.44/2.05  %Foreground operators:
% 5.44/2.05  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.44/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.44/2.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.44/2.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.44/2.05  tff('#skF_2', type, '#skF_2': $i).
% 5.44/2.05  tff('#skF_3', type, '#skF_3': $i).
% 5.44/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.44/2.05  tff('#skF_4', type, '#skF_4': $i).
% 5.44/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.44/2.05  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.44/2.05  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.44/2.05  
% 5.44/2.07  tff(f_50, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.44/2.07  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.44/2.07  tff(f_60, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_xboole_1)).
% 5.44/2.07  tff(f_56, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.44/2.07  tff(f_48, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & (![D]: ((r1_tarski(D, B) & r1_tarski(D, C)) => r1_tarski(D, A)))) => (A = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_xboole_1)).
% 5.44/2.07  tff(f_54, axiom, (![A, B, C]: (r1_tarski(A, B) => (k2_xboole_0(A, k3_xboole_0(C, B)) = k3_xboole_0(k2_xboole_0(A, C), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_xboole_1)).
% 5.44/2.07  tff(f_35, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_xboole_1)).
% 5.44/2.07  tff(f_63, negated_conjecture, ~(![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 5.44/2.07  tff(c_12, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.44/2.07  tff(c_23, plain, (![A_23, B_24]: (k2_xboole_0(A_23, B_24)=B_24 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.44/2.07  tff(c_31, plain, (![A_11]: (k2_xboole_0(k1_xboole_0, A_11)=A_11)), inference(resolution, [status(thm)], [c_12, c_23])).
% 5.44/2.07  tff(c_80, plain, (![A_28, C_29, B_30]: (r1_tarski(k2_xboole_0(A_28, C_29), k2_xboole_0(B_30, C_29)) | ~r1_tarski(A_28, B_30))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.44/2.07  tff(c_92, plain, (![A_11, B_30]: (r1_tarski(A_11, k2_xboole_0(B_30, A_11)) | ~r1_tarski(k1_xboole_0, B_30))), inference(superposition, [status(thm), theory('equality')], [c_31, c_80])).
% 5.44/2.07  tff(c_99, plain, (![A_31, B_32]: (r1_tarski(A_31, k2_xboole_0(B_32, A_31)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_92])).
% 5.44/2.07  tff(c_108, plain, (![A_11]: (r1_tarski(A_11, A_11))), inference(superposition, [status(thm), theory('equality')], [c_31, c_99])).
% 5.44/2.07  tff(c_16, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.44/2.07  tff(c_8, plain, (![A_7, B_8, C_9]: (r1_tarski('#skF_1'(A_7, B_8, C_9), C_9) | k3_xboole_0(B_8, C_9)=A_7 | ~r1_tarski(A_7, C_9) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.44/2.07  tff(c_5625, plain, (![A_173, B_174, C_175]: (~r1_tarski('#skF_1'(A_173, B_174, C_175), A_173) | k3_xboole_0(B_174, C_175)=A_173 | ~r1_tarski(A_173, C_175) | ~r1_tarski(A_173, B_174))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.44/2.07  tff(c_5629, plain, (![B_8, C_9]: (k3_xboole_0(B_8, C_9)=C_9 | ~r1_tarski(C_9, C_9) | ~r1_tarski(C_9, B_8))), inference(resolution, [status(thm)], [c_8, c_5625])).
% 5.44/2.07  tff(c_5645, plain, (![B_176, C_177]: (k3_xboole_0(B_176, C_177)=C_177 | ~r1_tarski(C_177, B_176))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_5629])).
% 5.44/2.07  tff(c_5802, plain, (![A_180, B_181]: (k3_xboole_0(k2_xboole_0(A_180, B_181), A_180)=A_180)), inference(resolution, [status(thm)], [c_16, c_5645])).
% 5.44/2.07  tff(c_14, plain, (![A_12, C_14, B_13]: (k3_xboole_0(k2_xboole_0(A_12, C_14), B_13)=k2_xboole_0(A_12, k3_xboole_0(C_14, B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.44/2.07  tff(c_5818, plain, (![A_180, B_181]: (k2_xboole_0(A_180, k3_xboole_0(B_181, A_180))=A_180 | ~r1_tarski(A_180, A_180))), inference(superposition, [status(thm), theory('equality')], [c_5802, c_14])).
% 5.44/2.07  tff(c_5986, plain, (![A_184, B_185]: (k2_xboole_0(A_184, k3_xboole_0(B_185, A_184))=A_184)), inference(demodulation, [status(thm), theory('equality')], [c_108, c_5818])).
% 5.44/2.07  tff(c_98, plain, (![A_11, B_30]: (r1_tarski(A_11, k2_xboole_0(B_30, A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_92])).
% 5.44/2.07  tff(c_6085, plain, (![B_185, A_184]: (r1_tarski(k3_xboole_0(B_185, A_184), A_184))), inference(superposition, [status(thm), theory('equality')], [c_5986, c_98])).
% 5.44/2.07  tff(c_2159, plain, (![A_99, B_100, C_101]: (~r1_tarski('#skF_1'(A_99, B_100, C_101), A_99) | k3_xboole_0(B_100, C_101)=A_99 | ~r1_tarski(A_99, C_101) | ~r1_tarski(A_99, B_100))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.44/2.07  tff(c_2167, plain, (![B_8, C_9]: (k3_xboole_0(B_8, C_9)=C_9 | ~r1_tarski(C_9, C_9) | ~r1_tarski(C_9, B_8))), inference(resolution, [status(thm)], [c_8, c_2159])).
% 5.44/2.07  tff(c_2808, plain, (![B_114, C_115]: (k3_xboole_0(B_114, C_115)=C_115 | ~r1_tarski(C_115, B_114))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_2167])).
% 5.44/2.07  tff(c_3012, plain, (![A_119, B_120]: (k3_xboole_0(k2_xboole_0(A_119, B_120), A_119)=A_119)), inference(resolution, [status(thm)], [c_16, c_2808])).
% 5.44/2.07  tff(c_3032, plain, (![A_119, B_120]: (k2_xboole_0(A_119, k3_xboole_0(B_120, A_119))=A_119 | ~r1_tarski(A_119, A_119))), inference(superposition, [status(thm), theory('equality')], [c_3012, c_14])).
% 5.44/2.07  tff(c_3105, plain, (![A_121, B_122]: (k2_xboole_0(A_121, k3_xboole_0(B_122, A_121))=A_121)), inference(demodulation, [status(thm), theory('equality')], [c_108, c_3032])).
% 5.44/2.07  tff(c_3209, plain, (![B_122, A_121]: (r1_tarski(k3_xboole_0(B_122, A_121), A_121))), inference(superposition, [status(thm), theory('equality')], [c_3105, c_98])).
% 5.44/2.07  tff(c_333, plain, (![A_43, C_44, B_45, D_46]: (r1_tarski(k2_xboole_0(A_43, C_44), k2_xboole_0(B_45, D_46)) | ~r1_tarski(C_44, D_46) | ~r1_tarski(A_43, B_45))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.44/2.07  tff(c_20, plain, (~r1_tarski(k2_xboole_0(k3_xboole_0('#skF_2', '#skF_3'), k3_xboole_0('#skF_2', '#skF_4')), k2_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.44/2.07  tff(c_370, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_4'), '#skF_4') | ~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_333, c_20])).
% 5.44/2.07  tff(c_490, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_370])).
% 5.44/2.07  tff(c_3521, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3209, c_490])).
% 5.44/2.07  tff(c_3522, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_370])).
% 5.44/2.07  tff(c_6170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6085, c_3522])).
% 5.44/2.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.44/2.07  
% 5.44/2.07  Inference rules
% 5.44/2.07  ----------------------
% 5.44/2.07  #Ref     : 0
% 5.44/2.07  #Sup     : 1524
% 5.44/2.07  #Fact    : 0
% 5.44/2.07  #Define  : 0
% 5.44/2.07  #Split   : 6
% 5.44/2.07  #Chain   : 0
% 5.44/2.07  #Close   : 0
% 5.44/2.07  
% 5.44/2.07  Ordering : KBO
% 5.44/2.07  
% 5.44/2.07  Simplification rules
% 5.44/2.07  ----------------------
% 5.44/2.07  #Subsume      : 266
% 5.44/2.07  #Demod        : 854
% 5.44/2.07  #Tautology    : 821
% 5.44/2.07  #SimpNegUnit  : 0
% 5.44/2.07  #BackRed      : 2
% 5.44/2.07  
% 5.44/2.07  #Partial instantiations: 0
% 5.44/2.07  #Strategies tried      : 1
% 5.44/2.07  
% 5.44/2.07  Timing (in seconds)
% 5.44/2.07  ----------------------
% 5.44/2.07  Preprocessing        : 0.30
% 5.44/2.07  Parsing              : 0.16
% 5.44/2.07  CNF conversion       : 0.02
% 5.44/2.07  Main loop            : 1.01
% 5.44/2.07  Inferencing          : 0.35
% 5.44/2.07  Reduction            : 0.34
% 5.44/2.07  Demodulation         : 0.26
% 5.44/2.07  BG Simplification    : 0.04
% 5.44/2.07  Subsumption          : 0.21
% 5.44/2.07  Abstraction          : 0.06
% 5.44/2.07  MUC search           : 0.00
% 5.44/2.07  Cooper               : 0.00
% 5.44/2.07  Total                : 1.33
% 5.44/2.07  Index Insertion      : 0.00
% 5.44/2.07  Index Deletion       : 0.00
% 5.44/2.07  Index Matching       : 0.00
% 5.44/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
