%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:56 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   46 (  65 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :    6
%              Number of atoms          :   58 ( 104 expanded)
%              Number of equality atoms :   23 (  44 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_mcart_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(B,C))
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_mcart_1)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ~ ( r1_tarski(A,k2_zfmisc_1(B,C))
        & r2_hidden(D,A)
        & ! [E,F] :
            ~ ( r2_hidden(E,B)
              & r2_hidden(F,C)
              & D = k4_tarski(E,F) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    ! [A_24,B_25] : r1_tarski(A_24,k2_xboole_0(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_34])).

tff(c_24,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_39,plain,(
    k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_12,plain,(
    ! [A_12,B_13,C_14,D_15] :
      ( k4_tarski('#skF_1'(A_12,B_13,C_14,D_15),'#skF_2'(A_12,B_13,C_14,D_15)) = D_15
      | ~ r2_hidden(D_15,A_12)
      | ~ r1_tarski(A_12,k2_zfmisc_1(B_13,C_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_75,plain,(
    ! [A_46,B_47,C_48,D_49] :
      ( k4_tarski('#skF_1'(A_46,B_47,C_48,D_49),'#skF_2'(A_46,B_47,C_48,D_49)) = D_49
      | ~ r2_hidden(D_49,A_46)
      | ~ r1_tarski(A_46,k2_zfmisc_1(B_47,C_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_20,plain,(
    ! [B_21,C_22] : k1_mcart_1(k4_tarski(B_21,C_22)) != k4_tarski(B_21,C_22) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_94,plain,(
    ! [A_54,B_55,C_56,D_57] :
      ( k4_tarski('#skF_1'(A_54,B_55,C_56,D_57),'#skF_2'(A_54,B_55,C_56,D_57)) != k1_mcart_1(D_57)
      | ~ r2_hidden(D_57,A_54)
      | ~ r1_tarski(A_54,k2_zfmisc_1(B_55,C_56)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_20])).

tff(c_111,plain,(
    ! [D_62,A_63,B_64,C_65] :
      ( k1_mcart_1(D_62) != D_62
      | ~ r2_hidden(D_62,A_63)
      | ~ r1_tarski(A_63,k2_zfmisc_1(B_64,C_65))
      | ~ r2_hidden(D_62,A_63)
      | ~ r1_tarski(A_63,k2_zfmisc_1(B_64,C_65)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_94])).

tff(c_117,plain,(
    ! [B_64,C_65] :
      ( k1_mcart_1('#skF_3') != '#skF_3'
      | ~ r2_hidden('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1(B_64,C_65)) ) ),
    inference(resolution,[status(thm)],[c_24,c_111])).

tff(c_123,plain,(
    ! [B_66,C_67] : ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1(B_66,C_67)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_39,c_117])).

tff(c_128,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_37,c_123])).

tff(c_129,plain,(
    k2_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_166,plain,(
    ! [A_87,B_88,C_89,D_90] :
      ( k4_tarski('#skF_1'(A_87,B_88,C_89,D_90),'#skF_2'(A_87,B_88,C_89,D_90)) = D_90
      | ~ r2_hidden(D_90,A_87)
      | ~ r1_tarski(A_87,k2_zfmisc_1(B_88,C_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_18,plain,(
    ! [B_21,C_22] : k2_mcart_1(k4_tarski(B_21,C_22)) != k4_tarski(B_21,C_22) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_197,plain,(
    ! [A_99,B_100,C_101,D_102] :
      ( k4_tarski('#skF_1'(A_99,B_100,C_101,D_102),'#skF_2'(A_99,B_100,C_101,D_102)) != k2_mcart_1(D_102)
      | ~ r2_hidden(D_102,A_99)
      | ~ r1_tarski(A_99,k2_zfmisc_1(B_100,C_101)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_18])).

tff(c_201,plain,(
    ! [D_103,A_104,B_105,C_106] :
      ( k2_mcart_1(D_103) != D_103
      | ~ r2_hidden(D_103,A_104)
      | ~ r1_tarski(A_104,k2_zfmisc_1(B_105,C_106))
      | ~ r2_hidden(D_103,A_104)
      | ~ r1_tarski(A_104,k2_zfmisc_1(B_105,C_106)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_197])).

tff(c_207,plain,(
    ! [B_105,C_106] :
      ( k2_mcart_1('#skF_3') != '#skF_3'
      | ~ r2_hidden('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1(B_105,C_106)) ) ),
    inference(resolution,[status(thm)],[c_24,c_201])).

tff(c_213,plain,(
    ! [B_107,C_108] : ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1(B_107,C_108)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_129,c_207])).

tff(c_218,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_37,c_213])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:45:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.20  
% 1.88/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.21  %$ r2_hidden > r1_tarski > k3_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_mcart_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.88/1.21  
% 1.88/1.21  %Foreground sorts:
% 1.88/1.21  
% 1.88/1.21  
% 1.88/1.21  %Background operators:
% 1.88/1.21  
% 1.88/1.21  
% 1.88/1.21  %Foreground operators:
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.88/1.21  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.88/1.21  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.88/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.88/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.88/1.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 1.88/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.88/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.21  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.88/1.21  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.88/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.88/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.21  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.88/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.88/1.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 1.88/1.21  
% 1.88/1.22  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.88/1.22  tff(f_29, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.88/1.22  tff(f_66, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_mcart_1)).
% 1.88/1.22  tff(f_48, axiom, (![A, B, C, D]: ~((r1_tarski(A, k2_zfmisc_1(B, C)) & r2_hidden(D, A)) & (![E, F]: ~((r2_hidden(E, B) & r2_hidden(F, C)) & (D = k4_tarski(E, F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_zfmisc_1)).
% 1.88/1.22  tff(f_57, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 1.88/1.22  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.88/1.22  tff(c_34, plain, (![A_24, B_25]: (r1_tarski(A_24, k2_xboole_0(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.88/1.22  tff(c_37, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_34])).
% 1.88/1.22  tff(c_24, plain, (r2_hidden('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.88/1.22  tff(c_22, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.88/1.22  tff(c_39, plain, (k1_mcart_1('#skF_3')='#skF_3'), inference(splitLeft, [status(thm)], [c_22])).
% 1.88/1.22  tff(c_12, plain, (![A_12, B_13, C_14, D_15]: (k4_tarski('#skF_1'(A_12, B_13, C_14, D_15), '#skF_2'(A_12, B_13, C_14, D_15))=D_15 | ~r2_hidden(D_15, A_12) | ~r1_tarski(A_12, k2_zfmisc_1(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.88/1.22  tff(c_75, plain, (![A_46, B_47, C_48, D_49]: (k4_tarski('#skF_1'(A_46, B_47, C_48, D_49), '#skF_2'(A_46, B_47, C_48, D_49))=D_49 | ~r2_hidden(D_49, A_46) | ~r1_tarski(A_46, k2_zfmisc_1(B_47, C_48)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.88/1.22  tff(c_20, plain, (![B_21, C_22]: (k1_mcart_1(k4_tarski(B_21, C_22))!=k4_tarski(B_21, C_22))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.88/1.22  tff(c_94, plain, (![A_54, B_55, C_56, D_57]: (k4_tarski('#skF_1'(A_54, B_55, C_56, D_57), '#skF_2'(A_54, B_55, C_56, D_57))!=k1_mcart_1(D_57) | ~r2_hidden(D_57, A_54) | ~r1_tarski(A_54, k2_zfmisc_1(B_55, C_56)))), inference(superposition, [status(thm), theory('equality')], [c_75, c_20])).
% 1.88/1.22  tff(c_111, plain, (![D_62, A_63, B_64, C_65]: (k1_mcart_1(D_62)!=D_62 | ~r2_hidden(D_62, A_63) | ~r1_tarski(A_63, k2_zfmisc_1(B_64, C_65)) | ~r2_hidden(D_62, A_63) | ~r1_tarski(A_63, k2_zfmisc_1(B_64, C_65)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_94])).
% 1.88/1.22  tff(c_117, plain, (![B_64, C_65]: (k1_mcart_1('#skF_3')!='#skF_3' | ~r2_hidden('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5')) | ~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1(B_64, C_65)))), inference(resolution, [status(thm)], [c_24, c_111])).
% 1.88/1.22  tff(c_123, plain, (![B_66, C_67]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1(B_66, C_67)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_39, c_117])).
% 1.88/1.22  tff(c_128, plain, $false, inference(resolution, [status(thm)], [c_37, c_123])).
% 1.88/1.22  tff(c_129, plain, (k2_mcart_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_22])).
% 1.88/1.22  tff(c_166, plain, (![A_87, B_88, C_89, D_90]: (k4_tarski('#skF_1'(A_87, B_88, C_89, D_90), '#skF_2'(A_87, B_88, C_89, D_90))=D_90 | ~r2_hidden(D_90, A_87) | ~r1_tarski(A_87, k2_zfmisc_1(B_88, C_89)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.88/1.22  tff(c_18, plain, (![B_21, C_22]: (k2_mcart_1(k4_tarski(B_21, C_22))!=k4_tarski(B_21, C_22))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.88/1.22  tff(c_197, plain, (![A_99, B_100, C_101, D_102]: (k4_tarski('#skF_1'(A_99, B_100, C_101, D_102), '#skF_2'(A_99, B_100, C_101, D_102))!=k2_mcart_1(D_102) | ~r2_hidden(D_102, A_99) | ~r1_tarski(A_99, k2_zfmisc_1(B_100, C_101)))), inference(superposition, [status(thm), theory('equality')], [c_166, c_18])).
% 1.88/1.22  tff(c_201, plain, (![D_103, A_104, B_105, C_106]: (k2_mcart_1(D_103)!=D_103 | ~r2_hidden(D_103, A_104) | ~r1_tarski(A_104, k2_zfmisc_1(B_105, C_106)) | ~r2_hidden(D_103, A_104) | ~r1_tarski(A_104, k2_zfmisc_1(B_105, C_106)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_197])).
% 1.88/1.22  tff(c_207, plain, (![B_105, C_106]: (k2_mcart_1('#skF_3')!='#skF_3' | ~r2_hidden('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5')) | ~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1(B_105, C_106)))), inference(resolution, [status(thm)], [c_24, c_201])).
% 1.88/1.22  tff(c_213, plain, (![B_107, C_108]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1(B_107, C_108)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_129, c_207])).
% 1.88/1.22  tff(c_218, plain, $false, inference(resolution, [status(thm)], [c_37, c_213])).
% 1.88/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.22  
% 1.88/1.22  Inference rules
% 1.88/1.22  ----------------------
% 1.88/1.22  #Ref     : 0
% 1.88/1.22  #Sup     : 45
% 1.88/1.22  #Fact    : 0
% 1.88/1.22  #Define  : 0
% 1.88/1.22  #Split   : 2
% 1.88/1.22  #Chain   : 0
% 1.88/1.22  #Close   : 0
% 1.88/1.22  
% 1.88/1.22  Ordering : KBO
% 1.88/1.22  
% 1.88/1.22  Simplification rules
% 1.88/1.22  ----------------------
% 1.88/1.22  #Subsume      : 1
% 1.88/1.22  #Demod        : 6
% 1.88/1.22  #Tautology    : 22
% 1.88/1.22  #SimpNegUnit  : 0
% 1.88/1.22  #BackRed      : 0
% 1.88/1.22  
% 1.88/1.22  #Partial instantiations: 0
% 1.88/1.22  #Strategies tried      : 1
% 1.88/1.22  
% 1.88/1.22  Timing (in seconds)
% 1.88/1.22  ----------------------
% 1.88/1.22  Preprocessing        : 0.28
% 1.88/1.22  Parsing              : 0.14
% 1.88/1.22  CNF conversion       : 0.02
% 1.88/1.22  Main loop            : 0.17
% 1.88/1.22  Inferencing          : 0.07
% 1.88/1.22  Reduction            : 0.05
% 1.88/1.22  Demodulation         : 0.03
% 1.88/1.22  BG Simplification    : 0.01
% 1.88/1.22  Subsumption          : 0.03
% 1.88/1.22  Abstraction          : 0.01
% 1.88/1.22  MUC search           : 0.00
% 1.88/1.22  Cooper               : 0.00
% 1.88/1.22  Total                : 0.48
% 1.88/1.22  Index Insertion      : 0.00
% 1.88/1.22  Index Deletion       : 0.00
% 1.88/1.22  Index Matching       : 0.00
% 1.88/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
