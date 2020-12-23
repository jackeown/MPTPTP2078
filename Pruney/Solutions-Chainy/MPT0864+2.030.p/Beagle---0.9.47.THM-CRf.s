%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:12 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   55 (  98 expanded)
%              Number of leaves         :   22 (  44 expanded)
%              Depth                    :    6
%              Number of atoms          :   64 ( 144 expanded)
%              Number of equality atoms :   51 ( 118 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k2_xboole_0 > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_67,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_45,plain,(
    ! [A_26,B_27] : k2_xboole_0(k1_tarski(A_26),B_27) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_49,plain,(
    ! [A_26] : k1_tarski(A_26) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_45])).

tff(c_190,plain,(
    ! [A_47] :
      ( r2_hidden('#skF_3'(A_47),A_47)
      | k1_xboole_0 = A_47 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [C_7,A_3] :
      ( C_7 = A_3
      | ~ r2_hidden(C_7,k1_tarski(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_194,plain,(
    ! [A_3] :
      ( '#skF_3'(k1_tarski(A_3)) = A_3
      | k1_tarski(A_3) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_190,c_4])).

tff(c_197,plain,(
    ! [A_3] : '#skF_3'(k1_tarski(A_3)) = A_3 ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_194])).

tff(c_6,plain,(
    ! [C_7] : r2_hidden(C_7,k1_tarski(C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_212,plain,(
    ! [D_49,A_50,C_51] :
      ( ~ r2_hidden(D_49,A_50)
      | k4_tarski(C_51,D_49) != '#skF_3'(A_50)
      | k1_xboole_0 = A_50 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_216,plain,(
    ! [C_51,C_7] :
      ( k4_tarski(C_51,C_7) != '#skF_3'(k1_tarski(C_7))
      | k1_tarski(C_7) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_212])).

tff(c_219,plain,(
    ! [C_51,C_7] :
      ( k4_tarski(C_51,C_7) != C_7
      | k1_tarski(C_7) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_216])).

tff(c_220,plain,(
    ! [C_51,C_7] : k4_tarski(C_51,C_7) != C_7 ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_219])).

tff(c_22,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_3'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_108,plain,(
    ! [C_34,A_35] :
      ( C_34 = A_35
      | ~ r2_hidden(C_34,k1_tarski(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_112,plain,(
    ! [A_35] :
      ( '#skF_3'(k1_tarski(A_35)) = A_35
      | k1_tarski(A_35) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_108])).

tff(c_118,plain,(
    ! [A_35] : '#skF_3'(k1_tarski(A_35)) = A_35 ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_112])).

tff(c_149,plain,(
    ! [C_42,A_43,D_44] :
      ( ~ r2_hidden(C_42,A_43)
      | k4_tarski(C_42,D_44) != '#skF_3'(A_43)
      | k1_xboole_0 = A_43 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_153,plain,(
    ! [C_7,D_44] :
      ( k4_tarski(C_7,D_44) != '#skF_3'(k1_tarski(C_7))
      | k1_tarski(C_7) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_149])).

tff(c_156,plain,(
    ! [C_7,D_44] :
      ( k4_tarski(C_7,D_44) != C_7
      | k1_tarski(C_7) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_153])).

tff(c_157,plain,(
    ! [C_7,D_44] : k4_tarski(C_7,D_44) != C_7 ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_156])).

tff(c_30,plain,(
    k4_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_67,plain,(
    ! [A_31,B_32] : k1_mcart_1(k4_tarski(A_31,B_32)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_76,plain,(
    k1_mcart_1('#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_67])).

tff(c_51,plain,(
    ! [A_29,B_30] : k2_mcart_1(k4_tarski(A_29,B_30)) = B_30 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_60,plain,(
    k2_mcart_1('#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_51])).

tff(c_28,plain,
    ( k2_mcart_1('#skF_4') = '#skF_4'
    | k1_mcart_1('#skF_4') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_83,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_60,c_28])).

tff(c_84,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_86,plain,(
    k4_tarski('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_30])).

tff(c_159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_157,c_86])).

tff(c_160,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_163,plain,(
    k4_tarski('#skF_5','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_30])).

tff(c_231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_220,c_163])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 21:04:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.54  
% 2.34/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.55  %$ r2_hidden > k4_tarski > k2_xboole_0 > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.34/1.55  
% 2.34/1.55  %Foreground sorts:
% 2.34/1.55  
% 2.34/1.55  
% 2.34/1.55  %Background operators:
% 2.34/1.55  
% 2.34/1.55  
% 2.34/1.55  %Foreground operators:
% 2.34/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.34/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.34/1.55  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.34/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.34/1.55  tff('#skF_5', type, '#skF_5': $i).
% 2.34/1.55  tff('#skF_6', type, '#skF_6': $i).
% 2.34/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.55  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.34/1.55  tff('#skF_4', type, '#skF_4': $i).
% 2.34/1.55  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.34/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.55  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.34/1.55  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.34/1.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.34/1.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.34/1.55  
% 2.34/1.57  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.34/1.57  tff(f_37, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.34/1.57  tff(f_57, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.34/1.57  tff(f_34, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.34/1.57  tff(f_67, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.34/1.57  tff(f_41, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.34/1.57  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.34/1.57  tff(c_45, plain, (![A_26, B_27]: (k2_xboole_0(k1_tarski(A_26), B_27)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.34/1.57  tff(c_49, plain, (![A_26]: (k1_tarski(A_26)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_45])).
% 2.34/1.57  tff(c_190, plain, (![A_47]: (r2_hidden('#skF_3'(A_47), A_47) | k1_xboole_0=A_47)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.34/1.57  tff(c_4, plain, (![C_7, A_3]: (C_7=A_3 | ~r2_hidden(C_7, k1_tarski(A_3)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.34/1.57  tff(c_194, plain, (![A_3]: ('#skF_3'(k1_tarski(A_3))=A_3 | k1_tarski(A_3)=k1_xboole_0)), inference(resolution, [status(thm)], [c_190, c_4])).
% 2.34/1.57  tff(c_197, plain, (![A_3]: ('#skF_3'(k1_tarski(A_3))=A_3)), inference(negUnitSimplification, [status(thm)], [c_49, c_194])).
% 2.34/1.57  tff(c_6, plain, (![C_7]: (r2_hidden(C_7, k1_tarski(C_7)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.34/1.57  tff(c_212, plain, (![D_49, A_50, C_51]: (~r2_hidden(D_49, A_50) | k4_tarski(C_51, D_49)!='#skF_3'(A_50) | k1_xboole_0=A_50)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.34/1.57  tff(c_216, plain, (![C_51, C_7]: (k4_tarski(C_51, C_7)!='#skF_3'(k1_tarski(C_7)) | k1_tarski(C_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_212])).
% 2.34/1.57  tff(c_219, plain, (![C_51, C_7]: (k4_tarski(C_51, C_7)!=C_7 | k1_tarski(C_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_197, c_216])).
% 2.34/1.57  tff(c_220, plain, (![C_51, C_7]: (k4_tarski(C_51, C_7)!=C_7)), inference(negUnitSimplification, [status(thm)], [c_49, c_219])).
% 2.34/1.57  tff(c_22, plain, (![A_12]: (r2_hidden('#skF_3'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.34/1.57  tff(c_108, plain, (![C_34, A_35]: (C_34=A_35 | ~r2_hidden(C_34, k1_tarski(A_35)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.34/1.57  tff(c_112, plain, (![A_35]: ('#skF_3'(k1_tarski(A_35))=A_35 | k1_tarski(A_35)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_108])).
% 2.34/1.57  tff(c_118, plain, (![A_35]: ('#skF_3'(k1_tarski(A_35))=A_35)), inference(negUnitSimplification, [status(thm)], [c_49, c_112])).
% 2.34/1.57  tff(c_149, plain, (![C_42, A_43, D_44]: (~r2_hidden(C_42, A_43) | k4_tarski(C_42, D_44)!='#skF_3'(A_43) | k1_xboole_0=A_43)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.34/1.57  tff(c_153, plain, (![C_7, D_44]: (k4_tarski(C_7, D_44)!='#skF_3'(k1_tarski(C_7)) | k1_tarski(C_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_149])).
% 2.34/1.57  tff(c_156, plain, (![C_7, D_44]: (k4_tarski(C_7, D_44)!=C_7 | k1_tarski(C_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_118, c_153])).
% 2.34/1.57  tff(c_157, plain, (![C_7, D_44]: (k4_tarski(C_7, D_44)!=C_7)), inference(negUnitSimplification, [status(thm)], [c_49, c_156])).
% 2.34/1.57  tff(c_30, plain, (k4_tarski('#skF_5', '#skF_6')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.34/1.57  tff(c_67, plain, (![A_31, B_32]: (k1_mcart_1(k4_tarski(A_31, B_32))=A_31)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.34/1.57  tff(c_76, plain, (k1_mcart_1('#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_30, c_67])).
% 2.34/1.57  tff(c_51, plain, (![A_29, B_30]: (k2_mcart_1(k4_tarski(A_29, B_30))=B_30)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.34/1.57  tff(c_60, plain, (k2_mcart_1('#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_30, c_51])).
% 2.34/1.57  tff(c_28, plain, (k2_mcart_1('#skF_4')='#skF_4' | k1_mcart_1('#skF_4')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.34/1.57  tff(c_83, plain, ('#skF_6'='#skF_4' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_60, c_28])).
% 2.34/1.57  tff(c_84, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_83])).
% 2.34/1.57  tff(c_86, plain, (k4_tarski('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_30])).
% 2.34/1.57  tff(c_159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_157, c_86])).
% 2.34/1.57  tff(c_160, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_83])).
% 2.34/1.57  tff(c_163, plain, (k4_tarski('#skF_5', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_160, c_30])).
% 2.34/1.57  tff(c_231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_220, c_163])).
% 2.34/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.57  
% 2.34/1.57  Inference rules
% 2.34/1.57  ----------------------
% 2.34/1.57  #Ref     : 0
% 2.34/1.57  #Sup     : 50
% 2.34/1.57  #Fact    : 0
% 2.34/1.57  #Define  : 0
% 2.34/1.57  #Split   : 1
% 2.34/1.57  #Chain   : 0
% 2.34/1.57  #Close   : 0
% 2.34/1.57  
% 2.34/1.57  Ordering : KBO
% 2.34/1.57  
% 2.34/1.57  Simplification rules
% 2.34/1.57  ----------------------
% 2.34/1.57  #Subsume      : 0
% 2.34/1.57  #Demod        : 16
% 2.34/1.57  #Tautology    : 36
% 2.34/1.57  #SimpNegUnit  : 10
% 2.34/1.57  #BackRed      : 6
% 2.34/1.57  
% 2.34/1.57  #Partial instantiations: 0
% 2.34/1.57  #Strategies tried      : 1
% 2.34/1.57  
% 2.34/1.57  Timing (in seconds)
% 2.34/1.57  ----------------------
% 2.34/1.57  Preprocessing        : 0.45
% 2.34/1.57  Parsing              : 0.24
% 2.34/1.57  CNF conversion       : 0.04
% 2.34/1.57  Main loop            : 0.26
% 2.34/1.57  Inferencing          : 0.09
% 2.34/1.57  Reduction            : 0.09
% 2.34/1.57  Demodulation         : 0.06
% 2.34/1.57  BG Simplification    : 0.02
% 2.34/1.57  Subsumption          : 0.04
% 2.34/1.57  Abstraction          : 0.01
% 2.34/1.57  MUC search           : 0.00
% 2.34/1.57  Cooper               : 0.00
% 2.34/1.57  Total                : 0.76
% 2.34/1.57  Index Insertion      : 0.00
% 2.34/1.57  Index Deletion       : 0.00
% 2.34/1.57  Index Matching       : 0.00
% 2.34/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
