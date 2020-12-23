%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:54 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 153 expanded)
%              Number of leaves         :   20 (  55 expanded)
%              Depth                    :    8
%              Number of atoms          :   91 ( 269 expanded)
%              Number of equality atoms :    4 (  14 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),C)
      <=> ( r2_hidden(A,C)
          & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_22,plain,
    ( r2_hidden('#skF_1','#skF_3')
    | ~ r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_83,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_26,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_68,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_8,plain,(
    ! [A_9,B_10] : k2_xboole_0(k1_tarski(A_9),k1_tarski(B_10)) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_78,plain,(
    ! [A_23,C_24,B_25] :
      ( r1_tarski(A_23,C_24)
      | ~ r1_tarski(k2_xboole_0(A_23,B_25),C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_85,plain,(
    ! [A_26,C_27,B_28] :
      ( r1_tarski(k1_tarski(A_26),C_27)
      | ~ r1_tarski(k2_tarski(A_26,B_28),C_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_78])).

tff(c_95,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_85])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | ~ r1_tarski(k1_tarski(A_13),B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_98,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_95,c_14])).

tff(c_102,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_98])).

tff(c_104,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_103,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_105,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_6,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_108,plain,(
    ! [A_29,C_30,B_31] :
      ( r1_tarski(k1_tarski(A_29),C_30)
      | ~ r1_tarski(k2_tarski(A_29,B_31),C_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_78])).

tff(c_125,plain,(
    ! [A_32,C_33,B_34] :
      ( r1_tarski(k1_tarski(A_32),C_33)
      | ~ r1_tarski(k2_tarski(B_34,A_32),C_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_108])).

tff(c_135,plain,(
    r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_125])).

tff(c_138,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_135,c_14])).

tff(c_142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_138])).

tff(c_144,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_20,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | ~ r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_146,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_144,c_20])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(k1_tarski(A_13),B_14)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_143,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_180,plain,(
    ! [A_41,C_42,B_43] :
      ( r1_tarski(k2_xboole_0(A_41,C_42),B_43)
      | ~ r1_tarski(C_42,B_43)
      | ~ r1_tarski(A_41,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_190,plain,(
    ! [A_44,B_45,B_46] :
      ( r1_tarski(k2_tarski(A_44,B_45),B_46)
      | ~ r1_tarski(k1_tarski(B_45),B_46)
      | ~ r1_tarski(k1_tarski(A_44),B_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_180])).

tff(c_18,plain,
    ( ~ r1_tarski(k2_tarski('#skF_1','#skF_2'),'#skF_3')
    | ~ r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_189,plain,(
    ~ r1_tarski(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_144,c_18])).

tff(c_206,plain,
    ( ~ r1_tarski(k1_tarski('#skF_2'),'#skF_3')
    | ~ r1_tarski(k1_tarski('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_190,c_189])).

tff(c_209,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_206])).

tff(c_212,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_209])).

tff(c_216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_212])).

tff(c_217,plain,(
    ~ r1_tarski(k1_tarski('#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_221,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_217])).

tff(c_225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_221])).

tff(c_226,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_227,plain,(
    ~ r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_28,plain,
    ( r2_hidden('#skF_1','#skF_3')
    | r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_228,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_227,c_228])).

tff(c_230,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_262,plain,(
    ! [A_58,C_59,B_60] :
      ( r1_tarski(k2_xboole_0(A_58,C_59),B_60)
      | ~ r1_tarski(C_59,B_60)
      | ~ r1_tarski(A_58,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_270,plain,(
    ! [A_61,B_62,B_63] :
      ( r1_tarski(k2_tarski(A_61,B_62),B_63)
      | ~ r1_tarski(k1_tarski(B_62),B_63)
      | ~ r1_tarski(k1_tarski(A_61),B_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_262])).

tff(c_24,plain,
    ( ~ r1_tarski(k2_tarski('#skF_1','#skF_2'),'#skF_3')
    | r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_247,plain,(
    ~ r1_tarski(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_227,c_24])).

tff(c_291,plain,
    ( ~ r1_tarski(k1_tarski('#skF_2'),'#skF_3')
    | ~ r1_tarski(k1_tarski('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_270,c_247])).

tff(c_293,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_291])).

tff(c_296,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_293])).

tff(c_300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_296])).

tff(c_301,plain,(
    ~ r1_tarski(k1_tarski('#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_291])).

tff(c_305,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_301])).

tff(c_309,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_305])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:59:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.19  
% 1.93/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.20  %$ r2_hidden > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.93/1.20  
% 1.93/1.20  %Foreground sorts:
% 1.93/1.20  
% 1.93/1.20  
% 1.93/1.20  %Background operators:
% 1.93/1.20  
% 1.93/1.20  
% 1.93/1.20  %Foreground operators:
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.93/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.20  tff('#skF_5', type, '#skF_5': $i).
% 1.93/1.20  tff('#skF_6', type, '#skF_6': $i).
% 1.93/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.93/1.20  
% 2.00/1.21  tff(f_54, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.00/1.21  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.00/1.21  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.00/1.21  tff(f_47, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 2.00/1.21  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.00/1.21  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 2.00/1.21  tff(c_22, plain, (r2_hidden('#skF_1', '#skF_3') | ~r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.00/1.21  tff(c_83, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_22])).
% 2.00/1.21  tff(c_26, plain, (r2_hidden('#skF_2', '#skF_3') | r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.00/1.21  tff(c_68, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_26])).
% 2.00/1.21  tff(c_8, plain, (![A_9, B_10]: (k2_xboole_0(k1_tarski(A_9), k1_tarski(B_10))=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.00/1.21  tff(c_78, plain, (![A_23, C_24, B_25]: (r1_tarski(A_23, C_24) | ~r1_tarski(k2_xboole_0(A_23, B_25), C_24))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.00/1.21  tff(c_85, plain, (![A_26, C_27, B_28]: (r1_tarski(k1_tarski(A_26), C_27) | ~r1_tarski(k2_tarski(A_26, B_28), C_27))), inference(superposition, [status(thm), theory('equality')], [c_8, c_78])).
% 2.00/1.21  tff(c_95, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_6')), inference(resolution, [status(thm)], [c_68, c_85])).
% 2.00/1.21  tff(c_14, plain, (![A_13, B_14]: (r2_hidden(A_13, B_14) | ~r1_tarski(k1_tarski(A_13), B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.00/1.21  tff(c_98, plain, (r2_hidden('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_95, c_14])).
% 2.00/1.21  tff(c_102, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_98])).
% 2.00/1.21  tff(c_104, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_22])).
% 2.00/1.21  tff(c_103, plain, (~r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_22])).
% 2.00/1.21  tff(c_105, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_103])).
% 2.00/1.21  tff(c_6, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.00/1.21  tff(c_108, plain, (![A_29, C_30, B_31]: (r1_tarski(k1_tarski(A_29), C_30) | ~r1_tarski(k2_tarski(A_29, B_31), C_30))), inference(superposition, [status(thm), theory('equality')], [c_8, c_78])).
% 2.00/1.21  tff(c_125, plain, (![A_32, C_33, B_34]: (r1_tarski(k1_tarski(A_32), C_33) | ~r1_tarski(k2_tarski(B_34, A_32), C_33))), inference(superposition, [status(thm), theory('equality')], [c_6, c_108])).
% 2.00/1.21  tff(c_135, plain, (r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_68, c_125])).
% 2.00/1.21  tff(c_138, plain, (r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_135, c_14])).
% 2.00/1.21  tff(c_142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105, c_138])).
% 2.00/1.21  tff(c_144, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_103])).
% 2.00/1.21  tff(c_20, plain, (r2_hidden('#skF_2', '#skF_3') | ~r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.00/1.21  tff(c_146, plain, (r2_hidden('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_144, c_20])).
% 2.00/1.21  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(k1_tarski(A_13), B_14) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.00/1.21  tff(c_143, plain, (r2_hidden('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_103])).
% 2.00/1.21  tff(c_180, plain, (![A_41, C_42, B_43]: (r1_tarski(k2_xboole_0(A_41, C_42), B_43) | ~r1_tarski(C_42, B_43) | ~r1_tarski(A_41, B_43))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.00/1.21  tff(c_190, plain, (![A_44, B_45, B_46]: (r1_tarski(k2_tarski(A_44, B_45), B_46) | ~r1_tarski(k1_tarski(B_45), B_46) | ~r1_tarski(k1_tarski(A_44), B_46))), inference(superposition, [status(thm), theory('equality')], [c_8, c_180])).
% 2.00/1.21  tff(c_18, plain, (~r1_tarski(k2_tarski('#skF_1', '#skF_2'), '#skF_3') | ~r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.00/1.21  tff(c_189, plain, (~r1_tarski(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_144, c_18])).
% 2.00/1.21  tff(c_206, plain, (~r1_tarski(k1_tarski('#skF_2'), '#skF_3') | ~r1_tarski(k1_tarski('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_190, c_189])).
% 2.00/1.21  tff(c_209, plain, (~r1_tarski(k1_tarski('#skF_1'), '#skF_3')), inference(splitLeft, [status(thm)], [c_206])).
% 2.00/1.21  tff(c_212, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_16, c_209])).
% 2.00/1.21  tff(c_216, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_143, c_212])).
% 2.00/1.21  tff(c_217, plain, (~r1_tarski(k1_tarski('#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_206])).
% 2.00/1.21  tff(c_221, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_16, c_217])).
% 2.00/1.21  tff(c_225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_146, c_221])).
% 2.00/1.21  tff(c_226, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_26])).
% 2.00/1.21  tff(c_227, plain, (~r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_26])).
% 2.00/1.21  tff(c_28, plain, (r2_hidden('#skF_1', '#skF_3') | r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.00/1.21  tff(c_228, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_28])).
% 2.00/1.21  tff(c_229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_227, c_228])).
% 2.00/1.21  tff(c_230, plain, (r2_hidden('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_28])).
% 2.00/1.21  tff(c_262, plain, (![A_58, C_59, B_60]: (r1_tarski(k2_xboole_0(A_58, C_59), B_60) | ~r1_tarski(C_59, B_60) | ~r1_tarski(A_58, B_60))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.00/1.21  tff(c_270, plain, (![A_61, B_62, B_63]: (r1_tarski(k2_tarski(A_61, B_62), B_63) | ~r1_tarski(k1_tarski(B_62), B_63) | ~r1_tarski(k1_tarski(A_61), B_63))), inference(superposition, [status(thm), theory('equality')], [c_8, c_262])).
% 2.00/1.21  tff(c_24, plain, (~r1_tarski(k2_tarski('#skF_1', '#skF_2'), '#skF_3') | r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.00/1.21  tff(c_247, plain, (~r1_tarski(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_227, c_24])).
% 2.00/1.21  tff(c_291, plain, (~r1_tarski(k1_tarski('#skF_2'), '#skF_3') | ~r1_tarski(k1_tarski('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_270, c_247])).
% 2.00/1.21  tff(c_293, plain, (~r1_tarski(k1_tarski('#skF_1'), '#skF_3')), inference(splitLeft, [status(thm)], [c_291])).
% 2.00/1.21  tff(c_296, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_16, c_293])).
% 2.00/1.21  tff(c_300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_230, c_296])).
% 2.00/1.21  tff(c_301, plain, (~r1_tarski(k1_tarski('#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_291])).
% 2.00/1.21  tff(c_305, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_16, c_301])).
% 2.00/1.21  tff(c_309, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_226, c_305])).
% 2.00/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.21  
% 2.00/1.21  Inference rules
% 2.00/1.21  ----------------------
% 2.00/1.21  #Ref     : 0
% 2.00/1.21  #Sup     : 58
% 2.00/1.21  #Fact    : 0
% 2.00/1.21  #Define  : 0
% 2.00/1.21  #Split   : 7
% 2.00/1.21  #Chain   : 0
% 2.00/1.21  #Close   : 0
% 2.00/1.21  
% 2.00/1.21  Ordering : KBO
% 2.00/1.21  
% 2.00/1.21  Simplification rules
% 2.00/1.21  ----------------------
% 2.00/1.21  #Subsume      : 18
% 2.00/1.21  #Demod        : 17
% 2.00/1.21  #Tautology    : 27
% 2.00/1.21  #SimpNegUnit  : 4
% 2.00/1.21  #BackRed      : 0
% 2.00/1.21  
% 2.00/1.21  #Partial instantiations: 0
% 2.00/1.21  #Strategies tried      : 1
% 2.00/1.21  
% 2.00/1.21  Timing (in seconds)
% 2.00/1.21  ----------------------
% 2.00/1.21  Preprocessing        : 0.25
% 2.00/1.21  Parsing              : 0.14
% 2.00/1.21  CNF conversion       : 0.02
% 2.00/1.21  Main loop            : 0.20
% 2.00/1.21  Inferencing          : 0.07
% 2.00/1.21  Reduction            : 0.07
% 2.00/1.21  Demodulation         : 0.05
% 2.00/1.21  BG Simplification    : 0.01
% 2.00/1.21  Subsumption          : 0.04
% 2.00/1.21  Abstraction          : 0.01
% 2.00/1.21  MUC search           : 0.00
% 2.00/1.21  Cooper               : 0.00
% 2.00/1.21  Total                : 0.48
% 2.00/1.21  Index Insertion      : 0.00
% 2.00/1.21  Index Deletion       : 0.00
% 2.00/1.21  Index Matching       : 0.00
% 2.00/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
