%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:28 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 103 expanded)
%              Number of leaves         :   24 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :   56 ( 116 expanded)
%              Number of equality atoms :   38 (  81 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(B,C) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_53,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_61,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_46,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = k1_xboole_0
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_53,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_46])).

tff(c_98,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k4_xboole_0(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_119,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k3_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_98])).

tff(c_129,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_119])).

tff(c_28,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_54,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_46])).

tff(c_24,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_81,plain,(
    ! [A_28,B_29,C_30] :
      ( ~ r1_xboole_0(A_28,B_29)
      | ~ r2_hidden(C_30,k3_xboole_0(A_28,B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_270,plain,(
    ! [A_44,B_45] :
      ( ~ r1_xboole_0(A_44,B_45)
      | k3_xboole_0(A_44,B_45) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_81])).

tff(c_279,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_270])).

tff(c_16,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_292,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_16])).

tff(c_299,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_292])).

tff(c_12,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_122,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k3_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_98])).

tff(c_131,plain,(
    ! [A_34] : k4_xboole_0(A_34,A_34) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_122])).

tff(c_18,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_136,plain,(
    ! [A_34] : k4_xboole_0(A_34,k1_xboole_0) = k3_xboole_0(A_34,A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_18])).

tff(c_148,plain,(
    ! [A_34] : k3_xboole_0(A_34,A_34) = A_34 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_136])).

tff(c_130,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_122])).

tff(c_228,plain,(
    ! [A_41,B_42,C_43] : k2_xboole_0(k4_xboole_0(A_41,B_42),k3_xboole_0(A_41,C_43)) = k4_xboole_0(A_41,k4_xboole_0(B_42,C_43)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_246,plain,(
    ! [A_11,C_43] : k4_xboole_0(A_11,k4_xboole_0(A_11,C_43)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(A_11,C_43)) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_228])).

tff(c_595,plain,(
    ! [A_56,C_57] : k2_xboole_0(k1_xboole_0,k3_xboole_0(A_56,C_57)) = k3_xboole_0(A_56,C_57) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_246])).

tff(c_613,plain,(
    ! [A_34] : k3_xboole_0(A_34,A_34) = k2_xboole_0(k1_xboole_0,A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_595])).

tff(c_628,plain,(
    ! [A_34] : k2_xboole_0(k1_xboole_0,A_34) = A_34 ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_613])).

tff(c_255,plain,(
    ! [C_43] : k4_xboole_0('#skF_3',k4_xboole_0('#skF_4',C_43)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_3',C_43)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_228])).

tff(c_654,plain,(
    ! [C_59] : k4_xboole_0('#skF_3',k4_xboole_0('#skF_4',C_59)) = k3_xboole_0('#skF_3',C_59) ),
    inference(demodulation,[status(thm),theory(equality)],[c_628,c_255])).

tff(c_676,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_654])).

tff(c_697,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_54,c_676])).

tff(c_699,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_697])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:14:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.45  
% 2.68/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.45  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.68/1.45  
% 2.68/1.45  %Foreground sorts:
% 2.68/1.45  
% 2.68/1.45  
% 2.68/1.45  %Background operators:
% 2.68/1.45  
% 2.68/1.45  
% 2.68/1.45  %Foreground operators:
% 2.68/1.45  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.68/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.68/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.68/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.68/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.68/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.68/1.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.68/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.68/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.68/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.68/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.68/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.68/1.45  
% 2.68/1.47  tff(f_70, negated_conjecture, ~(![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 2.68/1.47  tff(f_55, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.68/1.47  tff(f_51, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.68/1.47  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.68/1.47  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.68/1.47  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.68/1.47  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.68/1.47  tff(f_53, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.68/1.47  tff(f_61, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 2.68/1.47  tff(c_22, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.68/1.47  tff(c_14, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.68/1.47  tff(c_26, plain, (r1_tarski('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.68/1.47  tff(c_46, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=k1_xboole_0 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.68/1.47  tff(c_53, plain, (k4_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_46])).
% 2.68/1.47  tff(c_98, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k4_xboole_0(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.68/1.47  tff(c_119, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_53, c_98])).
% 2.68/1.47  tff(c_129, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_119])).
% 2.68/1.47  tff(c_28, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.68/1.47  tff(c_54, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_46])).
% 2.68/1.47  tff(c_24, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.68/1.47  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.68/1.47  tff(c_81, plain, (![A_28, B_29, C_30]: (~r1_xboole_0(A_28, B_29) | ~r2_hidden(C_30, k3_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.68/1.47  tff(c_270, plain, (![A_44, B_45]: (~r1_xboole_0(A_44, B_45) | k3_xboole_0(A_44, B_45)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_81])).
% 2.68/1.47  tff(c_279, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_270])).
% 2.68/1.47  tff(c_16, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.68/1.47  tff(c_292, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_279, c_16])).
% 2.68/1.47  tff(c_299, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_292])).
% 2.68/1.47  tff(c_12, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.68/1.47  tff(c_122, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k3_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_98])).
% 2.68/1.47  tff(c_131, plain, (![A_34]: (k4_xboole_0(A_34, A_34)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_122])).
% 2.68/1.47  tff(c_18, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.68/1.47  tff(c_136, plain, (![A_34]: (k4_xboole_0(A_34, k1_xboole_0)=k3_xboole_0(A_34, A_34))), inference(superposition, [status(thm), theory('equality')], [c_131, c_18])).
% 2.68/1.47  tff(c_148, plain, (![A_34]: (k3_xboole_0(A_34, A_34)=A_34)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_136])).
% 2.68/1.47  tff(c_130, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_122])).
% 2.68/1.47  tff(c_228, plain, (![A_41, B_42, C_43]: (k2_xboole_0(k4_xboole_0(A_41, B_42), k3_xboole_0(A_41, C_43))=k4_xboole_0(A_41, k4_xboole_0(B_42, C_43)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.68/1.47  tff(c_246, plain, (![A_11, C_43]: (k4_xboole_0(A_11, k4_xboole_0(A_11, C_43))=k2_xboole_0(k1_xboole_0, k3_xboole_0(A_11, C_43)))), inference(superposition, [status(thm), theory('equality')], [c_130, c_228])).
% 2.68/1.47  tff(c_595, plain, (![A_56, C_57]: (k2_xboole_0(k1_xboole_0, k3_xboole_0(A_56, C_57))=k3_xboole_0(A_56, C_57))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_246])).
% 2.68/1.47  tff(c_613, plain, (![A_34]: (k3_xboole_0(A_34, A_34)=k2_xboole_0(k1_xboole_0, A_34))), inference(superposition, [status(thm), theory('equality')], [c_148, c_595])).
% 2.68/1.47  tff(c_628, plain, (![A_34]: (k2_xboole_0(k1_xboole_0, A_34)=A_34)), inference(demodulation, [status(thm), theory('equality')], [c_148, c_613])).
% 2.68/1.47  tff(c_255, plain, (![C_43]: (k4_xboole_0('#skF_3', k4_xboole_0('#skF_4', C_43))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_3', C_43)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_228])).
% 2.68/1.47  tff(c_654, plain, (![C_59]: (k4_xboole_0('#skF_3', k4_xboole_0('#skF_4', C_59))=k3_xboole_0('#skF_3', C_59))), inference(demodulation, [status(thm), theory('equality')], [c_628, c_255])).
% 2.68/1.47  tff(c_676, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_299, c_654])).
% 2.68/1.47  tff(c_697, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_129, c_54, c_676])).
% 2.68/1.47  tff(c_699, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_697])).
% 2.68/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.47  
% 2.68/1.47  Inference rules
% 2.68/1.47  ----------------------
% 2.68/1.47  #Ref     : 0
% 2.68/1.47  #Sup     : 169
% 2.68/1.47  #Fact    : 0
% 2.68/1.47  #Define  : 0
% 2.68/1.47  #Split   : 3
% 2.68/1.47  #Chain   : 0
% 2.68/1.47  #Close   : 0
% 2.68/1.47  
% 2.68/1.47  Ordering : KBO
% 2.68/1.47  
% 2.68/1.47  Simplification rules
% 2.68/1.47  ----------------------
% 2.68/1.47  #Subsume      : 2
% 2.68/1.47  #Demod        : 111
% 2.68/1.47  #Tautology    : 103
% 2.68/1.47  #SimpNegUnit  : 5
% 2.68/1.47  #BackRed      : 1
% 2.68/1.47  
% 2.68/1.47  #Partial instantiations: 0
% 2.68/1.47  #Strategies tried      : 1
% 2.68/1.47  
% 2.68/1.47  Timing (in seconds)
% 2.68/1.47  ----------------------
% 2.68/1.47  Preprocessing        : 0.39
% 2.68/1.47  Parsing              : 0.24
% 2.68/1.47  CNF conversion       : 0.02
% 2.68/1.47  Main loop            : 0.30
% 2.68/1.47  Inferencing          : 0.12
% 2.68/1.47  Reduction            : 0.10
% 2.68/1.47  Demodulation         : 0.08
% 2.68/1.47  BG Simplification    : 0.02
% 2.68/1.47  Subsumption          : 0.04
% 2.68/1.47  Abstraction          : 0.02
% 2.68/1.47  MUC search           : 0.00
% 2.68/1.47  Cooper               : 0.00
% 2.68/1.47  Total                : 0.72
% 2.68/1.47  Index Insertion      : 0.00
% 2.68/1.47  Index Deletion       : 0.00
% 2.68/1.47  Index Matching       : 0.00
% 2.68/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
