%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:21 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 151 expanded)
%              Number of leaves         :   31 (  65 expanded)
%              Depth                    :   11
%              Number of atoms          :   46 ( 138 expanded)
%              Number of equality atoms :   28 ( 120 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_51,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_61,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_80,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_57,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_72,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_16,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26,plain,(
    ! [B_20,A_19] : k2_tarski(B_20,A_19) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_163,plain,(
    ! [A_56,B_57] : k3_tarski(k2_tarski(A_56,B_57)) = k2_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_289,plain,(
    ! [B_63,A_64] : k3_tarski(k2_tarski(B_63,A_64)) = k2_xboole_0(A_64,B_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_163])).

tff(c_54,plain,(
    ! [A_37,B_38] : k3_tarski(k2_tarski(A_37,B_38)) = k2_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_347,plain,(
    ! [B_68,A_69] : k2_xboole_0(B_68,A_69) = k2_xboole_0(A_69,B_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_54])).

tff(c_56,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_153,plain,(
    ! [A_54,B_55] : k4_xboole_0(A_54,k2_xboole_0(A_54,B_55)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_160,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_153])).

tff(c_184,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_16])).

tff(c_193,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_56])).

tff(c_362,plain,(
    k2_xboole_0('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_193])).

tff(c_20,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k2_xboole_0(A_14,B_15)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_407,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_20])).

tff(c_413,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_407])).

tff(c_22,plain,(
    ! [A_16] : r1_xboole_0(A_16,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_428,plain,(
    ! [A_16] : r1_xboole_0(A_16,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_22])).

tff(c_12,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_474,plain,(
    ! [A_76] : k3_xboole_0(A_76,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_413,c_12])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_479,plain,(
    ! [A_76,C_5] :
      ( ~ r1_xboole_0(A_76,'#skF_5')
      | ~ r2_hidden(C_5,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_474,c_4])).

tff(c_484,plain,(
    ! [C_5] : ~ r2_hidden(C_5,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_428,c_479])).

tff(c_80,plain,(
    ! [A_50] : k2_tarski(A_50,A_50) = k1_tarski(A_50) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_32,plain,(
    ! [D_26,B_22] : r2_hidden(D_26,k2_tarski(D_26,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_86,plain,(
    ! [A_50] : r2_hidden(A_50,k1_tarski(A_50)) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_32])).

tff(c_199,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_86])).

tff(c_421,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_199])).

tff(c_496,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_484,c_421])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:52:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.83  
% 2.88/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.83  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.88/1.83  
% 2.88/1.83  %Foreground sorts:
% 2.88/1.83  
% 2.88/1.83  
% 2.88/1.83  %Background operators:
% 2.88/1.83  
% 2.88/1.83  
% 2.88/1.83  %Foreground operators:
% 2.88/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.88/1.83  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.88/1.83  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.88/1.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.88/1.83  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.88/1.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.88/1.83  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.88/1.83  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.88/1.83  tff('#skF_5', type, '#skF_5': $i).
% 2.88/1.83  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.88/1.83  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.88/1.83  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.88/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.83  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.88/1.83  tff('#skF_4', type, '#skF_4': $i).
% 2.88/1.83  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.88/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.83  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.88/1.83  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.88/1.83  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.88/1.83  
% 2.88/1.85  tff(f_51, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.88/1.85  tff(f_61, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.88/1.85  tff(f_80, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.88/1.85  tff(f_84, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.88/1.85  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.88/1.85  tff(f_57, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.88/1.85  tff(f_47, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.88/1.85  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.88/1.85  tff(f_72, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.88/1.85  tff(f_70, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.88/1.85  tff(c_16, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.88/1.85  tff(c_26, plain, (![B_20, A_19]: (k2_tarski(B_20, A_19)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.88/1.85  tff(c_163, plain, (![A_56, B_57]: (k3_tarski(k2_tarski(A_56, B_57))=k2_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.88/1.85  tff(c_289, plain, (![B_63, A_64]: (k3_tarski(k2_tarski(B_63, A_64))=k2_xboole_0(A_64, B_63))), inference(superposition, [status(thm), theory('equality')], [c_26, c_163])).
% 2.88/1.85  tff(c_54, plain, (![A_37, B_38]: (k3_tarski(k2_tarski(A_37, B_38))=k2_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.88/1.85  tff(c_347, plain, (![B_68, A_69]: (k2_xboole_0(B_68, A_69)=k2_xboole_0(A_69, B_68))), inference(superposition, [status(thm), theory('equality')], [c_289, c_54])).
% 2.88/1.85  tff(c_56, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.88/1.85  tff(c_153, plain, (![A_54, B_55]: (k4_xboole_0(A_54, k2_xboole_0(A_54, B_55))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.88/1.85  tff(c_160, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_56, c_153])).
% 2.88/1.85  tff(c_184, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_160, c_16])).
% 2.88/1.85  tff(c_193, plain, (k2_xboole_0(k1_xboole_0, '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_184, c_56])).
% 2.88/1.85  tff(c_362, plain, (k2_xboole_0('#skF_5', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_347, c_193])).
% 2.88/1.85  tff(c_20, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k2_xboole_0(A_14, B_15))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.88/1.85  tff(c_407, plain, (k4_xboole_0('#skF_5', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_362, c_20])).
% 2.88/1.85  tff(c_413, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_407])).
% 2.88/1.85  tff(c_22, plain, (![A_16]: (r1_xboole_0(A_16, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.88/1.85  tff(c_428, plain, (![A_16]: (r1_xboole_0(A_16, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_413, c_22])).
% 2.88/1.85  tff(c_12, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.88/1.85  tff(c_474, plain, (![A_76]: (k3_xboole_0(A_76, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_413, c_413, c_12])).
% 2.88/1.85  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.88/1.85  tff(c_479, plain, (![A_76, C_5]: (~r1_xboole_0(A_76, '#skF_5') | ~r2_hidden(C_5, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_474, c_4])).
% 2.88/1.85  tff(c_484, plain, (![C_5]: (~r2_hidden(C_5, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_428, c_479])).
% 2.88/1.85  tff(c_80, plain, (![A_50]: (k2_tarski(A_50, A_50)=k1_tarski(A_50))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.88/1.85  tff(c_32, plain, (![D_26, B_22]: (r2_hidden(D_26, k2_tarski(D_26, B_22)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.88/1.85  tff(c_86, plain, (![A_50]: (r2_hidden(A_50, k1_tarski(A_50)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_32])).
% 2.88/1.85  tff(c_199, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_184, c_86])).
% 2.88/1.85  tff(c_421, plain, (r2_hidden('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_413, c_199])).
% 2.88/1.85  tff(c_496, plain, $false, inference(negUnitSimplification, [status(thm)], [c_484, c_421])).
% 2.88/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.85  
% 2.88/1.85  Inference rules
% 2.88/1.85  ----------------------
% 2.88/1.85  #Ref     : 0
% 2.88/1.85  #Sup     : 115
% 2.88/1.85  #Fact    : 0
% 2.88/1.85  #Define  : 0
% 2.88/1.85  #Split   : 0
% 2.88/1.85  #Chain   : 0
% 2.88/1.85  #Close   : 0
% 2.88/1.85  
% 2.88/1.85  Ordering : KBO
% 2.88/1.85  
% 2.88/1.85  Simplification rules
% 2.88/1.85  ----------------------
% 2.88/1.85  #Subsume      : 1
% 2.88/1.85  #Demod        : 54
% 2.88/1.85  #Tautology    : 87
% 2.88/1.85  #SimpNegUnit  : 1
% 2.88/1.85  #BackRed      : 18
% 2.88/1.85  
% 2.88/1.85  #Partial instantiations: 0
% 2.88/1.85  #Strategies tried      : 1
% 2.88/1.85  
% 2.88/1.85  Timing (in seconds)
% 2.88/1.85  ----------------------
% 2.88/1.86  Preprocessing        : 0.53
% 2.88/1.86  Parsing              : 0.28
% 2.88/1.86  CNF conversion       : 0.04
% 2.88/1.86  Main loop            : 0.38
% 2.88/1.86  Inferencing          : 0.13
% 2.88/1.86  Reduction            : 0.14
% 2.88/1.86  Demodulation         : 0.11
% 2.88/1.86  BG Simplification    : 0.02
% 2.88/1.86  Subsumption          : 0.06
% 2.88/1.86  Abstraction          : 0.02
% 2.88/1.86  MUC search           : 0.00
% 2.88/1.86  Cooper               : 0.00
% 2.88/1.86  Total                : 0.96
% 2.88/1.86  Index Insertion      : 0.00
% 2.88/1.86  Index Deletion       : 0.00
% 2.88/1.86  Index Matching       : 0.00
% 2.88/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
