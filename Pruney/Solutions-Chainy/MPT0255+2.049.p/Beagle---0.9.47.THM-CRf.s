%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:45 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 161 expanded)
%              Number of leaves         :   24 (  64 expanded)
%              Depth                    :   10
%              Number of atoms          :   57 ( 186 expanded)
%              Number of equality atoms :   26 (  97 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_207,plain,(
    ! [A_43,B_44] :
      ( k2_xboole_0(A_43,B_44) = B_44
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_264,plain,(
    ! [A_48] : k2_xboole_0(k1_xboole_0,A_48) = A_48 ),
    inference(resolution,[status(thm)],[c_12,c_207])).

tff(c_290,plain,(
    ! [B_2] : k2_xboole_0(B_2,k1_xboole_0) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_264])).

tff(c_32,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_54,plain,(
    ! [B_30,A_31] : k2_xboole_0(B_30,A_31) = k2_xboole_0(A_31,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_113,plain,(
    ! [A_32,B_33] : r1_tarski(A_32,k2_xboole_0(B_33,A_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_14])).

tff(c_122,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_113])).

tff(c_230,plain,(
    k2_xboole_0('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_122,c_207])).

tff(c_360,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_230])).

tff(c_430,plain,(
    ! [A_7] : r1_tarski('#skF_3',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_12])).

tff(c_277,plain,(
    ! [A_48] : k2_xboole_0(A_48,k1_xboole_0) = A_48 ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_2])).

tff(c_461,plain,(
    ! [A_48] : k2_xboole_0(A_48,'#skF_3') = A_48 ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_277])).

tff(c_428,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_32])).

tff(c_522,plain,(
    k2_tarski('#skF_1','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_461,c_428])).

tff(c_28,plain,(
    ! [A_18,C_20,B_19] :
      ( r2_hidden(A_18,C_20)
      | ~ r1_tarski(k2_tarski(A_18,B_19),C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_615,plain,(
    ! [C_20] :
      ( r2_hidden('#skF_1',C_20)
      | ~ r1_tarski('#skF_3',C_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_522,c_28])).

tff(c_624,plain,(
    ! [C_20] : r2_hidden('#skF_1',C_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_615])).

tff(c_30,plain,(
    ! [A_21,B_22] : k2_xboole_0(k1_tarski(A_21),B_22) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_86,plain,(
    ! [A_31,A_21] : k2_xboole_0(A_31,k1_tarski(A_21)) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_30])).

tff(c_271,plain,(
    ! [A_21] : k1_tarski(A_21) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_86])).

tff(c_421,plain,(
    ! [A_21] : k1_tarski(A_21) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_271])).

tff(c_16,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_710,plain,(
    ! [A_77,B_78,C_79] :
      ( r1_tarski(k2_tarski(A_77,B_78),C_79)
      | ~ r2_hidden(B_78,C_79)
      | ~ r2_hidden(A_77,C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1567,plain,(
    ! [A_110,C_111] :
      ( r1_tarski(k1_tarski(A_110),C_111)
      | ~ r2_hidden(A_110,C_111)
      | ~ r2_hidden(A_110,C_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_710])).

tff(c_591,plain,(
    ! [B_60,A_61] :
      ( B_60 = A_61
      | ~ r1_tarski(B_60,A_61)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_600,plain,(
    ! [A_7] :
      ( A_7 = '#skF_3'
      | ~ r1_tarski(A_7,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_430,c_591])).

tff(c_1574,plain,(
    ! [A_110] :
      ( k1_tarski(A_110) = '#skF_3'
      | ~ r2_hidden(A_110,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1567,c_600])).

tff(c_1586,plain,(
    ! [A_112] : ~ r2_hidden(A_112,'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_421,c_1574])).

tff(c_1594,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_624,c_1586])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:09:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.61/1.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/1.95  
% 3.61/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/1.95  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.61/1.95  
% 3.61/1.95  %Foreground sorts:
% 3.61/1.95  
% 3.61/1.95  
% 3.61/1.95  %Background operators:
% 3.61/1.95  
% 3.61/1.95  
% 3.61/1.95  %Foreground operators:
% 3.61/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.61/1.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.61/1.95  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.61/1.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.61/1.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.61/1.95  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.61/1.95  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.61/1.95  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.61/1.95  tff('#skF_2', type, '#skF_2': $i).
% 3.61/1.95  tff('#skF_3', type, '#skF_3': $i).
% 3.61/1.95  tff('#skF_1', type, '#skF_1': $i).
% 3.61/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.61/1.95  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.61/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.61/1.95  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.61/1.95  
% 3.61/1.97  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.61/1.97  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.61/1.97  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.61/1.97  tff(f_62, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 3.61/1.97  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.61/1.97  tff(f_55, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.61/1.97  tff(f_58, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.61/1.97  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.61/1.97  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.61/1.97  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.61/1.97  tff(c_12, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.61/1.97  tff(c_207, plain, (![A_43, B_44]: (k2_xboole_0(A_43, B_44)=B_44 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.61/1.97  tff(c_264, plain, (![A_48]: (k2_xboole_0(k1_xboole_0, A_48)=A_48)), inference(resolution, [status(thm)], [c_12, c_207])).
% 3.61/1.97  tff(c_290, plain, (![B_2]: (k2_xboole_0(B_2, k1_xboole_0)=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_264])).
% 3.61/1.97  tff(c_32, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.61/1.97  tff(c_54, plain, (![B_30, A_31]: (k2_xboole_0(B_30, A_31)=k2_xboole_0(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.61/1.97  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.61/1.97  tff(c_113, plain, (![A_32, B_33]: (r1_tarski(A_32, k2_xboole_0(B_33, A_32)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_14])).
% 3.61/1.97  tff(c_122, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_113])).
% 3.61/1.97  tff(c_230, plain, (k2_xboole_0('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_122, c_207])).
% 3.61/1.97  tff(c_360, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_290, c_230])).
% 3.61/1.97  tff(c_430, plain, (![A_7]: (r1_tarski('#skF_3', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_360, c_12])).
% 3.61/1.97  tff(c_277, plain, (![A_48]: (k2_xboole_0(A_48, k1_xboole_0)=A_48)), inference(superposition, [status(thm), theory('equality')], [c_264, c_2])).
% 3.61/1.97  tff(c_461, plain, (![A_48]: (k2_xboole_0(A_48, '#skF_3')=A_48)), inference(demodulation, [status(thm), theory('equality')], [c_360, c_277])).
% 3.61/1.97  tff(c_428, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_360, c_32])).
% 3.61/1.97  tff(c_522, plain, (k2_tarski('#skF_1', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_461, c_428])).
% 3.61/1.97  tff(c_28, plain, (![A_18, C_20, B_19]: (r2_hidden(A_18, C_20) | ~r1_tarski(k2_tarski(A_18, B_19), C_20))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.61/1.97  tff(c_615, plain, (![C_20]: (r2_hidden('#skF_1', C_20) | ~r1_tarski('#skF_3', C_20))), inference(superposition, [status(thm), theory('equality')], [c_522, c_28])).
% 3.61/1.97  tff(c_624, plain, (![C_20]: (r2_hidden('#skF_1', C_20))), inference(demodulation, [status(thm), theory('equality')], [c_430, c_615])).
% 3.61/1.97  tff(c_30, plain, (![A_21, B_22]: (k2_xboole_0(k1_tarski(A_21), B_22)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.61/1.97  tff(c_86, plain, (![A_31, A_21]: (k2_xboole_0(A_31, k1_tarski(A_21))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_54, c_30])).
% 3.61/1.97  tff(c_271, plain, (![A_21]: (k1_tarski(A_21)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_264, c_86])).
% 3.61/1.97  tff(c_421, plain, (![A_21]: (k1_tarski(A_21)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_360, c_271])).
% 3.61/1.97  tff(c_16, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.61/1.97  tff(c_710, plain, (![A_77, B_78, C_79]: (r1_tarski(k2_tarski(A_77, B_78), C_79) | ~r2_hidden(B_78, C_79) | ~r2_hidden(A_77, C_79))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.61/1.97  tff(c_1567, plain, (![A_110, C_111]: (r1_tarski(k1_tarski(A_110), C_111) | ~r2_hidden(A_110, C_111) | ~r2_hidden(A_110, C_111))), inference(superposition, [status(thm), theory('equality')], [c_16, c_710])).
% 3.61/1.97  tff(c_591, plain, (![B_60, A_61]: (B_60=A_61 | ~r1_tarski(B_60, A_61) | ~r1_tarski(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.61/1.97  tff(c_600, plain, (![A_7]: (A_7='#skF_3' | ~r1_tarski(A_7, '#skF_3'))), inference(resolution, [status(thm)], [c_430, c_591])).
% 3.61/1.97  tff(c_1574, plain, (![A_110]: (k1_tarski(A_110)='#skF_3' | ~r2_hidden(A_110, '#skF_3'))), inference(resolution, [status(thm)], [c_1567, c_600])).
% 3.61/1.97  tff(c_1586, plain, (![A_112]: (~r2_hidden(A_112, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_421, c_1574])).
% 3.61/1.97  tff(c_1594, plain, $false, inference(resolution, [status(thm)], [c_624, c_1586])).
% 3.61/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/1.97  
% 3.61/1.97  Inference rules
% 3.61/1.97  ----------------------
% 3.61/1.97  #Ref     : 0
% 3.61/1.97  #Sup     : 363
% 3.61/1.97  #Fact    : 0
% 3.61/1.97  #Define  : 0
% 3.61/1.97  #Split   : 2
% 3.61/1.97  #Chain   : 0
% 3.61/1.97  #Close   : 0
% 3.61/1.97  
% 3.61/1.97  Ordering : KBO
% 3.61/1.97  
% 3.61/1.97  Simplification rules
% 3.61/1.97  ----------------------
% 3.61/1.97  #Subsume      : 37
% 3.61/1.97  #Demod        : 339
% 3.61/1.97  #Tautology    : 269
% 3.61/1.97  #SimpNegUnit  : 1
% 3.61/1.97  #BackRed      : 16
% 3.61/1.97  
% 3.61/1.97  #Partial instantiations: 0
% 3.61/1.97  #Strategies tried      : 1
% 3.61/1.97  
% 3.61/1.97  Timing (in seconds)
% 3.61/1.97  ----------------------
% 3.78/1.98  Preprocessing        : 0.44
% 3.78/1.98  Parsing              : 0.23
% 3.78/1.98  CNF conversion       : 0.03
% 3.78/1.98  Main loop            : 0.64
% 3.78/1.98  Inferencing          : 0.21
% 3.78/1.98  Reduction            : 0.27
% 3.78/1.98  Demodulation         : 0.22
% 3.78/1.98  BG Simplification    : 0.03
% 3.78/1.98  Subsumption          : 0.10
% 3.78/1.98  Abstraction          : 0.03
% 3.78/1.98  MUC search           : 0.00
% 3.78/1.98  Cooper               : 0.00
% 3.78/1.98  Total                : 1.13
% 3.78/1.98  Index Insertion      : 0.00
% 3.78/1.98  Index Deletion       : 0.00
% 3.78/1.98  Index Matching       : 0.00
% 3.78/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
