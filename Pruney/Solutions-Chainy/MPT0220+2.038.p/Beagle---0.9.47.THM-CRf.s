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
% DateTime   : Thu Dec  3 09:48:09 EST 2020

% Result     : Theorem 6.40s
% Output     : CNFRefutation 6.40s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 123 expanded)
%              Number of leaves         :   26 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :   45 ( 110 expanded)
%              Number of equality atoms :   40 ( 105 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_12,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_226,plain,(
    ! [A_43,B_44] : k5_xboole_0(A_43,k3_xboole_0(A_43,B_44)) = k4_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_247,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = k4_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_226])).

tff(c_265,plain,(
    ! [A_47] : k5_xboole_0(A_47,k1_xboole_0) = A_47 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_247])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_271,plain,(
    ! [A_47] : k5_xboole_0(k1_xboole_0,A_47) = A_47 ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_4])).

tff(c_16,plain,(
    ! [A_14] : k5_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26,plain,(
    ! [A_23,B_24] : r1_tarski(k1_tarski(A_23),k2_tarski(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_207,plain,(
    ! [A_39,B_40] :
      ( k3_xboole_0(A_39,B_40) = A_39
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_668,plain,(
    ! [A_62,B_63] : k3_xboole_0(k1_tarski(A_62),k2_tarski(A_62,B_63)) = k1_tarski(A_62) ),
    inference(resolution,[status(thm)],[c_26,c_207])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_674,plain,(
    ! [A_62,B_63] : k5_xboole_0(k1_tarski(A_62),k1_tarski(A_62)) = k4_xboole_0(k1_tarski(A_62),k2_tarski(A_62,B_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_668,c_6])).

tff(c_916,plain,(
    ! [A_69,B_70] : k4_xboole_0(k1_tarski(A_69),k2_tarski(A_69,B_70)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_674])).

tff(c_18,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_921,plain,(
    ! [A_69,B_70] : k2_xboole_0(k2_tarski(A_69,B_70),k1_tarski(A_69)) = k5_xboole_0(k2_tarski(A_69,B_70),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_916,c_18])).

tff(c_8101,plain,(
    ! [A_163,B_164] : k2_xboole_0(k2_tarski(A_163,B_164),k1_tarski(A_163)) = k2_tarski(A_163,B_164) ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_4,c_921])).

tff(c_426,plain,(
    ! [A_55,B_56,C_57] : k5_xboole_0(k5_xboole_0(A_55,B_56),C_57) = k5_xboole_0(A_55,k5_xboole_0(B_56,C_57)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1326,plain,(
    ! [C_83,A_84,B_85] : k5_xboole_0(C_83,k5_xboole_0(A_84,B_85)) = k5_xboole_0(A_84,k5_xboole_0(B_85,C_83)) ),
    inference(superposition,[status(thm),theory(equality)],[c_426,c_4])).

tff(c_1688,plain,(
    ! [A_86,C_87] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_86,C_87)) = k5_xboole_0(C_87,A_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_1326])).

tff(c_1802,plain,(
    ! [B_16,A_15] : k5_xboole_0(k4_xboole_0(B_16,A_15),A_15) = k5_xboole_0(k1_xboole_0,k2_xboole_0(A_15,B_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1688])).

tff(c_1844,plain,(
    ! [B_16,A_15] : k5_xboole_0(k4_xboole_0(B_16,A_15),A_15) = k2_xboole_0(A_15,B_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_1802])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_244,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_226])).

tff(c_1767,plain,(
    ! [A_1,B_2] : k5_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k5_xboole_0(k1_xboole_0,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_1688])).

tff(c_1835,plain,(
    ! [A_1,B_2] : k5_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k4_xboole_0(B_2,A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_1767])).

tff(c_4064,plain,(
    ! [A_121,B_122,C_123] : k5_xboole_0(A_121,k5_xboole_0(k3_xboole_0(A_121,B_122),C_123)) = k5_xboole_0(k4_xboole_0(A_121,B_122),C_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_426])).

tff(c_4146,plain,(
    ! [A_1,B_2] : k5_xboole_0(k4_xboole_0(A_1,B_2),B_2) = k5_xboole_0(A_1,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1835,c_4064])).

tff(c_4272,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1844,c_18,c_4146])).

tff(c_8131,plain,(
    ! [A_163,B_164] : k2_xboole_0(k1_tarski(A_163),k2_tarski(A_163,B_164)) = k2_tarski(A_163,B_164) ),
    inference(superposition,[status(thm),theory(equality)],[c_8101,c_4272])).

tff(c_28,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8131,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n007.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 16:01:21 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.17/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.40/2.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.40/2.53  
% 6.40/2.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.40/2.53  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 6.40/2.53  
% 6.40/2.53  %Foreground sorts:
% 6.40/2.53  
% 6.40/2.53  
% 6.40/2.53  %Background operators:
% 6.40/2.53  
% 6.40/2.53  
% 6.40/2.53  %Foreground operators:
% 6.40/2.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.40/2.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.40/2.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.40/2.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.40/2.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.40/2.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.40/2.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.40/2.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.40/2.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.40/2.53  tff('#skF_2', type, '#skF_2': $i).
% 6.40/2.53  tff('#skF_1', type, '#skF_1': $i).
% 6.40/2.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.40/2.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.40/2.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.40/2.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.40/2.53  
% 6.40/2.54  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 6.40/2.54  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 6.40/2.54  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.40/2.54  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 6.40/2.54  tff(f_43, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.40/2.54  tff(f_53, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 6.40/2.54  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.40/2.54  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 6.40/2.54  tff(f_41, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.40/2.54  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.40/2.54  tff(f_56, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 6.40/2.54  tff(c_12, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.40/2.54  tff(c_10, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.40/2.54  tff(c_226, plain, (![A_43, B_44]: (k5_xboole_0(A_43, k3_xboole_0(A_43, B_44))=k4_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.40/2.54  tff(c_247, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=k4_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_226])).
% 6.40/2.54  tff(c_265, plain, (![A_47]: (k5_xboole_0(A_47, k1_xboole_0)=A_47)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_247])).
% 6.40/2.54  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.40/2.54  tff(c_271, plain, (![A_47]: (k5_xboole_0(k1_xboole_0, A_47)=A_47)), inference(superposition, [status(thm), theory('equality')], [c_265, c_4])).
% 6.40/2.54  tff(c_16, plain, (![A_14]: (k5_xboole_0(A_14, A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.40/2.54  tff(c_26, plain, (![A_23, B_24]: (r1_tarski(k1_tarski(A_23), k2_tarski(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.40/2.54  tff(c_207, plain, (![A_39, B_40]: (k3_xboole_0(A_39, B_40)=A_39 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.40/2.54  tff(c_668, plain, (![A_62, B_63]: (k3_xboole_0(k1_tarski(A_62), k2_tarski(A_62, B_63))=k1_tarski(A_62))), inference(resolution, [status(thm)], [c_26, c_207])).
% 6.40/2.54  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.40/2.54  tff(c_674, plain, (![A_62, B_63]: (k5_xboole_0(k1_tarski(A_62), k1_tarski(A_62))=k4_xboole_0(k1_tarski(A_62), k2_tarski(A_62, B_63)))), inference(superposition, [status(thm), theory('equality')], [c_668, c_6])).
% 6.40/2.54  tff(c_916, plain, (![A_69, B_70]: (k4_xboole_0(k1_tarski(A_69), k2_tarski(A_69, B_70))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_674])).
% 6.40/2.54  tff(c_18, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.40/2.54  tff(c_921, plain, (![A_69, B_70]: (k2_xboole_0(k2_tarski(A_69, B_70), k1_tarski(A_69))=k5_xboole_0(k2_tarski(A_69, B_70), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_916, c_18])).
% 6.40/2.54  tff(c_8101, plain, (![A_163, B_164]: (k2_xboole_0(k2_tarski(A_163, B_164), k1_tarski(A_163))=k2_tarski(A_163, B_164))), inference(demodulation, [status(thm), theory('equality')], [c_271, c_4, c_921])).
% 6.40/2.54  tff(c_426, plain, (![A_55, B_56, C_57]: (k5_xboole_0(k5_xboole_0(A_55, B_56), C_57)=k5_xboole_0(A_55, k5_xboole_0(B_56, C_57)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.40/2.54  tff(c_1326, plain, (![C_83, A_84, B_85]: (k5_xboole_0(C_83, k5_xboole_0(A_84, B_85))=k5_xboole_0(A_84, k5_xboole_0(B_85, C_83)))), inference(superposition, [status(thm), theory('equality')], [c_426, c_4])).
% 6.40/2.54  tff(c_1688, plain, (![A_86, C_87]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_86, C_87))=k5_xboole_0(C_87, A_86))), inference(superposition, [status(thm), theory('equality')], [c_271, c_1326])).
% 6.40/2.54  tff(c_1802, plain, (![B_16, A_15]: (k5_xboole_0(k4_xboole_0(B_16, A_15), A_15)=k5_xboole_0(k1_xboole_0, k2_xboole_0(A_15, B_16)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1688])).
% 6.40/2.54  tff(c_1844, plain, (![B_16, A_15]: (k5_xboole_0(k4_xboole_0(B_16, A_15), A_15)=k2_xboole_0(A_15, B_16))), inference(demodulation, [status(thm), theory('equality')], [c_271, c_1802])).
% 6.40/2.54  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.40/2.54  tff(c_244, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_226])).
% 6.40/2.54  tff(c_1767, plain, (![A_1, B_2]: (k5_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k5_xboole_0(k1_xboole_0, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_244, c_1688])).
% 6.40/2.54  tff(c_1835, plain, (![A_1, B_2]: (k5_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k4_xboole_0(B_2, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_271, c_1767])).
% 6.40/2.54  tff(c_4064, plain, (![A_121, B_122, C_123]: (k5_xboole_0(A_121, k5_xboole_0(k3_xboole_0(A_121, B_122), C_123))=k5_xboole_0(k4_xboole_0(A_121, B_122), C_123))), inference(superposition, [status(thm), theory('equality')], [c_6, c_426])).
% 6.40/2.54  tff(c_4146, plain, (![A_1, B_2]: (k5_xboole_0(k4_xboole_0(A_1, B_2), B_2)=k5_xboole_0(A_1, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_1835, c_4064])).
% 6.40/2.54  tff(c_4272, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_1844, c_18, c_4146])).
% 6.40/2.54  tff(c_8131, plain, (![A_163, B_164]: (k2_xboole_0(k1_tarski(A_163), k2_tarski(A_163, B_164))=k2_tarski(A_163, B_164))), inference(superposition, [status(thm), theory('equality')], [c_8101, c_4272])).
% 6.40/2.54  tff(c_28, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.40/2.54  tff(c_8171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8131, c_28])).
% 6.40/2.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.40/2.54  
% 6.40/2.54  Inference rules
% 6.40/2.54  ----------------------
% 6.40/2.54  #Ref     : 0
% 6.40/2.54  #Sup     : 2036
% 6.40/2.54  #Fact    : 0
% 6.40/2.54  #Define  : 0
% 6.40/2.54  #Split   : 0
% 6.40/2.54  #Chain   : 0
% 6.40/2.54  #Close   : 0
% 6.40/2.54  
% 6.40/2.54  Ordering : KBO
% 6.40/2.54  
% 6.40/2.54  Simplification rules
% 6.40/2.54  ----------------------
% 6.40/2.54  #Subsume      : 96
% 6.40/2.54  #Demod        : 2162
% 6.40/2.54  #Tautology    : 1078
% 6.40/2.54  #SimpNegUnit  : 0
% 6.40/2.54  #BackRed      : 1
% 6.40/2.54  
% 6.40/2.54  #Partial instantiations: 0
% 6.40/2.54  #Strategies tried      : 1
% 6.40/2.54  
% 6.40/2.54  Timing (in seconds)
% 6.40/2.54  ----------------------
% 6.40/2.55  Preprocessing        : 0.34
% 6.40/2.55  Parsing              : 0.18
% 6.40/2.55  CNF conversion       : 0.02
% 6.40/2.55  Main loop            : 1.45
% 6.40/2.55  Inferencing          : 0.36
% 6.40/2.55  Reduction            : 0.83
% 6.40/2.55  Demodulation         : 0.75
% 6.40/2.55  BG Simplification    : 0.05
% 6.40/2.55  Subsumption          : 0.15
% 6.40/2.55  Abstraction          : 0.08
% 6.40/2.55  MUC search           : 0.00
% 6.40/2.55  Cooper               : 0.00
% 6.40/2.55  Total                : 1.82
% 6.40/2.55  Index Insertion      : 0.00
% 6.40/2.55  Index Deletion       : 0.00
% 6.40/2.55  Index Matching       : 0.00
% 6.40/2.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
