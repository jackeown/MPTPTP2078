%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:48 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :   54 (  82 expanded)
%              Number of leaves         :   30 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   45 (  83 expanded)
%              Number of equality atoms :   40 (  74 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_12,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_241,plain,(
    ! [A_62,B_63] : k5_xboole_0(A_62,k3_xboole_0(A_62,B_63)) = k4_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_262,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = k4_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_241])).

tff(c_267,plain,(
    ! [A_64] : k4_xboole_0(A_64,k1_xboole_0) = A_64 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_262])).

tff(c_10,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_273,plain,(
    ! [A_64] : k4_xboole_0(A_64,A_64) = k3_xboole_0(A_64,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_10])).

tff(c_330,plain,(
    ! [A_68] : k4_xboole_0(A_68,A_68) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_273])).

tff(c_18,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_338,plain,(
    ! [A_68] : k5_xboole_0(A_68,k1_xboole_0) = k2_xboole_0(A_68,A_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_18])).

tff(c_357,plain,(
    ! [A_68] : k2_xboole_0(A_68,A_68) = A_68 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_338])).

tff(c_20,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_36,plain,(
    ! [A_40,B_41] :
      ( k5_xboole_0(k1_tarski(A_40),k1_tarski(B_41)) = k2_tarski(A_40,B_41)
      | B_41 = A_40 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_221,plain,(
    ! [A_58,B_59] :
      ( r1_xboole_0(k1_tarski(A_58),k1_tarski(B_59))
      | B_59 = A_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = A_11
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_549,plain,(
    ! [A_81,B_82] :
      ( k4_xboole_0(k1_tarski(A_81),k1_tarski(B_82)) = k1_tarski(A_81)
      | B_82 = A_81 ) ),
    inference(resolution,[status(thm)],[c_221,c_14])).

tff(c_801,plain,(
    ! [B_100,A_101] :
      ( k5_xboole_0(k1_tarski(B_100),k1_tarski(A_101)) = k2_xboole_0(k1_tarski(B_100),k1_tarski(A_101))
      | B_100 = A_101 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_549,c_18])).

tff(c_1099,plain,(
    ! [A_116,B_117] :
      ( k2_xboole_0(k1_tarski(A_116),k1_tarski(B_117)) = k2_tarski(A_116,B_117)
      | B_117 = A_116
      | B_117 = A_116 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_801])).

tff(c_32,plain,(
    ! [A_36,B_37] : k3_tarski(k2_tarski(A_36,B_37)) = k2_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_38,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_39,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_38])).

tff(c_1120,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1099,c_39])).

tff(c_1124,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) != k2_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1120,c_1120,c_39])).

tff(c_1127,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_20,c_1124])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:12:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.52  
% 2.92/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.52  %$ r1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.92/1.52  
% 2.92/1.52  %Foreground sorts:
% 2.92/1.52  
% 2.92/1.52  
% 2.92/1.52  %Background operators:
% 2.92/1.52  
% 2.92/1.52  
% 2.92/1.52  %Foreground operators:
% 2.92/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.92/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.92/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.92/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.92/1.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.92/1.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.92/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.92/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.92/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.92/1.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.92/1.52  tff('#skF_2', type, '#skF_2': $i).
% 2.92/1.52  tff('#skF_1', type, '#skF_1': $i).
% 2.92/1.52  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.92/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.92/1.52  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.92/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.92/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.92/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.92/1.52  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.92/1.52  
% 3.24/1.53  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.24/1.53  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.24/1.53  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.24/1.53  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.24/1.53  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.24/1.53  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.24/1.53  tff(f_67, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 3.24/1.53  tff(f_62, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 3.24/1.53  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.24/1.53  tff(f_57, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.24/1.53  tff(f_70, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 3.24/1.53  tff(c_12, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.24/1.53  tff(c_8, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.24/1.53  tff(c_241, plain, (![A_62, B_63]: (k5_xboole_0(A_62, k3_xboole_0(A_62, B_63))=k4_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.24/1.53  tff(c_262, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=k4_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_241])).
% 3.24/1.53  tff(c_267, plain, (![A_64]: (k4_xboole_0(A_64, k1_xboole_0)=A_64)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_262])).
% 3.24/1.53  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.24/1.53  tff(c_273, plain, (![A_64]: (k4_xboole_0(A_64, A_64)=k3_xboole_0(A_64, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_267, c_10])).
% 3.24/1.53  tff(c_330, plain, (![A_68]: (k4_xboole_0(A_68, A_68)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_273])).
% 3.24/1.53  tff(c_18, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.24/1.53  tff(c_338, plain, (![A_68]: (k5_xboole_0(A_68, k1_xboole_0)=k2_xboole_0(A_68, A_68))), inference(superposition, [status(thm), theory('equality')], [c_330, c_18])).
% 3.24/1.53  tff(c_357, plain, (![A_68]: (k2_xboole_0(A_68, A_68)=A_68)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_338])).
% 3.24/1.53  tff(c_20, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.24/1.53  tff(c_36, plain, (![A_40, B_41]: (k5_xboole_0(k1_tarski(A_40), k1_tarski(B_41))=k2_tarski(A_40, B_41) | B_41=A_40)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.24/1.53  tff(c_221, plain, (![A_58, B_59]: (r1_xboole_0(k1_tarski(A_58), k1_tarski(B_59)) | B_59=A_58)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.24/1.53  tff(c_14, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=A_11 | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.24/1.53  tff(c_549, plain, (![A_81, B_82]: (k4_xboole_0(k1_tarski(A_81), k1_tarski(B_82))=k1_tarski(A_81) | B_82=A_81)), inference(resolution, [status(thm)], [c_221, c_14])).
% 3.24/1.53  tff(c_801, plain, (![B_100, A_101]: (k5_xboole_0(k1_tarski(B_100), k1_tarski(A_101))=k2_xboole_0(k1_tarski(B_100), k1_tarski(A_101)) | B_100=A_101)), inference(superposition, [status(thm), theory('equality')], [c_549, c_18])).
% 3.24/1.53  tff(c_1099, plain, (![A_116, B_117]: (k2_xboole_0(k1_tarski(A_116), k1_tarski(B_117))=k2_tarski(A_116, B_117) | B_117=A_116 | B_117=A_116)), inference(superposition, [status(thm), theory('equality')], [c_36, c_801])).
% 3.24/1.53  tff(c_32, plain, (![A_36, B_37]: (k3_tarski(k2_tarski(A_36, B_37))=k2_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.24/1.53  tff(c_38, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.24/1.53  tff(c_39, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_38])).
% 3.24/1.53  tff(c_1120, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1099, c_39])).
% 3.24/1.53  tff(c_1124, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))!=k2_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1120, c_1120, c_39])).
% 3.24/1.53  tff(c_1127, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_357, c_20, c_1124])).
% 3.24/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.53  
% 3.24/1.53  Inference rules
% 3.24/1.53  ----------------------
% 3.24/1.53  #Ref     : 0
% 3.24/1.53  #Sup     : 253
% 3.24/1.53  #Fact    : 0
% 3.24/1.53  #Define  : 0
% 3.24/1.53  #Split   : 0
% 3.24/1.53  #Chain   : 0
% 3.24/1.53  #Close   : 0
% 3.24/1.53  
% 3.24/1.53  Ordering : KBO
% 3.24/1.53  
% 3.24/1.53  Simplification rules
% 3.24/1.53  ----------------------
% 3.24/1.53  #Subsume      : 9
% 3.24/1.53  #Demod        : 215
% 3.24/1.53  #Tautology    : 185
% 3.24/1.53  #SimpNegUnit  : 0
% 3.24/1.53  #BackRed      : 2
% 3.24/1.53  
% 3.24/1.53  #Partial instantiations: 0
% 3.24/1.53  #Strategies tried      : 1
% 3.24/1.53  
% 3.24/1.53  Timing (in seconds)
% 3.24/1.53  ----------------------
% 3.24/1.54  Preprocessing        : 0.33
% 3.24/1.54  Parsing              : 0.18
% 3.24/1.54  CNF conversion       : 0.02
% 3.24/1.54  Main loop            : 0.38
% 3.24/1.54  Inferencing          : 0.14
% 3.24/1.54  Reduction            : 0.15
% 3.24/1.54  Demodulation         : 0.12
% 3.24/1.54  BG Simplification    : 0.02
% 3.24/1.54  Subsumption          : 0.05
% 3.24/1.54  Abstraction          : 0.02
% 3.24/1.54  MUC search           : 0.00
% 3.24/1.54  Cooper               : 0.00
% 3.24/1.54  Total                : 0.74
% 3.24/1.54  Index Insertion      : 0.00
% 3.24/1.54  Index Deletion       : 0.00
% 3.24/1.54  Index Matching       : 0.00
% 3.24/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
