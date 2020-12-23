%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:52 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   67 (  81 expanded)
%              Number of leaves         :   32 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :   64 (  81 expanded)
%              Number of equality atoms :   37 (  51 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_49,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_69,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_44,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_12,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_66,plain,(
    ! [B_37,A_38] :
      ( r1_xboole_0(B_37,A_38)
      | ~ r1_xboole_0(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_69,plain,(
    ! [A_14] : r1_xboole_0(k1_xboole_0,A_14) ),
    inference(resolution,[status(thm)],[c_20,c_66])).

tff(c_186,plain,(
    ! [A_57,B_58] :
      ( k4_xboole_0(A_57,B_58) = A_57
      | ~ r1_xboole_0(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_197,plain,(
    ! [A_14] : k4_xboole_0(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_69,c_186])).

tff(c_26,plain,(
    ! [B_18,A_17] : k2_tarski(B_18,A_17) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_108,plain,(
    ! [A_42,B_43] : k3_tarski(k2_tarski(A_42,B_43)) = k2_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_246,plain,(
    ! [A_64,B_65] : k3_tarski(k2_tarski(A_64,B_65)) = k2_xboole_0(B_65,A_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_108])).

tff(c_40,plain,(
    ! [A_31,B_32] : k3_tarski(k2_tarski(A_31,B_32)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_273,plain,(
    ! [B_66,A_67] : k2_xboole_0(B_66,A_67) = k2_xboole_0(A_67,B_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_40])).

tff(c_289,plain,(
    ! [A_67] : k2_xboole_0(k1_xboole_0,A_67) = A_67 ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_12])).

tff(c_406,plain,(
    ! [A_75,B_76] : k4_xboole_0(k2_xboole_0(A_75,B_76),B_76) = k4_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_422,plain,(
    ! [A_67] : k4_xboole_0(k1_xboole_0,A_67) = k4_xboole_0(A_67,A_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_406])).

tff(c_446,plain,(
    ! [A_67] : k4_xboole_0(A_67,A_67) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_422])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_168,plain,(
    ! [A_54,B_55] :
      ( k3_xboole_0(A_54,B_55) = A_54
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_176,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_168])).

tff(c_199,plain,(
    ! [A_59,B_60] : k5_xboole_0(A_59,k3_xboole_0(A_59,B_60)) = k4_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_208,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_199])).

tff(c_449,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_446,c_208])).

tff(c_38,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(k1_tarski(A_29),B_30)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1041,plain,(
    ! [A_106,B_107] :
      ( k3_xboole_0(k1_tarski(A_106),B_107) = k1_tarski(A_106)
      | ~ r2_hidden(A_106,B_107) ) ),
    inference(resolution,[status(thm)],[c_38,c_168])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1047,plain,(
    ! [A_106,B_107] :
      ( k5_xboole_0(k1_tarski(A_106),k1_tarski(A_106)) = k4_xboole_0(k1_tarski(A_106),B_107)
      | ~ r2_hidden(A_106,B_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1041,c_10])).

tff(c_1068,plain,(
    ! [A_108,B_109] :
      ( k4_xboole_0(k1_tarski(A_108),B_109) = k1_xboole_0
      | ~ r2_hidden(A_108,B_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_449,c_1047])).

tff(c_16,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1101,plain,(
    ! [B_109,A_108] :
      ( k2_xboole_0(B_109,k1_tarski(A_108)) = k2_xboole_0(B_109,k1_xboole_0)
      | ~ r2_hidden(A_108,B_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1068,c_16])).

tff(c_1350,plain,(
    ! [B_115,A_116] :
      ( k2_xboole_0(B_115,k1_tarski(A_116)) = B_115
      | ~ r2_hidden(A_116,B_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1101])).

tff(c_252,plain,(
    ! [B_65,A_64] : k2_xboole_0(B_65,A_64) = k2_xboole_0(A_64,B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_40])).

tff(c_42,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_272,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_42])).

tff(c_1388,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1350,c_272])).

tff(c_1437,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1388])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:17:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.57  
% 3.02/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.57  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.02/1.57  
% 3.02/1.57  %Foreground sorts:
% 3.02/1.57  
% 3.02/1.57  
% 3.02/1.57  %Background operators:
% 3.02/1.57  
% 3.02/1.57  
% 3.02/1.57  %Foreground operators:
% 3.02/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.02/1.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.02/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.02/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.02/1.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.02/1.57  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.02/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.02/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.02/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.02/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.02/1.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.02/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.02/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.02/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.57  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.02/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.02/1.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.02/1.57  
% 3.02/1.58  tff(f_74, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 3.02/1.58  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.02/1.58  tff(f_49, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.02/1.58  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.02/1.58  tff(f_53, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.02/1.58  tff(f_55, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.02/1.58  tff(f_69, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.02/1.58  tff(f_47, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.02/1.58  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.02/1.58  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.02/1.58  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.02/1.58  tff(f_67, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.02/1.58  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.02/1.58  tff(c_44, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.02/1.58  tff(c_12, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.02/1.58  tff(c_20, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.02/1.58  tff(c_66, plain, (![B_37, A_38]: (r1_xboole_0(B_37, A_38) | ~r1_xboole_0(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.02/1.58  tff(c_69, plain, (![A_14]: (r1_xboole_0(k1_xboole_0, A_14))), inference(resolution, [status(thm)], [c_20, c_66])).
% 3.02/1.58  tff(c_186, plain, (![A_57, B_58]: (k4_xboole_0(A_57, B_58)=A_57 | ~r1_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.02/1.58  tff(c_197, plain, (![A_14]: (k4_xboole_0(k1_xboole_0, A_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_69, c_186])).
% 3.02/1.58  tff(c_26, plain, (![B_18, A_17]: (k2_tarski(B_18, A_17)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.02/1.58  tff(c_108, plain, (![A_42, B_43]: (k3_tarski(k2_tarski(A_42, B_43))=k2_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.02/1.58  tff(c_246, plain, (![A_64, B_65]: (k3_tarski(k2_tarski(A_64, B_65))=k2_xboole_0(B_65, A_64))), inference(superposition, [status(thm), theory('equality')], [c_26, c_108])).
% 3.02/1.58  tff(c_40, plain, (![A_31, B_32]: (k3_tarski(k2_tarski(A_31, B_32))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.02/1.58  tff(c_273, plain, (![B_66, A_67]: (k2_xboole_0(B_66, A_67)=k2_xboole_0(A_67, B_66))), inference(superposition, [status(thm), theory('equality')], [c_246, c_40])).
% 3.02/1.58  tff(c_289, plain, (![A_67]: (k2_xboole_0(k1_xboole_0, A_67)=A_67)), inference(superposition, [status(thm), theory('equality')], [c_273, c_12])).
% 3.02/1.58  tff(c_406, plain, (![A_75, B_76]: (k4_xboole_0(k2_xboole_0(A_75, B_76), B_76)=k4_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.02/1.58  tff(c_422, plain, (![A_67]: (k4_xboole_0(k1_xboole_0, A_67)=k4_xboole_0(A_67, A_67))), inference(superposition, [status(thm), theory('equality')], [c_289, c_406])).
% 3.02/1.58  tff(c_446, plain, (![A_67]: (k4_xboole_0(A_67, A_67)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_197, c_422])).
% 3.02/1.58  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.02/1.58  tff(c_168, plain, (![A_54, B_55]: (k3_xboole_0(A_54, B_55)=A_54 | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.02/1.58  tff(c_176, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_168])).
% 3.02/1.58  tff(c_199, plain, (![A_59, B_60]: (k5_xboole_0(A_59, k3_xboole_0(A_59, B_60))=k4_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.02/1.58  tff(c_208, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_176, c_199])).
% 3.02/1.58  tff(c_449, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_446, c_208])).
% 3.02/1.58  tff(c_38, plain, (![A_29, B_30]: (r1_tarski(k1_tarski(A_29), B_30) | ~r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.02/1.58  tff(c_1041, plain, (![A_106, B_107]: (k3_xboole_0(k1_tarski(A_106), B_107)=k1_tarski(A_106) | ~r2_hidden(A_106, B_107))), inference(resolution, [status(thm)], [c_38, c_168])).
% 3.02/1.58  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.02/1.58  tff(c_1047, plain, (![A_106, B_107]: (k5_xboole_0(k1_tarski(A_106), k1_tarski(A_106))=k4_xboole_0(k1_tarski(A_106), B_107) | ~r2_hidden(A_106, B_107))), inference(superposition, [status(thm), theory('equality')], [c_1041, c_10])).
% 3.02/1.58  tff(c_1068, plain, (![A_108, B_109]: (k4_xboole_0(k1_tarski(A_108), B_109)=k1_xboole_0 | ~r2_hidden(A_108, B_109))), inference(demodulation, [status(thm), theory('equality')], [c_449, c_1047])).
% 3.02/1.58  tff(c_16, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.02/1.58  tff(c_1101, plain, (![B_109, A_108]: (k2_xboole_0(B_109, k1_tarski(A_108))=k2_xboole_0(B_109, k1_xboole_0) | ~r2_hidden(A_108, B_109))), inference(superposition, [status(thm), theory('equality')], [c_1068, c_16])).
% 3.02/1.58  tff(c_1350, plain, (![B_115, A_116]: (k2_xboole_0(B_115, k1_tarski(A_116))=B_115 | ~r2_hidden(A_116, B_115))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1101])).
% 3.02/1.58  tff(c_252, plain, (![B_65, A_64]: (k2_xboole_0(B_65, A_64)=k2_xboole_0(A_64, B_65))), inference(superposition, [status(thm), theory('equality')], [c_246, c_40])).
% 3.02/1.58  tff(c_42, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.02/1.58  tff(c_272, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_252, c_42])).
% 3.02/1.58  tff(c_1388, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1350, c_272])).
% 3.02/1.58  tff(c_1437, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_1388])).
% 3.02/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.58  
% 3.02/1.58  Inference rules
% 3.02/1.58  ----------------------
% 3.02/1.58  #Ref     : 0
% 3.02/1.58  #Sup     : 332
% 3.02/1.58  #Fact    : 0
% 3.02/1.58  #Define  : 0
% 3.02/1.58  #Split   : 0
% 3.02/1.58  #Chain   : 0
% 3.02/1.58  #Close   : 0
% 3.02/1.58  
% 3.02/1.58  Ordering : KBO
% 3.02/1.58  
% 3.02/1.58  Simplification rules
% 3.02/1.58  ----------------------
% 3.02/1.58  #Subsume      : 13
% 3.02/1.58  #Demod        : 265
% 3.02/1.58  #Tautology    : 258
% 3.02/1.58  #SimpNegUnit  : 0
% 3.02/1.58  #BackRed      : 3
% 3.02/1.58  
% 3.02/1.58  #Partial instantiations: 0
% 3.02/1.58  #Strategies tried      : 1
% 3.02/1.58  
% 3.02/1.58  Timing (in seconds)
% 3.02/1.58  ----------------------
% 3.02/1.59  Preprocessing        : 0.36
% 3.02/1.59  Parsing              : 0.20
% 3.02/1.59  CNF conversion       : 0.02
% 3.02/1.59  Main loop            : 0.40
% 3.02/1.59  Inferencing          : 0.15
% 3.02/1.59  Reduction            : 0.15
% 3.02/1.59  Demodulation         : 0.12
% 3.02/1.59  BG Simplification    : 0.02
% 3.02/1.59  Subsumption          : 0.05
% 3.02/1.59  Abstraction          : 0.03
% 3.02/1.59  MUC search           : 0.00
% 3.02/1.59  Cooper               : 0.00
% 3.02/1.59  Total                : 0.79
% 3.02/1.59  Index Insertion      : 0.00
% 3.02/1.59  Index Deletion       : 0.00
% 3.02/1.59  Index Matching       : 0.00
% 3.02/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
