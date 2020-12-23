%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:51 EST 2020

% Result     : Theorem 4.33s
% Output     : CNFRefutation 4.47s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 101 expanded)
%              Number of leaves         :   31 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :   59 (  97 expanded)
%              Number of equality atoms :   41 (  76 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_65,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_79,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_60,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_28,plain,(
    ! [A_13] : k2_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_42,plain,(
    ! [B_27,A_26] : k2_tarski(B_27,A_26) = k2_tarski(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_143,plain,(
    ! [A_53,B_54] : k3_tarski(k2_tarski(A_53,B_54)) = k2_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_320,plain,(
    ! [B_72,A_73] : k3_tarski(k2_tarski(B_72,A_73)) = k2_xboole_0(A_73,B_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_143])).

tff(c_56,plain,(
    ! [A_40,B_41] : k3_tarski(k2_tarski(A_40,B_41)) = k2_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_370,plain,(
    ! [B_76,A_77] : k2_xboole_0(B_76,A_77) = k2_xboole_0(A_77,B_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_56])).

tff(c_406,plain,(
    ! [A_77] : k2_xboole_0(k1_xboole_0,A_77) = A_77 ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_28])).

tff(c_437,plain,(
    ! [A_78] : k2_xboole_0(k1_xboole_0,A_78) = A_78 ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_28])).

tff(c_30,plain,(
    ! [A_14,B_15] : k2_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_461,plain,(
    ! [B_15] : k3_xboole_0(k1_xboole_0,B_15) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_30])).

tff(c_564,plain,(
    ! [A_84,B_85] : k4_xboole_0(k2_xboole_0(A_84,B_85),B_85) = k4_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_903,plain,(
    ! [A_104] : k4_xboole_0(k1_xboole_0,A_104) = k4_xboole_0(A_104,A_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_564])).

tff(c_38,plain,(
    ! [A_22,B_23] : k2_xboole_0(k3_xboole_0(A_22,B_23),k4_xboole_0(A_22,B_23)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_924,plain,(
    ! [A_104] : k2_xboole_0(k3_xboole_0(k1_xboole_0,A_104),k4_xboole_0(A_104,A_104)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_903,c_38])).

tff(c_940,plain,(
    ! [A_104] : k4_xboole_0(A_104,A_104) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_461,c_924])).

tff(c_24,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_214,plain,(
    ! [A_63,B_64] :
      ( k3_xboole_0(A_63,B_64) = A_63
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_230,plain,(
    ! [B_10] : k3_xboole_0(B_10,B_10) = B_10 ),
    inference(resolution,[status(thm)],[c_24,c_214])).

tff(c_666,plain,(
    ! [A_90,B_91] : k5_xboole_0(A_90,k3_xboole_0(A_90,B_91)) = k4_xboole_0(A_90,B_91) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_681,plain,(
    ! [B_10] : k5_xboole_0(B_10,B_10) = k4_xboole_0(B_10,B_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_666])).

tff(c_947,plain,(
    ! [B_10] : k5_xboole_0(B_10,B_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_940,c_681])).

tff(c_54,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(k1_tarski(A_38),B_39)
      | ~ r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4785,plain,(
    ! [A_209,B_210] :
      ( k3_xboole_0(k1_tarski(A_209),B_210) = k1_tarski(A_209)
      | ~ r2_hidden(A_209,B_210) ) ),
    inference(resolution,[status(thm)],[c_54,c_214])).

tff(c_26,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4810,plain,(
    ! [A_209,B_210] :
      ( k5_xboole_0(k1_tarski(A_209),k1_tarski(A_209)) = k4_xboole_0(k1_tarski(A_209),B_210)
      | ~ r2_hidden(A_209,B_210) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4785,c_26])).

tff(c_4867,plain,(
    ! [A_211,B_212] :
      ( k4_xboole_0(k1_tarski(A_211),B_212) = k1_xboole_0
      | ~ r2_hidden(A_211,B_212) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_947,c_4810])).

tff(c_34,plain,(
    ! [A_18,B_19] : k2_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4925,plain,(
    ! [B_212,A_211] :
      ( k2_xboole_0(B_212,k1_tarski(A_211)) = k2_xboole_0(B_212,k1_xboole_0)
      | ~ r2_hidden(A_211,B_212) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4867,c_34])).

tff(c_4977,plain,(
    ! [B_213,A_214] :
      ( k2_xboole_0(B_213,k1_tarski(A_214)) = B_213
      | ~ r2_hidden(A_214,B_213) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_4925])).

tff(c_326,plain,(
    ! [B_72,A_73] : k2_xboole_0(B_72,A_73) = k2_xboole_0(A_73,B_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_56])).

tff(c_58,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),'#skF_3') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_369,plain,(
    k2_xboole_0('#skF_3',k1_tarski('#skF_2')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_58])).

tff(c_5085,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4977,c_369])).

tff(c_5183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_5085])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:55:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.33/1.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.33/1.80  
% 4.33/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.33/1.81  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.33/1.81  
% 4.33/1.81  %Foreground sorts:
% 4.33/1.81  
% 4.33/1.81  
% 4.33/1.81  %Background operators:
% 4.33/1.81  
% 4.33/1.81  
% 4.33/1.81  %Foreground operators:
% 4.33/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.33/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.33/1.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.33/1.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.33/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.33/1.81  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.33/1.81  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.33/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.33/1.81  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.33/1.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.33/1.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.33/1.81  tff('#skF_2', type, '#skF_2': $i).
% 4.33/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.33/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.33/1.81  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.33/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.33/1.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.33/1.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.33/1.81  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.33/1.81  
% 4.47/1.82  tff(f_84, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 4.47/1.82  tff(f_49, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.47/1.82  tff(f_65, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.47/1.82  tff(f_79, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.47/1.82  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 4.47/1.82  tff(f_59, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 4.47/1.82  tff(f_61, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 4.47/1.82  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.47/1.82  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.47/1.82  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.47/1.82  tff(f_77, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.47/1.82  tff(f_57, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.47/1.82  tff(c_60, plain, (r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.47/1.82  tff(c_28, plain, (![A_13]: (k2_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.47/1.82  tff(c_42, plain, (![B_27, A_26]: (k2_tarski(B_27, A_26)=k2_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.47/1.82  tff(c_143, plain, (![A_53, B_54]: (k3_tarski(k2_tarski(A_53, B_54))=k2_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.47/1.82  tff(c_320, plain, (![B_72, A_73]: (k3_tarski(k2_tarski(B_72, A_73))=k2_xboole_0(A_73, B_72))), inference(superposition, [status(thm), theory('equality')], [c_42, c_143])).
% 4.47/1.82  tff(c_56, plain, (![A_40, B_41]: (k3_tarski(k2_tarski(A_40, B_41))=k2_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.47/1.82  tff(c_370, plain, (![B_76, A_77]: (k2_xboole_0(B_76, A_77)=k2_xboole_0(A_77, B_76))), inference(superposition, [status(thm), theory('equality')], [c_320, c_56])).
% 4.47/1.82  tff(c_406, plain, (![A_77]: (k2_xboole_0(k1_xboole_0, A_77)=A_77)), inference(superposition, [status(thm), theory('equality')], [c_370, c_28])).
% 4.47/1.82  tff(c_437, plain, (![A_78]: (k2_xboole_0(k1_xboole_0, A_78)=A_78)), inference(superposition, [status(thm), theory('equality')], [c_370, c_28])).
% 4.47/1.82  tff(c_30, plain, (![A_14, B_15]: (k2_xboole_0(A_14, k3_xboole_0(A_14, B_15))=A_14)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.47/1.82  tff(c_461, plain, (![B_15]: (k3_xboole_0(k1_xboole_0, B_15)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_437, c_30])).
% 4.47/1.82  tff(c_564, plain, (![A_84, B_85]: (k4_xboole_0(k2_xboole_0(A_84, B_85), B_85)=k4_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.47/1.82  tff(c_903, plain, (![A_104]: (k4_xboole_0(k1_xboole_0, A_104)=k4_xboole_0(A_104, A_104))), inference(superposition, [status(thm), theory('equality')], [c_406, c_564])).
% 4.47/1.82  tff(c_38, plain, (![A_22, B_23]: (k2_xboole_0(k3_xboole_0(A_22, B_23), k4_xboole_0(A_22, B_23))=A_22)), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.47/1.82  tff(c_924, plain, (![A_104]: (k2_xboole_0(k3_xboole_0(k1_xboole_0, A_104), k4_xboole_0(A_104, A_104))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_903, c_38])).
% 4.47/1.82  tff(c_940, plain, (![A_104]: (k4_xboole_0(A_104, A_104)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_406, c_461, c_924])).
% 4.47/1.82  tff(c_24, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.47/1.82  tff(c_214, plain, (![A_63, B_64]: (k3_xboole_0(A_63, B_64)=A_63 | ~r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.47/1.82  tff(c_230, plain, (![B_10]: (k3_xboole_0(B_10, B_10)=B_10)), inference(resolution, [status(thm)], [c_24, c_214])).
% 4.47/1.82  tff(c_666, plain, (![A_90, B_91]: (k5_xboole_0(A_90, k3_xboole_0(A_90, B_91))=k4_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.47/1.82  tff(c_681, plain, (![B_10]: (k5_xboole_0(B_10, B_10)=k4_xboole_0(B_10, B_10))), inference(superposition, [status(thm), theory('equality')], [c_230, c_666])).
% 4.47/1.82  tff(c_947, plain, (![B_10]: (k5_xboole_0(B_10, B_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_940, c_681])).
% 4.47/1.82  tff(c_54, plain, (![A_38, B_39]: (r1_tarski(k1_tarski(A_38), B_39) | ~r2_hidden(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.47/1.82  tff(c_4785, plain, (![A_209, B_210]: (k3_xboole_0(k1_tarski(A_209), B_210)=k1_tarski(A_209) | ~r2_hidden(A_209, B_210))), inference(resolution, [status(thm)], [c_54, c_214])).
% 4.47/1.82  tff(c_26, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.47/1.82  tff(c_4810, plain, (![A_209, B_210]: (k5_xboole_0(k1_tarski(A_209), k1_tarski(A_209))=k4_xboole_0(k1_tarski(A_209), B_210) | ~r2_hidden(A_209, B_210))), inference(superposition, [status(thm), theory('equality')], [c_4785, c_26])).
% 4.47/1.82  tff(c_4867, plain, (![A_211, B_212]: (k4_xboole_0(k1_tarski(A_211), B_212)=k1_xboole_0 | ~r2_hidden(A_211, B_212))), inference(demodulation, [status(thm), theory('equality')], [c_947, c_4810])).
% 4.47/1.82  tff(c_34, plain, (![A_18, B_19]: (k2_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.47/1.82  tff(c_4925, plain, (![B_212, A_211]: (k2_xboole_0(B_212, k1_tarski(A_211))=k2_xboole_0(B_212, k1_xboole_0) | ~r2_hidden(A_211, B_212))), inference(superposition, [status(thm), theory('equality')], [c_4867, c_34])).
% 4.47/1.82  tff(c_4977, plain, (![B_213, A_214]: (k2_xboole_0(B_213, k1_tarski(A_214))=B_213 | ~r2_hidden(A_214, B_213))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_4925])).
% 4.47/1.82  tff(c_326, plain, (![B_72, A_73]: (k2_xboole_0(B_72, A_73)=k2_xboole_0(A_73, B_72))), inference(superposition, [status(thm), theory('equality')], [c_320, c_56])).
% 4.47/1.82  tff(c_58, plain, (k2_xboole_0(k1_tarski('#skF_2'), '#skF_3')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.47/1.82  tff(c_369, plain, (k2_xboole_0('#skF_3', k1_tarski('#skF_2'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_326, c_58])).
% 4.47/1.82  tff(c_5085, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4977, c_369])).
% 4.47/1.82  tff(c_5183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_5085])).
% 4.47/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.47/1.82  
% 4.47/1.82  Inference rules
% 4.47/1.82  ----------------------
% 4.47/1.82  #Ref     : 0
% 4.47/1.82  #Sup     : 1254
% 4.47/1.82  #Fact    : 0
% 4.47/1.82  #Define  : 0
% 4.47/1.82  #Split   : 1
% 4.47/1.82  #Chain   : 0
% 4.47/1.82  #Close   : 0
% 4.47/1.82  
% 4.47/1.82  Ordering : KBO
% 4.47/1.82  
% 4.47/1.82  Simplification rules
% 4.47/1.82  ----------------------
% 4.47/1.82  #Subsume      : 115
% 4.47/1.82  #Demod        : 1296
% 4.47/1.82  #Tautology    : 935
% 4.47/1.82  #SimpNegUnit  : 0
% 4.47/1.82  #BackRed      : 9
% 4.47/1.82  
% 4.47/1.82  #Partial instantiations: 0
% 4.47/1.82  #Strategies tried      : 1
% 4.47/1.82  
% 4.47/1.82  Timing (in seconds)
% 4.47/1.82  ----------------------
% 4.47/1.82  Preprocessing        : 0.31
% 4.47/1.82  Parsing              : 0.17
% 4.47/1.82  CNF conversion       : 0.02
% 4.47/1.82  Main loop            : 0.74
% 4.47/1.82  Inferencing          : 0.25
% 4.47/1.82  Reduction            : 0.32
% 4.47/1.82  Demodulation         : 0.26
% 4.47/1.82  BG Simplification    : 0.03
% 4.47/1.82  Subsumption          : 0.11
% 4.47/1.82  Abstraction          : 0.04
% 4.47/1.82  MUC search           : 0.00
% 4.47/1.82  Cooper               : 0.00
% 4.47/1.82  Total                : 1.09
% 4.47/1.82  Index Insertion      : 0.00
% 4.47/1.82  Index Deletion       : 0.00
% 4.47/1.82  Index Matching       : 0.00
% 4.47/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
