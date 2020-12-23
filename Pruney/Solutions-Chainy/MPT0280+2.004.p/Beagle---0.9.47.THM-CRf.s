%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:24 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :   50 (  74 expanded)
%              Number of leaves         :   27 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   56 ( 107 expanded)
%              Number of equality atoms :    7 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(A),k1_zfmisc_1(B)),k1_zfmisc_1(k2_xboole_0(A,B))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_zfmisc_1)).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_10,C_12,B_11] :
      ( r1_tarski(A_10,k2_xboole_0(C_12,B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_32,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(k1_zfmisc_1(A_36),k1_zfmisc_1(B_37))
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    ! [A_16,B_17] : r1_tarski(A_16,k2_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_131,plain,(
    ! [A_58,C_59,B_60] :
      ( r1_tarski(k3_xboole_0(A_58,C_59),B_60)
      | ~ r1_tarski(A_58,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_136,plain,(
    ! [B_2,A_1,B_60] :
      ( r1_tarski(k3_xboole_0(B_2,A_1),B_60)
      | ~ r1_tarski(A_1,B_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_131])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_194,plain,(
    ! [A_71,C_72,B_73] :
      ( r1_tarski(k5_xboole_0(A_71,C_72),B_73)
      | ~ r1_tarski(C_72,B_73)
      | ~ r1_tarski(A_71,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_205,plain,(
    ! [A_5,B_6,B_73] :
      ( r1_tarski(k4_xboole_0(A_5,B_6),B_73)
      | ~ r1_tarski(k3_xboole_0(A_5,B_6),B_73)
      | ~ r1_tarski(A_5,B_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_194])).

tff(c_20,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_423,plain,(
    ! [A_107,B_108,B_109] :
      ( r1_tarski(k2_xboole_0(A_107,B_108),B_109)
      | ~ r1_tarski(k4_xboole_0(B_108,A_107),B_109)
      | ~ r1_tarski(A_107,B_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_194])).

tff(c_844,plain,(
    ! [B_153,A_154,B_155] :
      ( r1_tarski(k2_xboole_0(B_153,A_154),B_155)
      | ~ r1_tarski(B_153,B_155)
      | ~ r1_tarski(k3_xboole_0(A_154,B_153),B_155)
      | ~ r1_tarski(A_154,B_155) ) ),
    inference(resolution,[status(thm)],[c_205,c_423])).

tff(c_874,plain,(
    ! [A_156,B_157,B_158] :
      ( r1_tarski(k2_xboole_0(A_156,B_157),B_158)
      | ~ r1_tarski(B_157,B_158)
      | ~ r1_tarski(A_156,B_158) ) ),
    inference(resolution,[status(thm)],[c_136,c_844])).

tff(c_34,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1('#skF_1'),k1_zfmisc_1('#skF_2')),k1_zfmisc_1(k2_xboole_0('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_982,plain,
    ( ~ r1_tarski(k1_zfmisc_1('#skF_2'),k1_zfmisc_1(k2_xboole_0('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_zfmisc_1('#skF_1'),k1_zfmisc_1(k2_xboole_0('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_874,c_34])).

tff(c_1203,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_1'),k1_zfmisc_1(k2_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_982])).

tff(c_1206,plain,(
    ~ r1_tarski('#skF_1',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_1203])).

tff(c_1210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1206])).

tff(c_1211,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_2'),k1_zfmisc_1(k2_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_982])).

tff(c_1216,plain,(
    ~ r1_tarski('#skF_2',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_1211])).

tff(c_1219,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_1216])).

tff(c_1223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1219])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:47:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.59  
% 3.28/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.59  %$ r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.28/1.59  
% 3.28/1.59  %Foreground sorts:
% 3.28/1.59  
% 3.28/1.59  
% 3.28/1.59  %Background operators:
% 3.28/1.59  
% 3.28/1.59  
% 3.28/1.59  %Foreground operators:
% 3.28/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.28/1.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.28/1.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.28/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.28/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.28/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.28/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.28/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.28/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.28/1.59  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.28/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.28/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.59  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.28/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.28/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.28/1.59  
% 3.28/1.60  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.28/1.60  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.28/1.60  tff(f_67, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 3.28/1.60  tff(f_51, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.28/1.60  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.28/1.60  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 3.28/1.60  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.28/1.60  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_xboole_1)).
% 3.28/1.60  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.28/1.60  tff(f_70, negated_conjecture, ~(![A, B]: r1_tarski(k2_xboole_0(k1_zfmisc_1(A), k1_zfmisc_1(B)), k1_zfmisc_1(k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_zfmisc_1)).
% 3.28/1.60  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.28/1.60  tff(c_14, plain, (![A_10, C_12, B_11]: (r1_tarski(A_10, k2_xboole_0(C_12, B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.28/1.60  tff(c_32, plain, (![A_36, B_37]: (r1_tarski(k1_zfmisc_1(A_36), k1_zfmisc_1(B_37)) | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.28/1.60  tff(c_18, plain, (![A_16, B_17]: (r1_tarski(A_16, k2_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.28/1.60  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.28/1.60  tff(c_131, plain, (![A_58, C_59, B_60]: (r1_tarski(k3_xboole_0(A_58, C_59), B_60) | ~r1_tarski(A_58, B_60))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.28/1.60  tff(c_136, plain, (![B_2, A_1, B_60]: (r1_tarski(k3_xboole_0(B_2, A_1), B_60) | ~r1_tarski(A_1, B_60))), inference(superposition, [status(thm), theory('equality')], [c_2, c_131])).
% 3.28/1.60  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.28/1.60  tff(c_194, plain, (![A_71, C_72, B_73]: (r1_tarski(k5_xboole_0(A_71, C_72), B_73) | ~r1_tarski(C_72, B_73) | ~r1_tarski(A_71, B_73))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.28/1.60  tff(c_205, plain, (![A_5, B_6, B_73]: (r1_tarski(k4_xboole_0(A_5, B_6), B_73) | ~r1_tarski(k3_xboole_0(A_5, B_6), B_73) | ~r1_tarski(A_5, B_73))), inference(superposition, [status(thm), theory('equality')], [c_10, c_194])).
% 3.28/1.60  tff(c_20, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.28/1.60  tff(c_423, plain, (![A_107, B_108, B_109]: (r1_tarski(k2_xboole_0(A_107, B_108), B_109) | ~r1_tarski(k4_xboole_0(B_108, A_107), B_109) | ~r1_tarski(A_107, B_109))), inference(superposition, [status(thm), theory('equality')], [c_20, c_194])).
% 3.28/1.60  tff(c_844, plain, (![B_153, A_154, B_155]: (r1_tarski(k2_xboole_0(B_153, A_154), B_155) | ~r1_tarski(B_153, B_155) | ~r1_tarski(k3_xboole_0(A_154, B_153), B_155) | ~r1_tarski(A_154, B_155))), inference(resolution, [status(thm)], [c_205, c_423])).
% 3.28/1.60  tff(c_874, plain, (![A_156, B_157, B_158]: (r1_tarski(k2_xboole_0(A_156, B_157), B_158) | ~r1_tarski(B_157, B_158) | ~r1_tarski(A_156, B_158))), inference(resolution, [status(thm)], [c_136, c_844])).
% 3.28/1.60  tff(c_34, plain, (~r1_tarski(k2_xboole_0(k1_zfmisc_1('#skF_1'), k1_zfmisc_1('#skF_2')), k1_zfmisc_1(k2_xboole_0('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.28/1.60  tff(c_982, plain, (~r1_tarski(k1_zfmisc_1('#skF_2'), k1_zfmisc_1(k2_xboole_0('#skF_1', '#skF_2'))) | ~r1_tarski(k1_zfmisc_1('#skF_1'), k1_zfmisc_1(k2_xboole_0('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_874, c_34])).
% 3.28/1.60  tff(c_1203, plain, (~r1_tarski(k1_zfmisc_1('#skF_1'), k1_zfmisc_1(k2_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_982])).
% 3.28/1.60  tff(c_1206, plain, (~r1_tarski('#skF_1', k2_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_1203])).
% 3.28/1.60  tff(c_1210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_1206])).
% 3.28/1.60  tff(c_1211, plain, (~r1_tarski(k1_zfmisc_1('#skF_2'), k1_zfmisc_1(k2_xboole_0('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_982])).
% 3.28/1.60  tff(c_1216, plain, (~r1_tarski('#skF_2', k2_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_1211])).
% 3.28/1.60  tff(c_1219, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_14, c_1216])).
% 3.28/1.60  tff(c_1223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_1219])).
% 3.28/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.60  
% 3.28/1.60  Inference rules
% 3.28/1.60  ----------------------
% 3.28/1.60  #Ref     : 0
% 3.28/1.60  #Sup     : 268
% 3.28/1.60  #Fact    : 0
% 3.28/1.60  #Define  : 0
% 3.28/1.60  #Split   : 1
% 3.28/1.60  #Chain   : 0
% 3.28/1.60  #Close   : 0
% 3.28/1.60  
% 3.28/1.60  Ordering : KBO
% 3.28/1.60  
% 3.28/1.60  Simplification rules
% 3.28/1.60  ----------------------
% 3.28/1.60  #Subsume      : 28
% 3.28/1.60  #Demod        : 55
% 3.28/1.60  #Tautology    : 65
% 3.28/1.60  #SimpNegUnit  : 0
% 3.28/1.60  #BackRed      : 0
% 3.28/1.60  
% 3.28/1.60  #Partial instantiations: 0
% 3.28/1.60  #Strategies tried      : 1
% 3.28/1.60  
% 3.28/1.60  Timing (in seconds)
% 3.28/1.60  ----------------------
% 3.28/1.60  Preprocessing        : 0.34
% 3.28/1.61  Parsing              : 0.17
% 3.28/1.61  CNF conversion       : 0.02
% 3.28/1.61  Main loop            : 0.46
% 3.28/1.61  Inferencing          : 0.16
% 3.28/1.61  Reduction            : 0.13
% 3.28/1.61  Demodulation         : 0.10
% 3.28/1.61  BG Simplification    : 0.03
% 3.28/1.61  Subsumption          : 0.11
% 3.28/1.61  Abstraction          : 0.03
% 3.28/1.61  MUC search           : 0.00
% 3.28/1.61  Cooper               : 0.00
% 3.28/1.61  Total                : 0.83
% 3.28/1.61  Index Insertion      : 0.00
% 3.28/1.61  Index Deletion       : 0.00
% 3.28/1.61  Index Matching       : 0.00
% 3.28/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
