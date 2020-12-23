%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:28 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   50 (  78 expanded)
%              Number of leaves         :   25 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 ( 109 expanded)
%              Number of equality atoms :   10 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A,B)),k1_zfmisc_1(k4_xboole_0(B,A))),k1_zfmisc_1(k5_xboole_0(A,B))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_zfmisc_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_188,plain,(
    ! [A_55,B_56] : k2_xboole_0(k4_xboole_0(A_55,B_56),k4_xboole_0(B_56,A_55)) = k5_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_200,plain,(
    ! [A_57,B_58] : r1_tarski(k4_xboole_0(A_57,B_58),k5_xboole_0(A_57,B_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_14])).

tff(c_212,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),k5_xboole_0(B_4,A_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_200])).

tff(c_24,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(k1_zfmisc_1(A_26),k1_zfmisc_1(B_27))
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_194,plain,(
    ! [A_55,B_56] : r1_tarski(k4_xboole_0(A_55,B_56),k5_xboole_0(A_55,B_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_14])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_112,plain,(
    ! [A_38,C_39,B_40] :
      ( r1_tarski(k3_xboole_0(A_38,C_39),B_40)
      | ~ r1_tarski(A_38,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_115,plain,(
    ! [B_2,A_1,B_40] :
      ( r1_tarski(k3_xboole_0(B_2,A_1),B_40)
      | ~ r1_tarski(A_1,B_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_112])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_235,plain,(
    ! [A_61,C_62,B_63] :
      ( r1_tarski(k5_xboole_0(A_61,C_62),B_63)
      | ~ r1_tarski(C_62,B_63)
      | ~ r1_tarski(A_61,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_241,plain,(
    ! [A_7,B_8,B_63] :
      ( r1_tarski(k4_xboole_0(A_7,B_8),B_63)
      | ~ r1_tarski(k3_xboole_0(A_7,B_8),B_63)
      | ~ r1_tarski(A_7,B_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_235])).

tff(c_16,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_296,plain,(
    ! [A_79,B_80,B_81] :
      ( r1_tarski(k2_xboole_0(A_79,B_80),B_81)
      | ~ r1_tarski(k4_xboole_0(B_80,A_79),B_81)
      | ~ r1_tarski(A_79,B_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_235])).

tff(c_453,plain,(
    ! [B_99,A_100,B_101] :
      ( r1_tarski(k2_xboole_0(B_99,A_100),B_101)
      | ~ r1_tarski(B_99,B_101)
      | ~ r1_tarski(k3_xboole_0(A_100,B_99),B_101)
      | ~ r1_tarski(A_100,B_101) ) ),
    inference(resolution,[status(thm)],[c_241,c_296])).

tff(c_473,plain,(
    ! [A_102,B_103,B_104] :
      ( r1_tarski(k2_xboole_0(A_102,B_103),B_104)
      | ~ r1_tarski(B_103,B_104)
      | ~ r1_tarski(A_102,B_104) ) ),
    inference(resolution,[status(thm)],[c_115,c_453])).

tff(c_26,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1'))),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_480,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_473,c_26])).

tff(c_481,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_480])).

tff(c_484,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_481])).

tff(c_488,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_484])).

tff(c_489,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_480])).

tff(c_493,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_2','#skF_1'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_489])).

tff(c_497,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_493])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:16:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.36  
% 2.42/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.36  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.42/1.36  
% 2.42/1.36  %Foreground sorts:
% 2.42/1.36  
% 2.42/1.36  
% 2.42/1.36  %Background operators:
% 2.42/1.36  
% 2.42/1.36  
% 2.42/1.36  %Foreground operators:
% 2.42/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.42/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.42/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.42/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.42/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.42/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.42/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.42/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.42/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.42/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.42/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.42/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.42/1.36  
% 2.42/1.37  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 2.42/1.37  tff(f_31, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 2.42/1.37  tff(f_45, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.42/1.37  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.42/1.37  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.42/1.37  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 2.42/1.37  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.42/1.37  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_xboole_1)).
% 2.42/1.37  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.42/1.37  tff(f_60, negated_conjecture, ~(![A, B]: r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A, B)), k1_zfmisc_1(k4_xboole_0(B, A))), k1_zfmisc_1(k5_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_zfmisc_1)).
% 2.42/1.37  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.42/1.37  tff(c_188, plain, (![A_55, B_56]: (k2_xboole_0(k4_xboole_0(A_55, B_56), k4_xboole_0(B_56, A_55))=k5_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.42/1.37  tff(c_14, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.42/1.37  tff(c_200, plain, (![A_57, B_58]: (r1_tarski(k4_xboole_0(A_57, B_58), k5_xboole_0(A_57, B_58)))), inference(superposition, [status(thm), theory('equality')], [c_188, c_14])).
% 2.42/1.37  tff(c_212, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), k5_xboole_0(B_4, A_3)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_200])).
% 2.42/1.37  tff(c_24, plain, (![A_26, B_27]: (r1_tarski(k1_zfmisc_1(A_26), k1_zfmisc_1(B_27)) | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.42/1.37  tff(c_194, plain, (![A_55, B_56]: (r1_tarski(k4_xboole_0(A_55, B_56), k5_xboole_0(A_55, B_56)))), inference(superposition, [status(thm), theory('equality')], [c_188, c_14])).
% 2.42/1.37  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.42/1.37  tff(c_112, plain, (![A_38, C_39, B_40]: (r1_tarski(k3_xboole_0(A_38, C_39), B_40) | ~r1_tarski(A_38, B_40))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.42/1.37  tff(c_115, plain, (![B_2, A_1, B_40]: (r1_tarski(k3_xboole_0(B_2, A_1), B_40) | ~r1_tarski(A_1, B_40))), inference(superposition, [status(thm), theory('equality')], [c_2, c_112])).
% 2.42/1.37  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.42/1.37  tff(c_235, plain, (![A_61, C_62, B_63]: (r1_tarski(k5_xboole_0(A_61, C_62), B_63) | ~r1_tarski(C_62, B_63) | ~r1_tarski(A_61, B_63))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.42/1.37  tff(c_241, plain, (![A_7, B_8, B_63]: (r1_tarski(k4_xboole_0(A_7, B_8), B_63) | ~r1_tarski(k3_xboole_0(A_7, B_8), B_63) | ~r1_tarski(A_7, B_63))), inference(superposition, [status(thm), theory('equality')], [c_8, c_235])).
% 2.42/1.37  tff(c_16, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.42/1.37  tff(c_296, plain, (![A_79, B_80, B_81]: (r1_tarski(k2_xboole_0(A_79, B_80), B_81) | ~r1_tarski(k4_xboole_0(B_80, A_79), B_81) | ~r1_tarski(A_79, B_81))), inference(superposition, [status(thm), theory('equality')], [c_16, c_235])).
% 2.42/1.37  tff(c_453, plain, (![B_99, A_100, B_101]: (r1_tarski(k2_xboole_0(B_99, A_100), B_101) | ~r1_tarski(B_99, B_101) | ~r1_tarski(k3_xboole_0(A_100, B_99), B_101) | ~r1_tarski(A_100, B_101))), inference(resolution, [status(thm)], [c_241, c_296])).
% 2.42/1.37  tff(c_473, plain, (![A_102, B_103, B_104]: (r1_tarski(k2_xboole_0(A_102, B_103), B_104) | ~r1_tarski(B_103, B_104) | ~r1_tarski(A_102, B_104))), inference(resolution, [status(thm)], [c_115, c_453])).
% 2.42/1.37  tff(c_26, plain, (~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1'))), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.42/1.37  tff(c_480, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2'))) | ~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_473, c_26])).
% 2.42/1.37  tff(c_481, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_480])).
% 2.42/1.37  tff(c_484, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_481])).
% 2.42/1.37  tff(c_488, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_194, c_484])).
% 2.42/1.37  tff(c_489, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_480])).
% 2.42/1.37  tff(c_493, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_1'), k5_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_489])).
% 2.42/1.37  tff(c_497, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_212, c_493])).
% 2.42/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.37  
% 2.42/1.37  Inference rules
% 2.42/1.37  ----------------------
% 2.42/1.37  #Ref     : 0
% 2.42/1.37  #Sup     : 115
% 2.42/1.37  #Fact    : 0
% 2.42/1.37  #Define  : 0
% 2.42/1.37  #Split   : 1
% 2.42/1.37  #Chain   : 0
% 2.42/1.37  #Close   : 0
% 2.42/1.37  
% 2.42/1.37  Ordering : KBO
% 2.42/1.37  
% 2.42/1.37  Simplification rules
% 2.42/1.37  ----------------------
% 2.42/1.37  #Subsume      : 19
% 2.42/1.37  #Demod        : 39
% 2.42/1.37  #Tautology    : 48
% 2.42/1.37  #SimpNegUnit  : 0
% 2.42/1.37  #BackRed      : 0
% 2.42/1.37  
% 2.42/1.37  #Partial instantiations: 0
% 2.42/1.37  #Strategies tried      : 1
% 2.42/1.37  
% 2.42/1.37  Timing (in seconds)
% 2.42/1.37  ----------------------
% 2.42/1.37  Preprocessing        : 0.30
% 2.42/1.37  Parsing              : 0.16
% 2.42/1.37  CNF conversion       : 0.02
% 2.42/1.37  Main loop            : 0.27
% 2.42/1.37  Inferencing          : 0.10
% 2.42/1.37  Reduction            : 0.10
% 2.42/1.37  Demodulation         : 0.08
% 2.42/1.37  BG Simplification    : 0.01
% 2.42/1.37  Subsumption          : 0.04
% 2.42/1.37  Abstraction          : 0.01
% 2.42/1.37  MUC search           : 0.00
% 2.42/1.37  Cooper               : 0.00
% 2.42/1.37  Total                : 0.60
% 2.42/1.37  Index Insertion      : 0.00
% 2.42/1.37  Index Deletion       : 0.00
% 2.42/1.38  Index Matching       : 0.00
% 2.42/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
