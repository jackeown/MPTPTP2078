%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:25 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   58 (  82 expanded)
%              Number of leaves         :   33 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :   61 ( 112 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_70,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(A),k1_zfmisc_1(B)),k1_zfmisc_1(k2_xboole_0(A,B))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_zfmisc_1)).

tff(c_16,plain,(
    ! [D_20,A_15] : r2_hidden(D_20,k2_tarski(A_15,D_20)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_46,plain,(
    ! [A_50,B_51] : k3_tarski(k2_tarski(A_50,B_51)) = k2_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_96,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(A_64,k3_tarski(B_65))
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_196,plain,(
    ! [A_88,A_89,B_90] :
      ( r1_tarski(A_88,k2_xboole_0(A_89,B_90))
      | ~ r2_hidden(A_88,k2_tarski(A_89,B_90)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_96])).

tff(c_203,plain,(
    ! [D_20,A_15] : r1_tarski(D_20,k2_xboole_0(A_15,D_20)) ),
    inference(resolution,[status(thm)],[c_16,c_196])).

tff(c_48,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(k1_zfmisc_1(A_52),k1_zfmisc_1(B_53))
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_125,plain,(
    ! [A_72,C_73,B_74] :
      ( r1_tarski(k3_xboole_0(A_72,C_73),B_74)
      | ~ r1_tarski(A_72,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_131,plain,(
    ! [A_1,B_2,B_74] :
      ( r1_tarski(k3_xboole_0(A_1,B_2),B_74)
      | ~ r1_tarski(B_2,B_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_125])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_216,plain,(
    ! [A_97,C_98,B_99] :
      ( r1_tarski(k5_xboole_0(A_97,C_98),B_99)
      | ~ r1_tarski(C_98,B_99)
      | ~ r1_tarski(A_97,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_251,plain,(
    ! [A_108,B_109,B_110] :
      ( r1_tarski(k4_xboole_0(A_108,B_109),B_110)
      | ~ r1_tarski(k3_xboole_0(A_108,B_109),B_110)
      | ~ r1_tarski(A_108,B_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_216])).

tff(c_12,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_222,plain,(
    ! [A_13,B_14,B_99] :
      ( r1_tarski(k2_xboole_0(A_13,B_14),B_99)
      | ~ r1_tarski(k4_xboole_0(B_14,A_13),B_99)
      | ~ r1_tarski(A_13,B_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_216])).

tff(c_278,plain,(
    ! [B_132,A_133,B_134] :
      ( r1_tarski(k2_xboole_0(B_132,A_133),B_134)
      | ~ r1_tarski(B_132,B_134)
      | ~ r1_tarski(k3_xboole_0(A_133,B_132),B_134)
      | ~ r1_tarski(A_133,B_134) ) ),
    inference(resolution,[status(thm)],[c_251,c_222])).

tff(c_308,plain,(
    ! [B_135,A_136,B_137] :
      ( r1_tarski(k2_xboole_0(B_135,A_136),B_137)
      | ~ r1_tarski(A_136,B_137)
      | ~ r1_tarski(B_135,B_137) ) ),
    inference(resolution,[status(thm)],[c_131,c_278])).

tff(c_50,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1('#skF_3'),k1_zfmisc_1('#skF_4')),k1_zfmisc_1(k2_xboole_0('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_312,plain,
    ( ~ r1_tarski(k1_zfmisc_1('#skF_4'),k1_zfmisc_1(k2_xboole_0('#skF_3','#skF_4')))
    | ~ r1_tarski(k1_zfmisc_1('#skF_3'),k1_zfmisc_1(k2_xboole_0('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_308,c_50])).

tff(c_313,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_3'),k1_zfmisc_1(k2_xboole_0('#skF_3','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_312])).

tff(c_325,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_313])).

tff(c_329,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_325])).

tff(c_330,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_4'),k1_zfmisc_1(k2_xboole_0('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_312])).

tff(c_334,plain,(
    ~ r1_tarski('#skF_4',k2_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_330])).

tff(c_338,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_334])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:31:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.34  
% 2.49/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.34  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.49/1.34  
% 2.49/1.34  %Foreground sorts:
% 2.49/1.34  
% 2.49/1.34  
% 2.49/1.34  %Background operators:
% 2.49/1.34  
% 2.49/1.34  
% 2.49/1.34  %Foreground operators:
% 2.49/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.49/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.49/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.49/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.49/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.49/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.49/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.49/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.49/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.49/1.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.49/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.49/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.49/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.49/1.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.34  
% 2.49/1.36  tff(f_52, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.49/1.36  tff(f_70, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.49/1.36  tff(f_68, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.49/1.36  tff(f_74, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.49/1.36  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.49/1.36  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.49/1.36  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 2.49/1.36  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.49/1.36  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_xboole_1)).
% 2.49/1.36  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.49/1.36  tff(f_77, negated_conjecture, ~(![A, B]: r1_tarski(k2_xboole_0(k1_zfmisc_1(A), k1_zfmisc_1(B)), k1_zfmisc_1(k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_zfmisc_1)).
% 2.49/1.36  tff(c_16, plain, (![D_20, A_15]: (r2_hidden(D_20, k2_tarski(A_15, D_20)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.49/1.36  tff(c_46, plain, (![A_50, B_51]: (k3_tarski(k2_tarski(A_50, B_51))=k2_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.49/1.36  tff(c_96, plain, (![A_64, B_65]: (r1_tarski(A_64, k3_tarski(B_65)) | ~r2_hidden(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.49/1.36  tff(c_196, plain, (![A_88, A_89, B_90]: (r1_tarski(A_88, k2_xboole_0(A_89, B_90)) | ~r2_hidden(A_88, k2_tarski(A_89, B_90)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_96])).
% 2.49/1.36  tff(c_203, plain, (![D_20, A_15]: (r1_tarski(D_20, k2_xboole_0(A_15, D_20)))), inference(resolution, [status(thm)], [c_16, c_196])).
% 2.49/1.36  tff(c_48, plain, (![A_52, B_53]: (r1_tarski(k1_zfmisc_1(A_52), k1_zfmisc_1(B_53)) | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.49/1.36  tff(c_10, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.49/1.36  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.49/1.36  tff(c_125, plain, (![A_72, C_73, B_74]: (r1_tarski(k3_xboole_0(A_72, C_73), B_74) | ~r1_tarski(A_72, B_74))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.49/1.36  tff(c_131, plain, (![A_1, B_2, B_74]: (r1_tarski(k3_xboole_0(A_1, B_2), B_74) | ~r1_tarski(B_2, B_74))), inference(superposition, [status(thm), theory('equality')], [c_2, c_125])).
% 2.49/1.36  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.49/1.36  tff(c_216, plain, (![A_97, C_98, B_99]: (r1_tarski(k5_xboole_0(A_97, C_98), B_99) | ~r1_tarski(C_98, B_99) | ~r1_tarski(A_97, B_99))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.49/1.36  tff(c_251, plain, (![A_108, B_109, B_110]: (r1_tarski(k4_xboole_0(A_108, B_109), B_110) | ~r1_tarski(k3_xboole_0(A_108, B_109), B_110) | ~r1_tarski(A_108, B_110))), inference(superposition, [status(thm), theory('equality')], [c_4, c_216])).
% 2.49/1.36  tff(c_12, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.49/1.36  tff(c_222, plain, (![A_13, B_14, B_99]: (r1_tarski(k2_xboole_0(A_13, B_14), B_99) | ~r1_tarski(k4_xboole_0(B_14, A_13), B_99) | ~r1_tarski(A_13, B_99))), inference(superposition, [status(thm), theory('equality')], [c_12, c_216])).
% 2.49/1.36  tff(c_278, plain, (![B_132, A_133, B_134]: (r1_tarski(k2_xboole_0(B_132, A_133), B_134) | ~r1_tarski(B_132, B_134) | ~r1_tarski(k3_xboole_0(A_133, B_132), B_134) | ~r1_tarski(A_133, B_134))), inference(resolution, [status(thm)], [c_251, c_222])).
% 2.49/1.36  tff(c_308, plain, (![B_135, A_136, B_137]: (r1_tarski(k2_xboole_0(B_135, A_136), B_137) | ~r1_tarski(A_136, B_137) | ~r1_tarski(B_135, B_137))), inference(resolution, [status(thm)], [c_131, c_278])).
% 2.49/1.36  tff(c_50, plain, (~r1_tarski(k2_xboole_0(k1_zfmisc_1('#skF_3'), k1_zfmisc_1('#skF_4')), k1_zfmisc_1(k2_xboole_0('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.49/1.36  tff(c_312, plain, (~r1_tarski(k1_zfmisc_1('#skF_4'), k1_zfmisc_1(k2_xboole_0('#skF_3', '#skF_4'))) | ~r1_tarski(k1_zfmisc_1('#skF_3'), k1_zfmisc_1(k2_xboole_0('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_308, c_50])).
% 2.49/1.36  tff(c_313, plain, (~r1_tarski(k1_zfmisc_1('#skF_3'), k1_zfmisc_1(k2_xboole_0('#skF_3', '#skF_4')))), inference(splitLeft, [status(thm)], [c_312])).
% 2.49/1.36  tff(c_325, plain, (~r1_tarski('#skF_3', k2_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_313])).
% 2.49/1.36  tff(c_329, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_325])).
% 2.49/1.36  tff(c_330, plain, (~r1_tarski(k1_zfmisc_1('#skF_4'), k1_zfmisc_1(k2_xboole_0('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_312])).
% 2.49/1.36  tff(c_334, plain, (~r1_tarski('#skF_4', k2_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_330])).
% 2.49/1.36  tff(c_338, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_203, c_334])).
% 2.49/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.36  
% 2.49/1.36  Inference rules
% 2.49/1.36  ----------------------
% 2.49/1.36  #Ref     : 0
% 2.49/1.36  #Sup     : 62
% 2.49/1.36  #Fact    : 0
% 2.49/1.36  #Define  : 0
% 2.49/1.36  #Split   : 1
% 2.49/1.36  #Chain   : 0
% 2.49/1.36  #Close   : 0
% 2.49/1.36  
% 2.49/1.36  Ordering : KBO
% 2.49/1.36  
% 2.49/1.36  Simplification rules
% 2.49/1.36  ----------------------
% 2.49/1.36  #Subsume      : 5
% 2.49/1.36  #Demod        : 7
% 2.49/1.36  #Tautology    : 36
% 2.49/1.36  #SimpNegUnit  : 0
% 2.49/1.36  #BackRed      : 0
% 2.49/1.36  
% 2.49/1.36  #Partial instantiations: 0
% 2.49/1.36  #Strategies tried      : 1
% 2.49/1.36  
% 2.49/1.36  Timing (in seconds)
% 2.49/1.36  ----------------------
% 2.63/1.36  Preprocessing        : 0.35
% 2.63/1.36  Parsing              : 0.18
% 2.63/1.36  CNF conversion       : 0.02
% 2.63/1.36  Main loop            : 0.24
% 2.63/1.36  Inferencing          : 0.09
% 2.63/1.36  Reduction            : 0.07
% 2.63/1.36  Demodulation         : 0.06
% 2.63/1.36  BG Simplification    : 0.02
% 2.63/1.36  Subsumption          : 0.04
% 2.63/1.36  Abstraction          : 0.02
% 2.63/1.36  MUC search           : 0.00
% 2.63/1.36  Cooper               : 0.00
% 2.63/1.36  Total                : 0.62
% 2.63/1.36  Index Insertion      : 0.00
% 2.63/1.37  Index Deletion       : 0.00
% 2.63/1.37  Index Matching       : 0.00
% 2.63/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
