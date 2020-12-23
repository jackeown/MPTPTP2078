%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:26 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 111 expanded)
%              Number of leaves         :   22 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :   86 ( 221 expanded)
%              Number of equality atoms :   53 ( 131 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_55,negated_conjecture,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_50,plain,(
    ! [A_28] :
      ( k1_xboole_0 = A_28
      | ~ r1_tarski(A_28,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    ! [B_31] : k3_xboole_0(k1_xboole_0,B_31) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_50])).

tff(c_67,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_2])).

tff(c_28,plain,(
    ! [C_23,A_19] :
      ( r2_hidden(C_23,k1_zfmisc_1(A_19))
      | ~ r1_tarski(C_23,A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_38,plain,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_117,plain,(
    ! [A_49,B_50] :
      ( '#skF_1'(A_49,B_50) = A_49
      | r2_hidden('#skF_2'(A_49,B_50),B_50)
      | k1_tarski(A_49) = B_50 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_26,plain,(
    ! [C_23,A_19] :
      ( r1_tarski(C_23,A_19)
      | ~ r2_hidden(C_23,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_193,plain,(
    ! [A_64,A_65] :
      ( r1_tarski('#skF_2'(A_64,k1_zfmisc_1(A_65)),A_65)
      | '#skF_1'(A_64,k1_zfmisc_1(A_65)) = A_64
      | k1_zfmisc_1(A_65) = k1_tarski(A_64) ) ),
    inference(resolution,[status(thm)],[c_117,c_26])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_200,plain,(
    ! [A_66] :
      ( '#skF_2'(A_66,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
      | '#skF_1'(A_66,k1_zfmisc_1(k1_xboole_0)) = A_66
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_66) ) ),
    inference(resolution,[status(thm)],[c_193,c_4])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( '#skF_1'(A_4,B_5) = A_4
      | '#skF_2'(A_4,B_5) != A_4
      | k1_tarski(A_4) = B_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_214,plain,(
    ! [A_66] :
      ( '#skF_1'(A_66,k1_zfmisc_1(k1_xboole_0)) = A_66
      | k1_xboole_0 != A_66
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_66)
      | '#skF_1'(A_66,k1_zfmisc_1(k1_xboole_0)) = A_66
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_12])).

tff(c_353,plain,(
    ! [A_89] :
      ( k1_xboole_0 != A_89
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_89)
      | '#skF_1'(A_89,k1_zfmisc_1(k1_xboole_0)) = A_89 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_214])).

tff(c_146,plain,(
    ! [A_55,B_56] :
      ( ~ r2_hidden('#skF_1'(A_55,B_56),B_56)
      | r2_hidden('#skF_2'(A_55,B_56),B_56)
      | k1_tarski(A_55) = B_56 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_282,plain,(
    ! [A_79,A_80] :
      ( r1_tarski('#skF_2'(A_79,k1_zfmisc_1(A_80)),A_80)
      | ~ r2_hidden('#skF_1'(A_79,k1_zfmisc_1(A_80)),k1_zfmisc_1(A_80))
      | k1_zfmisc_1(A_80) = k1_tarski(A_79) ) ),
    inference(resolution,[status(thm)],[c_146,c_26])).

tff(c_288,plain,(
    ! [A_81,A_82] :
      ( r1_tarski('#skF_2'(A_81,k1_zfmisc_1(A_82)),A_82)
      | k1_zfmisc_1(A_82) = k1_tarski(A_81)
      | ~ r1_tarski('#skF_1'(A_81,k1_zfmisc_1(A_82)),A_82) ) ),
    inference(resolution,[status(thm)],[c_28,c_282])).

tff(c_296,plain,(
    ! [A_81] :
      ( '#skF_2'(A_81,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_81)
      | ~ r1_tarski('#skF_1'(A_81,k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_288,c_4])).

tff(c_359,plain,(
    ! [A_89] :
      ( '#skF_2'(A_89,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_89)
      | ~ r1_tarski(A_89,k1_xboole_0)
      | k1_xboole_0 != A_89
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_296])).

tff(c_16,plain,(
    ! [A_4,B_5] :
      ( '#skF_1'(A_4,B_5) = A_4
      | r2_hidden('#skF_2'(A_4,B_5),B_5)
      | k1_tarski(A_4) = B_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_212,plain,(
    ! [A_66] :
      ( '#skF_1'(A_66,k1_zfmisc_1(k1_xboole_0)) = A_66
      | r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_66)
      | '#skF_1'(A_66,k1_zfmisc_1(k1_xboole_0)) = A_66
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_16])).

tff(c_455,plain,(
    r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_212])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( ~ r2_hidden('#skF_1'(A_4,B_5),B_5)
      | '#skF_2'(A_4,B_5) != A_4
      | k1_tarski(A_4) = B_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_368,plain,(
    ! [A_89] :
      ( ~ r2_hidden(A_89,k1_zfmisc_1(k1_xboole_0))
      | '#skF_2'(A_89,k1_zfmisc_1(k1_xboole_0)) != A_89
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_89)
      | k1_xboole_0 != A_89
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_10])).

tff(c_458,plain,
    ( '#skF_2'(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_455,c_368])).

tff(c_464,plain,(
    '#skF_2'(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_38,c_458])).

tff(c_469,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_464])).

tff(c_475,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_469])).

tff(c_477,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_475])).

tff(c_479,plain,(
    ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_212])).

tff(c_482,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_28,c_479])).

tff(c_486,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_482])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n019.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 15:10:52 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.32  
% 2.48/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.32  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1 > #skF_4
% 2.48/1.32  
% 2.48/1.32  %Foreground sorts:
% 2.48/1.32  
% 2.48/1.32  
% 2.48/1.32  %Background operators:
% 2.48/1.32  
% 2.48/1.32  
% 2.48/1.32  %Foreground operators:
% 2.48/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.48/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.48/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.48/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.48/1.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.48/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.48/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.48/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.48/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.48/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.48/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.48/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.48/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.48/1.32  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.48/1.32  
% 2.48/1.34  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.48/1.34  tff(f_31, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.48/1.34  tff(f_53, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.48/1.34  tff(f_55, negated_conjecture, ~(k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 2.48/1.34  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.48/1.34  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.48/1.34  tff(c_50, plain, (![A_28]: (k1_xboole_0=A_28 | ~r1_tarski(A_28, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.48/1.34  tff(c_62, plain, (![B_31]: (k3_xboole_0(k1_xboole_0, B_31)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_50])).
% 2.48/1.34  tff(c_67, plain, (r1_tarski(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_62, c_2])).
% 2.48/1.34  tff(c_28, plain, (![C_23, A_19]: (r2_hidden(C_23, k1_zfmisc_1(A_19)) | ~r1_tarski(C_23, A_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.48/1.34  tff(c_38, plain, (k1_zfmisc_1(k1_xboole_0)!=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.48/1.34  tff(c_117, plain, (![A_49, B_50]: ('#skF_1'(A_49, B_50)=A_49 | r2_hidden('#skF_2'(A_49, B_50), B_50) | k1_tarski(A_49)=B_50)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.48/1.34  tff(c_26, plain, (![C_23, A_19]: (r1_tarski(C_23, A_19) | ~r2_hidden(C_23, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.48/1.34  tff(c_193, plain, (![A_64, A_65]: (r1_tarski('#skF_2'(A_64, k1_zfmisc_1(A_65)), A_65) | '#skF_1'(A_64, k1_zfmisc_1(A_65))=A_64 | k1_zfmisc_1(A_65)=k1_tarski(A_64))), inference(resolution, [status(thm)], [c_117, c_26])).
% 2.48/1.34  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.48/1.34  tff(c_200, plain, (![A_66]: ('#skF_2'(A_66, k1_zfmisc_1(k1_xboole_0))=k1_xboole_0 | '#skF_1'(A_66, k1_zfmisc_1(k1_xboole_0))=A_66 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_66))), inference(resolution, [status(thm)], [c_193, c_4])).
% 2.48/1.34  tff(c_12, plain, (![A_4, B_5]: ('#skF_1'(A_4, B_5)=A_4 | '#skF_2'(A_4, B_5)!=A_4 | k1_tarski(A_4)=B_5)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.48/1.34  tff(c_214, plain, (![A_66]: ('#skF_1'(A_66, k1_zfmisc_1(k1_xboole_0))=A_66 | k1_xboole_0!=A_66 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_66) | '#skF_1'(A_66, k1_zfmisc_1(k1_xboole_0))=A_66 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_66))), inference(superposition, [status(thm), theory('equality')], [c_200, c_12])).
% 2.48/1.34  tff(c_353, plain, (![A_89]: (k1_xboole_0!=A_89 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_89) | '#skF_1'(A_89, k1_zfmisc_1(k1_xboole_0))=A_89)), inference(factorization, [status(thm), theory('equality')], [c_214])).
% 2.48/1.34  tff(c_146, plain, (![A_55, B_56]: (~r2_hidden('#skF_1'(A_55, B_56), B_56) | r2_hidden('#skF_2'(A_55, B_56), B_56) | k1_tarski(A_55)=B_56)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.48/1.34  tff(c_282, plain, (![A_79, A_80]: (r1_tarski('#skF_2'(A_79, k1_zfmisc_1(A_80)), A_80) | ~r2_hidden('#skF_1'(A_79, k1_zfmisc_1(A_80)), k1_zfmisc_1(A_80)) | k1_zfmisc_1(A_80)=k1_tarski(A_79))), inference(resolution, [status(thm)], [c_146, c_26])).
% 2.48/1.34  tff(c_288, plain, (![A_81, A_82]: (r1_tarski('#skF_2'(A_81, k1_zfmisc_1(A_82)), A_82) | k1_zfmisc_1(A_82)=k1_tarski(A_81) | ~r1_tarski('#skF_1'(A_81, k1_zfmisc_1(A_82)), A_82))), inference(resolution, [status(thm)], [c_28, c_282])).
% 2.48/1.34  tff(c_296, plain, (![A_81]: ('#skF_2'(A_81, k1_zfmisc_1(k1_xboole_0))=k1_xboole_0 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_81) | ~r1_tarski('#skF_1'(A_81, k1_zfmisc_1(k1_xboole_0)), k1_xboole_0))), inference(resolution, [status(thm)], [c_288, c_4])).
% 2.48/1.34  tff(c_359, plain, (![A_89]: ('#skF_2'(A_89, k1_zfmisc_1(k1_xboole_0))=k1_xboole_0 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_89) | ~r1_tarski(A_89, k1_xboole_0) | k1_xboole_0!=A_89 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_89))), inference(superposition, [status(thm), theory('equality')], [c_353, c_296])).
% 2.48/1.34  tff(c_16, plain, (![A_4, B_5]: ('#skF_1'(A_4, B_5)=A_4 | r2_hidden('#skF_2'(A_4, B_5), B_5) | k1_tarski(A_4)=B_5)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.48/1.34  tff(c_212, plain, (![A_66]: ('#skF_1'(A_66, k1_zfmisc_1(k1_xboole_0))=A_66 | r2_hidden(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)) | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_66) | '#skF_1'(A_66, k1_zfmisc_1(k1_xboole_0))=A_66 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_66))), inference(superposition, [status(thm), theory('equality')], [c_200, c_16])).
% 2.48/1.34  tff(c_455, plain, (r2_hidden(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_212])).
% 2.48/1.34  tff(c_10, plain, (![A_4, B_5]: (~r2_hidden('#skF_1'(A_4, B_5), B_5) | '#skF_2'(A_4, B_5)!=A_4 | k1_tarski(A_4)=B_5)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.48/1.34  tff(c_368, plain, (![A_89]: (~r2_hidden(A_89, k1_zfmisc_1(k1_xboole_0)) | '#skF_2'(A_89, k1_zfmisc_1(k1_xboole_0))!=A_89 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_89) | k1_xboole_0!=A_89 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_89))), inference(superposition, [status(thm), theory('equality')], [c_353, c_10])).
% 2.48/1.34  tff(c_458, plain, ('#skF_2'(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))!=k1_xboole_0 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(resolution, [status(thm)], [c_455, c_368])).
% 2.48/1.34  tff(c_464, plain, ('#skF_2'(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_38, c_38, c_458])).
% 2.48/1.34  tff(c_469, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0) | k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_359, c_464])).
% 2.48/1.34  tff(c_475, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_67, c_469])).
% 2.48/1.34  tff(c_477, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_475])).
% 2.48/1.34  tff(c_479, plain, (~r2_hidden(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_212])).
% 2.48/1.34  tff(c_482, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_479])).
% 2.48/1.34  tff(c_486, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_482])).
% 2.48/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.34  
% 2.48/1.34  Inference rules
% 2.48/1.34  ----------------------
% 2.48/1.34  #Ref     : 0
% 2.48/1.34  #Sup     : 84
% 2.48/1.34  #Fact    : 2
% 2.48/1.34  #Define  : 0
% 2.48/1.34  #Split   : 1
% 2.48/1.34  #Chain   : 0
% 2.48/1.34  #Close   : 0
% 2.48/1.34  
% 2.48/1.34  Ordering : KBO
% 2.48/1.34  
% 2.48/1.34  Simplification rules
% 2.48/1.34  ----------------------
% 2.48/1.34  #Subsume      : 11
% 2.48/1.34  #Demod        : 13
% 2.48/1.34  #Tautology    : 37
% 2.48/1.34  #SimpNegUnit  : 2
% 2.48/1.34  #BackRed      : 0
% 2.48/1.34  
% 2.48/1.34  #Partial instantiations: 0
% 2.48/1.34  #Strategies tried      : 1
% 2.48/1.34  
% 2.48/1.34  Timing (in seconds)
% 2.48/1.34  ----------------------
% 2.48/1.34  Preprocessing        : 0.29
% 2.48/1.34  Parsing              : 0.15
% 2.48/1.34  CNF conversion       : 0.02
% 2.48/1.34  Main loop            : 0.28
% 2.48/1.34  Inferencing          : 0.12
% 2.48/1.34  Reduction            : 0.07
% 2.48/1.34  Demodulation         : 0.04
% 2.48/1.34  BG Simplification    : 0.02
% 2.48/1.34  Subsumption          : 0.06
% 2.48/1.34  Abstraction          : 0.02
% 2.48/1.34  MUC search           : 0.00
% 2.48/1.34  Cooper               : 0.00
% 2.48/1.34  Total                : 0.60
% 2.48/1.34  Index Insertion      : 0.00
% 2.48/1.34  Index Deletion       : 0.00
% 2.48/1.34  Index Matching       : 0.00
% 2.48/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
