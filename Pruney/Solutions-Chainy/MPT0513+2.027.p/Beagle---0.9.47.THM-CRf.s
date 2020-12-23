%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:02 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   69 (  84 expanded)
%              Number of leaves         :   39 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :   56 (  87 expanded)
%              Number of equality atoms :   34 (  43 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k3_xboole_0(B,k2_zfmisc_1(A,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_83,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_44,plain,(
    ! [A_45] :
      ( r2_hidden('#skF_1'(A_45),A_45)
      | v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_232,plain,(
    ! [A_85,B_86] :
      ( r1_tarski(k1_tarski(A_85),B_86)
      | ~ r2_hidden(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_243,plain,(
    ! [A_88] :
      ( k1_tarski(A_88) = k1_xboole_0
      | ~ r2_hidden(A_88,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_232,c_8])).

tff(c_248,plain,
    ( k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_44,c_243])).

tff(c_249,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_248])).

tff(c_358,plain,(
    ! [B_104,A_105] :
      ( k3_xboole_0(B_104,k2_zfmisc_1(A_105,k2_relat_1(B_104))) = k7_relat_1(B_104,A_105)
      | ~ v1_relat_1(B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_10,plain,(
    ! [A_8] : k4_xboole_0(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_101,plain,(
    ! [B_71,A_72] : k5_xboole_0(B_71,A_72) = k5_xboole_0(A_72,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_117,plain,(
    ! [A_72] : k5_xboole_0(k1_xboole_0,A_72) = A_72 ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_12])).

tff(c_250,plain,(
    ! [A_89,B_90] : k5_xboole_0(A_89,k3_xboole_0(A_89,B_90)) = k4_xboole_0(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_264,plain,(
    ! [B_90] : k4_xboole_0(k1_xboole_0,B_90) = k3_xboole_0(k1_xboole_0,B_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_250])).

tff(c_271,plain,(
    ! [B_90] : k3_xboole_0(k1_xboole_0,B_90) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_264])).

tff(c_365,plain,(
    ! [A_105] :
      ( k7_relat_1(k1_xboole_0,A_105) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_271])).

tff(c_378,plain,(
    ! [A_105] : k7_relat_1(k1_xboole_0,A_105) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_365])).

tff(c_48,plain,(
    k7_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_384,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_48])).

tff(c_386,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_248])).

tff(c_14,plain,(
    ! [A_10] : k5_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_387,plain,(
    ! [A_106,B_107] : k5_xboole_0(A_106,k3_xboole_0(A_106,B_107)) = k4_xboole_0(A_106,B_107) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_404,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_387])).

tff(c_409,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_404])).

tff(c_34,plain,(
    ! [B_42] : k4_xboole_0(k1_tarski(B_42),k1_tarski(B_42)) != k1_tarski(B_42) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_410,plain,(
    ! [B_42] : k1_tarski(B_42) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_34])).

tff(c_241,plain,(
    ! [A_85] :
      ( k1_tarski(A_85) = k1_xboole_0
      | ~ r2_hidden(A_85,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_232,c_8])).

tff(c_428,plain,(
    ! [A_110] : ~ r2_hidden(A_110,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_410,c_241])).

tff(c_432,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_44,c_428])).

tff(c_436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_386,c_432])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:51:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.30  
% 2.14/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.30  %$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.31/1.30  
% 2.31/1.30  %Foreground sorts:
% 2.31/1.30  
% 2.31/1.30  
% 2.31/1.30  %Background operators:
% 2.31/1.30  
% 2.31/1.30  
% 2.31/1.30  %Foreground operators:
% 2.31/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.31/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.31/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.31/1.30  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.31/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.31/1.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.31/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.31/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.31/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.31/1.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.31/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.31/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.31/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.31/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.31/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.31/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.31/1.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.31/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.31/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.31/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.31/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.31/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.31/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.31/1.30  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.31/1.30  
% 2.31/1.32  tff(f_76, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.31/1.32  tff(f_59, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.31/1.32  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.31/1.32  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k3_xboole_0(B, k2_zfmisc_1(A, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_relat_1)).
% 2.31/1.32  tff(f_37, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.31/1.32  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 2.31/1.32  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.31/1.32  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.31/1.32  tff(f_83, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 2.31/1.32  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.31/1.32  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.31/1.32  tff(f_64, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.31/1.32  tff(c_44, plain, (![A_45]: (r2_hidden('#skF_1'(A_45), A_45) | v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.31/1.32  tff(c_232, plain, (![A_85, B_86]: (r1_tarski(k1_tarski(A_85), B_86) | ~r2_hidden(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.31/1.32  tff(c_8, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.31/1.32  tff(c_243, plain, (![A_88]: (k1_tarski(A_88)=k1_xboole_0 | ~r2_hidden(A_88, k1_xboole_0))), inference(resolution, [status(thm)], [c_232, c_8])).
% 2.31/1.32  tff(c_248, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0 | v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_243])).
% 2.31/1.32  tff(c_249, plain, (v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_248])).
% 2.31/1.32  tff(c_358, plain, (![B_104, A_105]: (k3_xboole_0(B_104, k2_zfmisc_1(A_105, k2_relat_1(B_104)))=k7_relat_1(B_104, A_105) | ~v1_relat_1(B_104))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.31/1.32  tff(c_10, plain, (![A_8]: (k4_xboole_0(k1_xboole_0, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.31/1.32  tff(c_101, plain, (![B_71, A_72]: (k5_xboole_0(B_71, A_72)=k5_xboole_0(A_72, B_71))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.31/1.32  tff(c_12, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.31/1.32  tff(c_117, plain, (![A_72]: (k5_xboole_0(k1_xboole_0, A_72)=A_72)), inference(superposition, [status(thm), theory('equality')], [c_101, c_12])).
% 2.31/1.32  tff(c_250, plain, (![A_89, B_90]: (k5_xboole_0(A_89, k3_xboole_0(A_89, B_90))=k4_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.31/1.32  tff(c_264, plain, (![B_90]: (k4_xboole_0(k1_xboole_0, B_90)=k3_xboole_0(k1_xboole_0, B_90))), inference(superposition, [status(thm), theory('equality')], [c_117, c_250])).
% 2.31/1.32  tff(c_271, plain, (![B_90]: (k3_xboole_0(k1_xboole_0, B_90)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_264])).
% 2.31/1.32  tff(c_365, plain, (![A_105]: (k7_relat_1(k1_xboole_0, A_105)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_358, c_271])).
% 2.31/1.32  tff(c_378, plain, (![A_105]: (k7_relat_1(k1_xboole_0, A_105)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_249, c_365])).
% 2.31/1.32  tff(c_48, plain, (k7_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.31/1.32  tff(c_384, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_378, c_48])).
% 2.31/1.32  tff(c_386, plain, (~v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_248])).
% 2.31/1.32  tff(c_14, plain, (![A_10]: (k5_xboole_0(A_10, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.31/1.32  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.31/1.32  tff(c_387, plain, (![A_106, B_107]: (k5_xboole_0(A_106, k3_xboole_0(A_106, B_107))=k4_xboole_0(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.31/1.32  tff(c_404, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_387])).
% 2.31/1.32  tff(c_409, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_404])).
% 2.31/1.32  tff(c_34, plain, (![B_42]: (k4_xboole_0(k1_tarski(B_42), k1_tarski(B_42))!=k1_tarski(B_42))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.31/1.32  tff(c_410, plain, (![B_42]: (k1_tarski(B_42)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_409, c_34])).
% 2.31/1.32  tff(c_241, plain, (![A_85]: (k1_tarski(A_85)=k1_xboole_0 | ~r2_hidden(A_85, k1_xboole_0))), inference(resolution, [status(thm)], [c_232, c_8])).
% 2.31/1.32  tff(c_428, plain, (![A_110]: (~r2_hidden(A_110, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_410, c_241])).
% 2.31/1.32  tff(c_432, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_428])).
% 2.31/1.32  tff(c_436, plain, $false, inference(negUnitSimplification, [status(thm)], [c_386, c_432])).
% 2.31/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.32  
% 2.31/1.32  Inference rules
% 2.31/1.32  ----------------------
% 2.31/1.32  #Ref     : 0
% 2.31/1.32  #Sup     : 82
% 2.31/1.32  #Fact    : 0
% 2.31/1.32  #Define  : 0
% 2.31/1.32  #Split   : 1
% 2.31/1.32  #Chain   : 0
% 2.31/1.32  #Close   : 0
% 2.31/1.32  
% 2.31/1.32  Ordering : KBO
% 2.31/1.32  
% 2.31/1.32  Simplification rules
% 2.31/1.32  ----------------------
% 2.31/1.32  #Subsume      : 0
% 2.31/1.32  #Demod        : 23
% 2.31/1.32  #Tautology    : 69
% 2.31/1.32  #SimpNegUnit  : 3
% 2.31/1.32  #BackRed      : 5
% 2.31/1.32  
% 2.31/1.32  #Partial instantiations: 0
% 2.31/1.32  #Strategies tried      : 1
% 2.31/1.32  
% 2.31/1.32  Timing (in seconds)
% 2.31/1.32  ----------------------
% 2.31/1.32  Preprocessing        : 0.32
% 2.31/1.32  Parsing              : 0.17
% 2.31/1.32  CNF conversion       : 0.02
% 2.31/1.32  Main loop            : 0.19
% 2.31/1.32  Inferencing          : 0.07
% 2.31/1.32  Reduction            : 0.06
% 2.31/1.32  Demodulation         : 0.04
% 2.31/1.32  BG Simplification    : 0.02
% 2.31/1.32  Subsumption          : 0.02
% 2.31/1.32  Abstraction          : 0.01
% 2.31/1.32  MUC search           : 0.00
% 2.31/1.32  Cooper               : 0.00
% 2.31/1.32  Total                : 0.54
% 2.31/1.32  Index Insertion      : 0.00
% 2.31/1.32  Index Deletion       : 0.00
% 2.31/1.32  Index Matching       : 0.00
% 2.31/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
