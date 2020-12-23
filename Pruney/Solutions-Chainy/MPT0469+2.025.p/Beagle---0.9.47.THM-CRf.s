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
% DateTime   : Thu Dec  3 09:58:55 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   77 (  92 expanded)
%              Number of leaves         :   41 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :   71 (  96 expanded)
%              Number of equality atoms :   31 (  48 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_94,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k1_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_44,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_28,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_42,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_54,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_87,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_6,plain,(
    ! [A_3] :
      ( r2_hidden('#skF_1'(A_3),A_3)
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_62,plain,(
    ! [A_67] :
      ( v1_relat_1(A_67)
      | ~ v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_66,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_62])).

tff(c_52,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_6'(A_63,B_64),k2_relat_1(B_64))
      | ~ r2_hidden(A_63,k1_relat_1(B_64))
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_210,plain,(
    ! [A_102,C_103] :
      ( r2_hidden(k4_tarski('#skF_5'(A_102,k2_relat_1(A_102),C_103),C_103),A_102)
      | ~ r2_hidden(C_103,k2_relat_1(A_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_12,plain,(
    ! [A_8] : k5_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_138,plain,(
    ! [A_83,B_84] : k5_xboole_0(A_83,k3_xboole_0(A_83,B_84)) = k4_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_147,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_138])).

tff(c_150,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_147])).

tff(c_32,plain,(
    ! [B_40] : k4_xboole_0(k1_tarski(B_40),k1_tarski(B_40)) != k1_tarski(B_40) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_151,plain,(
    ! [B_40] : k1_tarski(B_40) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_32])).

tff(c_90,plain,(
    ! [A_75,B_76] :
      ( r1_tarski(k1_tarski(A_75),B_76)
      | ~ r2_hidden(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_99,plain,(
    ! [A_75] :
      ( k1_tarski(A_75) = k1_xboole_0
      | ~ r2_hidden(A_75,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_90,c_10])).

tff(c_168,plain,(
    ! [A_75] : ~ r2_hidden(A_75,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_99])).

tff(c_220,plain,(
    ! [C_104] : ~ r2_hidden(C_104,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_210,c_168])).

tff(c_228,plain,(
    ! [A_63] :
      ( ~ r2_hidden(A_63,k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_52,c_220])).

tff(c_263,plain,(
    ! [A_110] : ~ r2_hidden(A_110,k1_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_228])).

tff(c_271,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_263])).

tff(c_276,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_271])).

tff(c_277,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_414,plain,(
    ! [A_146,C_147] :
      ( r2_hidden(k4_tarski('#skF_5'(A_146,k2_relat_1(A_146),C_147),C_147),A_146)
      | ~ r2_hidden(C_147,k2_relat_1(A_146)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_333,plain,(
    ! [A_122,B_123] : k5_xboole_0(A_122,k3_xboole_0(A_122,B_123)) = k4_xboole_0(A_122,B_123) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_342,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_333])).

tff(c_345,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_342])).

tff(c_346,plain,(
    ! [B_40] : k1_tarski(B_40) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_32])).

tff(c_283,plain,(
    ! [A_111,B_112] :
      ( r1_tarski(k1_tarski(A_111),B_112)
      | ~ r2_hidden(A_111,B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_288,plain,(
    ! [A_111] :
      ( k1_tarski(A_111) = k1_xboole_0
      | ~ r2_hidden(A_111,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_283,c_10])).

tff(c_354,plain,(
    ! [A_111] : ~ r2_hidden(A_111,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_346,c_288])).

tff(c_424,plain,(
    ! [C_148] : ~ r2_hidden(C_148,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_414,c_354])).

tff(c_436,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_424])).

tff(c_444,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_277,c_436])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:14:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.28  
% 2.30/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.29  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 2.30/1.29  
% 2.30/1.29  %Foreground sorts:
% 2.30/1.29  
% 2.30/1.29  
% 2.30/1.29  %Background operators:
% 2.30/1.29  
% 2.30/1.29  
% 2.30/1.29  %Foreground operators:
% 2.30/1.29  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.30/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.30/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.30/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.30/1.29  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.30/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.30/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.30/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.30/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.30/1.29  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.30/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.30/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.30/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.30/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.30/1.29  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.30/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.30/1.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.30/1.29  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.30/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.30/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.30/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.30/1.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.30/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.30/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.30/1.29  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.30/1.29  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.30/1.29  
% 2.38/1.30  tff(f_94, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.38/1.30  tff(f_36, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.38/1.30  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.38/1.30  tff(f_73, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.38/1.30  tff(f_90, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k1_relat_1(B)) & (![C]: ~r2_hidden(C, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_relat_1)).
% 2.38/1.30  tff(f_81, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 2.38/1.30  tff(f_44, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.38/1.30  tff(f_28, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.38/1.30  tff(f_38, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.38/1.30  tff(f_67, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.38/1.30  tff(f_62, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.38/1.30  tff(f_42, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.38/1.30  tff(c_54, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.38/1.30  tff(c_87, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_54])).
% 2.38/1.30  tff(c_6, plain, (![A_3]: (r2_hidden('#skF_1'(A_3), A_3) | k1_xboole_0=A_3)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.38/1.30  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.38/1.30  tff(c_62, plain, (![A_67]: (v1_relat_1(A_67) | ~v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.38/1.30  tff(c_66, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_62])).
% 2.38/1.30  tff(c_52, plain, (![A_63, B_64]: (r2_hidden('#skF_6'(A_63, B_64), k2_relat_1(B_64)) | ~r2_hidden(A_63, k1_relat_1(B_64)) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.38/1.30  tff(c_210, plain, (![A_102, C_103]: (r2_hidden(k4_tarski('#skF_5'(A_102, k2_relat_1(A_102), C_103), C_103), A_102) | ~r2_hidden(C_103, k2_relat_1(A_102)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.38/1.30  tff(c_12, plain, (![A_8]: (k5_xboole_0(A_8, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.38/1.30  tff(c_4, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.38/1.30  tff(c_138, plain, (![A_83, B_84]: (k5_xboole_0(A_83, k3_xboole_0(A_83, B_84))=k4_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.38/1.30  tff(c_147, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_4, c_138])).
% 2.38/1.30  tff(c_150, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_147])).
% 2.38/1.30  tff(c_32, plain, (![B_40]: (k4_xboole_0(k1_tarski(B_40), k1_tarski(B_40))!=k1_tarski(B_40))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.38/1.30  tff(c_151, plain, (![B_40]: (k1_tarski(B_40)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_150, c_32])).
% 2.38/1.30  tff(c_90, plain, (![A_75, B_76]: (r1_tarski(k1_tarski(A_75), B_76) | ~r2_hidden(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.38/1.30  tff(c_10, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.38/1.30  tff(c_99, plain, (![A_75]: (k1_tarski(A_75)=k1_xboole_0 | ~r2_hidden(A_75, k1_xboole_0))), inference(resolution, [status(thm)], [c_90, c_10])).
% 2.38/1.30  tff(c_168, plain, (![A_75]: (~r2_hidden(A_75, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_151, c_99])).
% 2.38/1.30  tff(c_220, plain, (![C_104]: (~r2_hidden(C_104, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_210, c_168])).
% 2.38/1.30  tff(c_228, plain, (![A_63]: (~r2_hidden(A_63, k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_52, c_220])).
% 2.38/1.30  tff(c_263, plain, (![A_110]: (~r2_hidden(A_110, k1_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_228])).
% 2.38/1.30  tff(c_271, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_263])).
% 2.38/1.30  tff(c_276, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_271])).
% 2.38/1.30  tff(c_277, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 2.38/1.30  tff(c_414, plain, (![A_146, C_147]: (r2_hidden(k4_tarski('#skF_5'(A_146, k2_relat_1(A_146), C_147), C_147), A_146) | ~r2_hidden(C_147, k2_relat_1(A_146)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.38/1.30  tff(c_333, plain, (![A_122, B_123]: (k5_xboole_0(A_122, k3_xboole_0(A_122, B_123))=k4_xboole_0(A_122, B_123))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.38/1.30  tff(c_342, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_4, c_333])).
% 2.38/1.30  tff(c_345, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_342])).
% 2.38/1.30  tff(c_346, plain, (![B_40]: (k1_tarski(B_40)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_345, c_32])).
% 2.38/1.30  tff(c_283, plain, (![A_111, B_112]: (r1_tarski(k1_tarski(A_111), B_112) | ~r2_hidden(A_111, B_112))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.38/1.30  tff(c_288, plain, (![A_111]: (k1_tarski(A_111)=k1_xboole_0 | ~r2_hidden(A_111, k1_xboole_0))), inference(resolution, [status(thm)], [c_283, c_10])).
% 2.38/1.30  tff(c_354, plain, (![A_111]: (~r2_hidden(A_111, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_346, c_288])).
% 2.38/1.30  tff(c_424, plain, (![C_148]: (~r2_hidden(C_148, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_414, c_354])).
% 2.38/1.30  tff(c_436, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_424])).
% 2.38/1.30  tff(c_444, plain, $false, inference(negUnitSimplification, [status(thm)], [c_277, c_436])).
% 2.38/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.30  
% 2.38/1.30  Inference rules
% 2.38/1.30  ----------------------
% 2.38/1.30  #Ref     : 0
% 2.38/1.30  #Sup     : 77
% 2.38/1.30  #Fact    : 0
% 2.38/1.30  #Define  : 0
% 2.38/1.30  #Split   : 1
% 2.38/1.30  #Chain   : 0
% 2.38/1.30  #Close   : 0
% 2.38/1.30  
% 2.38/1.30  Ordering : KBO
% 2.38/1.30  
% 2.38/1.30  Simplification rules
% 2.38/1.30  ----------------------
% 2.38/1.30  #Subsume      : 3
% 2.38/1.30  #Demod        : 12
% 2.38/1.30  #Tautology    : 58
% 2.38/1.30  #SimpNegUnit  : 10
% 2.38/1.30  #BackRed      : 5
% 2.38/1.30  
% 2.38/1.30  #Partial instantiations: 0
% 2.38/1.30  #Strategies tried      : 1
% 2.38/1.30  
% 2.38/1.30  Timing (in seconds)
% 2.38/1.30  ----------------------
% 2.38/1.30  Preprocessing        : 0.33
% 2.38/1.30  Parsing              : 0.17
% 2.38/1.30  CNF conversion       : 0.02
% 2.38/1.30  Main loop            : 0.20
% 2.38/1.30  Inferencing          : 0.08
% 2.38/1.30  Reduction            : 0.06
% 2.38/1.30  Demodulation         : 0.04
% 2.38/1.30  BG Simplification    : 0.02
% 2.38/1.30  Subsumption          : 0.03
% 2.38/1.30  Abstraction          : 0.01
% 2.38/1.31  MUC search           : 0.00
% 2.38/1.31  Cooper               : 0.00
% 2.38/1.31  Total                : 0.57
% 2.38/1.31  Index Insertion      : 0.00
% 2.38/1.31  Index Deletion       : 0.00
% 2.38/1.31  Index Matching       : 0.00
% 2.38/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
