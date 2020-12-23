%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:33 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 133 expanded)
%              Number of leaves         :   39 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :   76 ( 159 expanded)
%              Number of equality atoms :   31 (  69 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_2 > #skF_7 > #skF_4 > #skF_8 > #skF_3 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_93,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_120,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_71,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_115,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_54,plain,(
    ! [C_39] : r2_hidden(C_39,k1_tarski(C_39)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_86,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_268,plain,(
    ! [A_117,B_118] : k5_xboole_0(A_117,k3_xboole_0(A_117,B_118)) = k4_xboole_0(A_117,B_118) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_286,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_268])).

tff(c_14,plain,(
    ! [A_15] : k2_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_109,plain,(
    ! [A_78,B_79] : r1_tarski(A_78,k2_xboole_0(A_78,B_79)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_112,plain,(
    ! [A_15] : r1_tarski(A_15,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_109])).

tff(c_248,plain,(
    ! [A_112,C_113,B_114] :
      ( r1_tarski(A_112,k2_xboole_0(C_113,B_114))
      | ~ r1_tarski(A_112,B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_259,plain,(
    ! [A_115,A_116] :
      ( r1_tarski(A_115,A_116)
      | ~ r1_tarski(A_115,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_248])).

tff(c_290,plain,(
    ! [A_119] : r1_tarski(k1_xboole_0,A_119) ),
    inference(resolution,[status(thm)],[c_112,c_259])).

tff(c_18,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_301,plain,(
    ! [A_120] : k3_xboole_0(k1_xboole_0,A_120) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_290,c_18])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_350,plain,(
    ! [A_124] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_10])).

tff(c_24,plain,(
    ! [A_24,B_25] : r1_xboole_0(k4_xboole_0(A_24,B_25),B_25) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_367,plain,(
    ! [A_124] : r1_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),A_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_24])).

tff(c_378,plain,(
    ! [A_124] : r1_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),A_124) ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_367])).

tff(c_380,plain,(
    ! [A_125,B_126,C_127] :
      ( ~ r1_xboole_0(A_125,B_126)
      | ~ r2_hidden(C_127,k3_xboole_0(A_125,B_126)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_399,plain,(
    ! [A_129,C_130] :
      ( ~ r1_xboole_0(A_129,A_129)
      | ~ r2_hidden(C_130,A_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_380])).

tff(c_404,plain,(
    ! [C_131] : ~ r2_hidden(C_131,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_378,c_399])).

tff(c_409,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_404])).

tff(c_412,plain,(
    ! [A_124] : r1_xboole_0(k1_xboole_0,A_124) ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_378])).

tff(c_88,plain,(
    r1_tarski(k1_tarski('#skF_7'),k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_515,plain,(
    ! [B_140,A_141] :
      ( k1_tarski(B_140) = A_141
      | k1_xboole_0 = A_141
      | ~ r1_tarski(A_141,k1_tarski(B_140)) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_534,plain,
    ( k1_tarski('#skF_7') = k1_tarski('#skF_8')
    | k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_88,c_515])).

tff(c_556,plain,(
    k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_534])).

tff(c_172,plain,(
    ! [A_102,B_103] :
      ( k3_xboole_0(A_102,B_103) = A_102
      | ~ r1_tarski(A_102,B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_189,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(resolution,[status(thm)],[c_88,c_172])).

tff(c_386,plain,(
    ! [C_127] :
      ( ~ r1_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8'))
      | ~ r2_hidden(C_127,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_380])).

tff(c_410,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_386])).

tff(c_558,plain,(
    ~ r1_xboole_0(k1_xboole_0,k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_410])).

tff(c_564,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_558])).

tff(c_565,plain,(
    k1_tarski('#skF_7') = k1_tarski('#skF_8') ),
    inference(splitRight,[status(thm)],[c_534])).

tff(c_587,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_565,c_54])).

tff(c_52,plain,(
    ! [C_39,A_35] :
      ( C_39 = A_35
      | ~ r2_hidden(C_39,k1_tarski(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_595,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_587,c_52])).

tff(c_599,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_595])).

tff(c_602,plain,(
    ! [C_144] : ~ r2_hidden(C_144,k1_tarski('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_386])).

tff(c_612,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_54,c_602])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:58:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.36  
% 2.67/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.36  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_2 > #skF_7 > #skF_4 > #skF_8 > #skF_3 > #skF_1 > #skF_5
% 2.67/1.36  
% 2.67/1.36  %Foreground sorts:
% 2.67/1.36  
% 2.67/1.36  
% 2.67/1.36  %Background operators:
% 2.67/1.36  
% 2.67/1.36  
% 2.67/1.36  %Foreground operators:
% 2.67/1.36  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.67/1.36  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.67/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.67/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.67/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.67/1.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.67/1.36  tff('#skF_7', type, '#skF_7': $i).
% 2.67/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.67/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.67/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.67/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.67/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.67/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.67/1.36  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.67/1.36  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.67/1.36  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.67/1.36  tff('#skF_8', type, '#skF_8': $i).
% 2.67/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.67/1.36  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.67/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.67/1.36  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.67/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.67/1.36  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.67/1.36  
% 2.78/1.38  tff(f_93, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.78/1.38  tff(f_120, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.78/1.38  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.78/1.38  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.78/1.38  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.78/1.38  tff(f_57, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.78/1.38  tff(f_71, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.78/1.38  tff(f_55, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.78/1.38  tff(f_63, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.78/1.38  tff(f_69, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.78/1.38  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.78/1.38  tff(f_115, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.78/1.38  tff(c_54, plain, (![C_39]: (r2_hidden(C_39, k1_tarski(C_39)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.78/1.38  tff(c_86, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.78/1.38  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.78/1.38  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.78/1.38  tff(c_268, plain, (![A_117, B_118]: (k5_xboole_0(A_117, k3_xboole_0(A_117, B_118))=k4_xboole_0(A_117, B_118))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.78/1.38  tff(c_286, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_268])).
% 2.78/1.38  tff(c_14, plain, (![A_15]: (k2_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.78/1.38  tff(c_109, plain, (![A_78, B_79]: (r1_tarski(A_78, k2_xboole_0(A_78, B_79)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.78/1.38  tff(c_112, plain, (![A_15]: (r1_tarski(A_15, A_15))), inference(superposition, [status(thm), theory('equality')], [c_14, c_109])).
% 2.78/1.38  tff(c_248, plain, (![A_112, C_113, B_114]: (r1_tarski(A_112, k2_xboole_0(C_113, B_114)) | ~r1_tarski(A_112, B_114))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.78/1.38  tff(c_259, plain, (![A_115, A_116]: (r1_tarski(A_115, A_116) | ~r1_tarski(A_115, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_248])).
% 2.78/1.38  tff(c_290, plain, (![A_119]: (r1_tarski(k1_xboole_0, A_119))), inference(resolution, [status(thm)], [c_112, c_259])).
% 2.78/1.38  tff(c_18, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.78/1.38  tff(c_301, plain, (![A_120]: (k3_xboole_0(k1_xboole_0, A_120)=k1_xboole_0)), inference(resolution, [status(thm)], [c_290, c_18])).
% 2.78/1.38  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.78/1.38  tff(c_350, plain, (![A_124]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_124))), inference(superposition, [status(thm), theory('equality')], [c_301, c_10])).
% 2.78/1.38  tff(c_24, plain, (![A_24, B_25]: (r1_xboole_0(k4_xboole_0(A_24, B_25), B_25))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.78/1.38  tff(c_367, plain, (![A_124]: (r1_xboole_0(k5_xboole_0(k1_xboole_0, k1_xboole_0), A_124))), inference(superposition, [status(thm), theory('equality')], [c_350, c_24])).
% 2.78/1.38  tff(c_378, plain, (![A_124]: (r1_xboole_0(k4_xboole_0(k1_xboole_0, k1_xboole_0), A_124))), inference(demodulation, [status(thm), theory('equality')], [c_286, c_367])).
% 2.78/1.38  tff(c_380, plain, (![A_125, B_126, C_127]: (~r1_xboole_0(A_125, B_126) | ~r2_hidden(C_127, k3_xboole_0(A_125, B_126)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.78/1.38  tff(c_399, plain, (![A_129, C_130]: (~r1_xboole_0(A_129, A_129) | ~r2_hidden(C_130, A_129))), inference(superposition, [status(thm), theory('equality')], [c_2, c_380])).
% 2.78/1.38  tff(c_404, plain, (![C_131]: (~r2_hidden(C_131, k4_xboole_0(k1_xboole_0, k1_xboole_0)))), inference(resolution, [status(thm)], [c_378, c_399])).
% 2.78/1.38  tff(c_409, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_404])).
% 2.78/1.38  tff(c_412, plain, (![A_124]: (r1_xboole_0(k1_xboole_0, A_124))), inference(demodulation, [status(thm), theory('equality')], [c_409, c_378])).
% 2.78/1.38  tff(c_88, plain, (r1_tarski(k1_tarski('#skF_7'), k1_tarski('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.78/1.38  tff(c_515, plain, (![B_140, A_141]: (k1_tarski(B_140)=A_141 | k1_xboole_0=A_141 | ~r1_tarski(A_141, k1_tarski(B_140)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.78/1.38  tff(c_534, plain, (k1_tarski('#skF_7')=k1_tarski('#skF_8') | k1_tarski('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_88, c_515])).
% 2.78/1.38  tff(c_556, plain, (k1_tarski('#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_534])).
% 2.78/1.38  tff(c_172, plain, (![A_102, B_103]: (k3_xboole_0(A_102, B_103)=A_102 | ~r1_tarski(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.78/1.38  tff(c_189, plain, (k3_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(resolution, [status(thm)], [c_88, c_172])).
% 2.78/1.38  tff(c_386, plain, (![C_127]: (~r1_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8')) | ~r2_hidden(C_127, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_189, c_380])).
% 2.78/1.38  tff(c_410, plain, (~r1_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))), inference(splitLeft, [status(thm)], [c_386])).
% 2.78/1.38  tff(c_558, plain, (~r1_xboole_0(k1_xboole_0, k1_tarski('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_556, c_410])).
% 2.78/1.38  tff(c_564, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_412, c_558])).
% 2.78/1.38  tff(c_565, plain, (k1_tarski('#skF_7')=k1_tarski('#skF_8')), inference(splitRight, [status(thm)], [c_534])).
% 2.78/1.38  tff(c_587, plain, (r2_hidden('#skF_7', k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_565, c_54])).
% 2.78/1.38  tff(c_52, plain, (![C_39, A_35]: (C_39=A_35 | ~r2_hidden(C_39, k1_tarski(A_35)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.78/1.38  tff(c_595, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_587, c_52])).
% 2.78/1.38  tff(c_599, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_595])).
% 2.78/1.38  tff(c_602, plain, (![C_144]: (~r2_hidden(C_144, k1_tarski('#skF_7')))), inference(splitRight, [status(thm)], [c_386])).
% 2.78/1.38  tff(c_612, plain, $false, inference(resolution, [status(thm)], [c_54, c_602])).
% 2.78/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.38  
% 2.78/1.38  Inference rules
% 2.78/1.38  ----------------------
% 2.78/1.38  #Ref     : 0
% 2.78/1.38  #Sup     : 119
% 2.78/1.38  #Fact    : 0
% 2.78/1.38  #Define  : 0
% 2.78/1.38  #Split   : 2
% 2.78/1.38  #Chain   : 0
% 2.78/1.38  #Close   : 0
% 2.78/1.38  
% 2.78/1.38  Ordering : KBO
% 2.78/1.38  
% 2.78/1.38  Simplification rules
% 2.78/1.38  ----------------------
% 2.78/1.38  #Subsume      : 4
% 2.78/1.38  #Demod        : 79
% 2.78/1.38  #Tautology    : 85
% 2.78/1.38  #SimpNegUnit  : 1
% 2.78/1.38  #BackRed      : 13
% 2.78/1.38  
% 2.78/1.38  #Partial instantiations: 0
% 2.78/1.38  #Strategies tried      : 1
% 2.78/1.38  
% 2.78/1.38  Timing (in seconds)
% 2.78/1.38  ----------------------
% 2.78/1.38  Preprocessing        : 0.35
% 2.78/1.38  Parsing              : 0.18
% 2.78/1.38  CNF conversion       : 0.03
% 2.78/1.38  Main loop            : 0.27
% 2.78/1.38  Inferencing          : 0.09
% 2.78/1.38  Reduction            : 0.10
% 2.78/1.38  Demodulation         : 0.07
% 2.78/1.38  BG Simplification    : 0.02
% 2.78/1.38  Subsumption          : 0.05
% 2.78/1.38  Abstraction          : 0.01
% 2.78/1.38  MUC search           : 0.00
% 2.78/1.38  Cooper               : 0.00
% 2.78/1.38  Total                : 0.65
% 2.78/1.38  Index Insertion      : 0.00
% 2.78/1.38  Index Deletion       : 0.00
% 2.78/1.38  Index Matching       : 0.00
% 2.78/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
