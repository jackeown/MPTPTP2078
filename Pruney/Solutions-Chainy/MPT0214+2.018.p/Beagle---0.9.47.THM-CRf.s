%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:32 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 102 expanded)
%              Number of leaves         :   39 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :   72 ( 123 expanded)
%              Number of equality atoms :   37 (  57 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_4 > #skF_8 > #skF_2 > #skF_3 > #skF_5

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_112,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_57,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_107,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_84,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_52,plain,(
    ! [C_34] : r2_hidden(C_34,k1_tarski(C_34)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_108,plain,(
    ! [B_75,A_76] :
      ( ~ r2_hidden(B_75,A_76)
      | ~ v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_112,plain,(
    ! [C_34] : ~ v1_xboole_0(k1_tarski(C_34)) ),
    inference(resolution,[status(thm)],[c_52,c_108])).

tff(c_152,plain,(
    ! [A_96] :
      ( v1_xboole_0(A_96)
      | r2_hidden('#skF_1'(A_96),A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    ! [C_34,A_30] :
      ( C_34 = A_30
      | ~ r2_hidden(C_34,k1_tarski(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_156,plain,(
    ! [A_30] :
      ( '#skF_1'(k1_tarski(A_30)) = A_30
      | v1_xboole_0(k1_tarski(A_30)) ) ),
    inference(resolution,[status(thm)],[c_152,c_50])).

tff(c_162,plain,(
    ! [A_30] : '#skF_1'(k1_tarski(A_30)) = A_30 ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_156])).

tff(c_18,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_82,plain,(
    ! [B_69] : r1_tarski(k1_xboole_0,k1_tarski(B_69)) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_178,plain,(
    ! [A_98,B_99] :
      ( k3_xboole_0(A_98,B_99) = A_98
      | ~ r1_tarski(A_98,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_190,plain,(
    ! [B_69] : k3_xboole_0(k1_xboole_0,k1_tarski(B_69)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_82,c_178])).

tff(c_272,plain,(
    ! [A_116,B_117] : k5_xboole_0(A_116,k3_xboole_0(A_116,B_117)) = k4_xboole_0(A_116,B_117) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_284,plain,(
    ! [B_69] : k4_xboole_0(k1_xboole_0,k1_tarski(B_69)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_272])).

tff(c_312,plain,(
    ! [B_119] : k4_xboole_0(k1_xboole_0,k1_tarski(B_119)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_284])).

tff(c_24,plain,(
    ! [A_21,B_22] : k5_xboole_0(A_21,k4_xboole_0(B_22,A_21)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_317,plain,(
    ! [B_119] : k5_xboole_0(k1_tarski(B_119),k1_xboole_0) = k2_xboole_0(k1_tarski(B_119),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_24])).

tff(c_323,plain,(
    ! [B_120] : k2_xboole_0(k1_tarski(B_120),k1_xboole_0) = k1_tarski(B_120) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_317])).

tff(c_16,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k2_xboole_0(A_16,B_17)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_329,plain,(
    ! [B_120] : k4_xboole_0(k1_tarski(B_120),k1_tarski(B_120)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_16])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( r1_xboole_0(A_19,B_20)
      | k4_xboole_0(A_19,B_20) != A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_80,plain,(
    ! [B_69] : r1_tarski(k1_tarski(B_69),k1_tarski(B_69)) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_188,plain,(
    ! [B_69] : k3_xboole_0(k1_tarski(B_69),k1_tarski(B_69)) = k1_tarski(B_69) ),
    inference(resolution,[status(thm)],[c_80,c_178])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_350,plain,(
    ! [A_122,B_123,C_124] :
      ( ~ r1_xboole_0(A_122,B_123)
      | ~ r2_hidden(C_124,k3_xboole_0(A_122,B_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_368,plain,(
    ! [A_125,B_126] :
      ( ~ r1_xboole_0(A_125,B_126)
      | v1_xboole_0(k3_xboole_0(A_125,B_126)) ) ),
    inference(resolution,[status(thm)],[c_4,c_350])).

tff(c_371,plain,(
    ! [B_69] :
      ( ~ r1_xboole_0(k1_tarski(B_69),k1_tarski(B_69))
      | v1_xboole_0(k1_tarski(B_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_368])).

tff(c_383,plain,(
    ! [B_127] : ~ r1_xboole_0(k1_tarski(B_127),k1_tarski(B_127)) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_371])).

tff(c_386,plain,(
    ! [B_127] : k4_xboole_0(k1_tarski(B_127),k1_tarski(B_127)) != k1_tarski(B_127) ),
    inference(resolution,[status(thm)],[c_22,c_383])).

tff(c_388,plain,(
    ! [B_127] : k1_tarski(B_127) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_386])).

tff(c_86,plain,(
    r1_tarski(k1_tarski('#skF_7'),k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_405,plain,(
    ! [B_130,A_131] :
      ( k1_tarski(B_130) = A_131
      | k1_xboole_0 = A_131
      | ~ r1_tarski(A_131,k1_tarski(B_130)) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_411,plain,
    ( k1_tarski('#skF_7') = k1_tarski('#skF_8')
    | k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_86,c_405])).

tff(c_421,plain,(
    k1_tarski('#skF_7') = k1_tarski('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_388,c_411])).

tff(c_464,plain,(
    '#skF_1'(k1_tarski('#skF_8')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_421,c_162])).

tff(c_493,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_464])).

tff(c_495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_493])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:25:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.37  
% 2.55/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.37  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_4 > #skF_8 > #skF_2 > #skF_3 > #skF_5
% 2.55/1.37  
% 2.55/1.37  %Foreground sorts:
% 2.55/1.37  
% 2.55/1.37  
% 2.55/1.37  %Background operators:
% 2.55/1.37  
% 2.55/1.37  
% 2.55/1.37  %Foreground operators:
% 2.55/1.37  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.55/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.55/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.55/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.55/1.37  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.55/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.55/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.55/1.37  tff('#skF_7', type, '#skF_7': $i).
% 2.55/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.55/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.55/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.55/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.55/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.55/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.55/1.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.55/1.37  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.55/1.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.55/1.37  tff('#skF_8', type, '#skF_8': $i).
% 2.55/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.55/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.55/1.37  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.55/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.55/1.37  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.55/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.55/1.37  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.55/1.37  
% 2.55/1.39  tff(f_112, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.55/1.39  tff(f_85, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.55/1.39  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.55/1.39  tff(f_57, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.55/1.39  tff(f_107, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.55/1.39  tff(f_53, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.55/1.39  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.55/1.39  tff(f_63, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.55/1.39  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.55/1.39  tff(f_61, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.55/1.39  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.55/1.39  tff(c_84, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.55/1.39  tff(c_52, plain, (![C_34]: (r2_hidden(C_34, k1_tarski(C_34)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.55/1.39  tff(c_108, plain, (![B_75, A_76]: (~r2_hidden(B_75, A_76) | ~v1_xboole_0(A_76))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.55/1.39  tff(c_112, plain, (![C_34]: (~v1_xboole_0(k1_tarski(C_34)))), inference(resolution, [status(thm)], [c_52, c_108])).
% 2.55/1.39  tff(c_152, plain, (![A_96]: (v1_xboole_0(A_96) | r2_hidden('#skF_1'(A_96), A_96))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.55/1.39  tff(c_50, plain, (![C_34, A_30]: (C_34=A_30 | ~r2_hidden(C_34, k1_tarski(A_30)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.55/1.39  tff(c_156, plain, (![A_30]: ('#skF_1'(k1_tarski(A_30))=A_30 | v1_xboole_0(k1_tarski(A_30)))), inference(resolution, [status(thm)], [c_152, c_50])).
% 2.55/1.39  tff(c_162, plain, (![A_30]: ('#skF_1'(k1_tarski(A_30))=A_30)), inference(negUnitSimplification, [status(thm)], [c_112, c_156])).
% 2.55/1.39  tff(c_18, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.55/1.39  tff(c_82, plain, (![B_69]: (r1_tarski(k1_xboole_0, k1_tarski(B_69)))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.55/1.39  tff(c_178, plain, (![A_98, B_99]: (k3_xboole_0(A_98, B_99)=A_98 | ~r1_tarski(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.55/1.39  tff(c_190, plain, (![B_69]: (k3_xboole_0(k1_xboole_0, k1_tarski(B_69))=k1_xboole_0)), inference(resolution, [status(thm)], [c_82, c_178])).
% 2.55/1.39  tff(c_272, plain, (![A_116, B_117]: (k5_xboole_0(A_116, k3_xboole_0(A_116, B_117))=k4_xboole_0(A_116, B_117))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.55/1.39  tff(c_284, plain, (![B_69]: (k4_xboole_0(k1_xboole_0, k1_tarski(B_69))=k5_xboole_0(k1_xboole_0, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_190, c_272])).
% 2.55/1.39  tff(c_312, plain, (![B_119]: (k4_xboole_0(k1_xboole_0, k1_tarski(B_119))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_284])).
% 2.55/1.39  tff(c_24, plain, (![A_21, B_22]: (k5_xboole_0(A_21, k4_xboole_0(B_22, A_21))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.55/1.39  tff(c_317, plain, (![B_119]: (k5_xboole_0(k1_tarski(B_119), k1_xboole_0)=k2_xboole_0(k1_tarski(B_119), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_312, c_24])).
% 2.55/1.39  tff(c_323, plain, (![B_120]: (k2_xboole_0(k1_tarski(B_120), k1_xboole_0)=k1_tarski(B_120))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_317])).
% 2.55/1.39  tff(c_16, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k2_xboole_0(A_16, B_17))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.55/1.39  tff(c_329, plain, (![B_120]: (k4_xboole_0(k1_tarski(B_120), k1_tarski(B_120))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_323, c_16])).
% 2.55/1.39  tff(c_22, plain, (![A_19, B_20]: (r1_xboole_0(A_19, B_20) | k4_xboole_0(A_19, B_20)!=A_19)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.55/1.39  tff(c_80, plain, (![B_69]: (r1_tarski(k1_tarski(B_69), k1_tarski(B_69)))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.55/1.39  tff(c_188, plain, (![B_69]: (k3_xboole_0(k1_tarski(B_69), k1_tarski(B_69))=k1_tarski(B_69))), inference(resolution, [status(thm)], [c_80, c_178])).
% 2.55/1.39  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.55/1.39  tff(c_350, plain, (![A_122, B_123, C_124]: (~r1_xboole_0(A_122, B_123) | ~r2_hidden(C_124, k3_xboole_0(A_122, B_123)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.55/1.39  tff(c_368, plain, (![A_125, B_126]: (~r1_xboole_0(A_125, B_126) | v1_xboole_0(k3_xboole_0(A_125, B_126)))), inference(resolution, [status(thm)], [c_4, c_350])).
% 2.55/1.39  tff(c_371, plain, (![B_69]: (~r1_xboole_0(k1_tarski(B_69), k1_tarski(B_69)) | v1_xboole_0(k1_tarski(B_69)))), inference(superposition, [status(thm), theory('equality')], [c_188, c_368])).
% 2.55/1.39  tff(c_383, plain, (![B_127]: (~r1_xboole_0(k1_tarski(B_127), k1_tarski(B_127)))), inference(negUnitSimplification, [status(thm)], [c_112, c_371])).
% 2.55/1.39  tff(c_386, plain, (![B_127]: (k4_xboole_0(k1_tarski(B_127), k1_tarski(B_127))!=k1_tarski(B_127))), inference(resolution, [status(thm)], [c_22, c_383])).
% 2.55/1.39  tff(c_388, plain, (![B_127]: (k1_tarski(B_127)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_329, c_386])).
% 2.55/1.39  tff(c_86, plain, (r1_tarski(k1_tarski('#skF_7'), k1_tarski('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.55/1.39  tff(c_405, plain, (![B_130, A_131]: (k1_tarski(B_130)=A_131 | k1_xboole_0=A_131 | ~r1_tarski(A_131, k1_tarski(B_130)))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.55/1.39  tff(c_411, plain, (k1_tarski('#skF_7')=k1_tarski('#skF_8') | k1_tarski('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_86, c_405])).
% 2.55/1.39  tff(c_421, plain, (k1_tarski('#skF_7')=k1_tarski('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_388, c_411])).
% 2.55/1.39  tff(c_464, plain, ('#skF_1'(k1_tarski('#skF_8'))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_421, c_162])).
% 2.55/1.39  tff(c_493, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_162, c_464])).
% 2.55/1.39  tff(c_495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_493])).
% 2.55/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.39  
% 2.55/1.39  Inference rules
% 2.55/1.39  ----------------------
% 2.55/1.39  #Ref     : 0
% 2.55/1.39  #Sup     : 97
% 2.55/1.39  #Fact    : 0
% 2.55/1.39  #Define  : 0
% 2.55/1.39  #Split   : 2
% 2.55/1.39  #Chain   : 0
% 2.55/1.39  #Close   : 0
% 2.55/1.39  
% 2.55/1.39  Ordering : KBO
% 2.55/1.39  
% 2.55/1.39  Simplification rules
% 2.55/1.39  ----------------------
% 2.55/1.39  #Subsume      : 11
% 2.55/1.39  #Demod        : 36
% 2.55/1.39  #Tautology    : 52
% 2.55/1.39  #SimpNegUnit  : 8
% 2.55/1.39  #BackRed      : 3
% 2.55/1.39  
% 2.55/1.39  #Partial instantiations: 0
% 2.55/1.39  #Strategies tried      : 1
% 2.55/1.39  
% 2.55/1.39  Timing (in seconds)
% 2.55/1.39  ----------------------
% 2.55/1.39  Preprocessing        : 0.35
% 2.55/1.39  Parsing              : 0.17
% 2.55/1.39  CNF conversion       : 0.03
% 2.55/1.39  Main loop            : 0.23
% 2.55/1.39  Inferencing          : 0.07
% 2.55/1.39  Reduction            : 0.08
% 2.55/1.39  Demodulation         : 0.05
% 2.55/1.39  BG Simplification    : 0.02
% 2.55/1.39  Subsumption          : 0.04
% 2.55/1.39  Abstraction          : 0.01
% 2.55/1.39  MUC search           : 0.00
% 2.55/1.39  Cooper               : 0.00
% 2.55/1.39  Total                : 0.61
% 2.55/1.39  Index Insertion      : 0.00
% 2.55/1.39  Index Deletion       : 0.00
% 2.55/1.39  Index Matching       : 0.00
% 2.55/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
