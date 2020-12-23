%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:37 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 182 expanded)
%              Number of leaves         :   38 (  79 expanded)
%              Depth                    :   11
%              Number of atoms          :   80 ( 270 expanded)
%              Number of equality atoms :   36 (  91 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_3 > #skF_2 > #skF_5 > #skF_4

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_111,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_59,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_84,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_106,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_66,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_24,plain,(
    ! [A_23,B_24] : r1_xboole_0(k4_xboole_0(A_23,B_24),B_24) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_106,plain,(
    ! [B_80,A_81] :
      ( r1_xboole_0(B_80,A_81)
      | ~ r1_xboole_0(A_81,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_109,plain,(
    ! [B_24,A_23] : r1_xboole_0(B_24,k4_xboole_0(A_23,B_24)) ),
    inference(resolution,[status(thm)],[c_24,c_106])).

tff(c_14,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_3'(A_14),A_14)
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_242,plain,(
    ! [A_102,B_103,C_104] :
      ( ~ r1_xboole_0(A_102,B_103)
      | ~ r2_hidden(C_104,k3_xboole_0(A_102,B_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_276,plain,(
    ! [A_109,B_110] :
      ( ~ r1_xboole_0(A_109,B_110)
      | k3_xboole_0(A_109,B_110) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_242])).

tff(c_291,plain,(
    ! [B_24,A_23] : k3_xboole_0(B_24,k4_xboole_0(A_23,B_24)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_109,c_276])).

tff(c_192,plain,(
    ! [A_97,B_98] :
      ( k4_xboole_0(A_97,B_98) = A_97
      | ~ r1_xboole_0(A_97,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_203,plain,(
    ! [B_24,A_23] : k4_xboole_0(B_24,k4_xboole_0(A_23,B_24)) = B_24 ),
    inference(resolution,[status(thm)],[c_109,c_192])).

tff(c_349,plain,(
    ! [A_116,B_117] : k4_xboole_0(A_116,k4_xboole_0(A_116,B_117)) = k3_xboole_0(A_116,B_117) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_383,plain,(
    ! [B_24,A_23] : k3_xboole_0(B_24,k4_xboole_0(A_23,B_24)) = k4_xboole_0(B_24,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_349])).

tff(c_391,plain,(
    ! [B_24] : k4_xboole_0(B_24,B_24) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_383])).

tff(c_158,plain,(
    ! [A_90,B_91] :
      ( r1_xboole_0(A_90,B_91)
      | k4_xboole_0(A_90,B_91) != A_90 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( r1_xboole_0(B_8,A_7)
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_161,plain,(
    ! [B_91,A_90] :
      ( r1_xboole_0(B_91,A_90)
      | k4_xboole_0(A_90,B_91) != A_90 ) ),
    inference(resolution,[status(thm)],[c_158,c_8])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_835,plain,(
    ! [A_133,B_134] :
      ( ~ r1_xboole_0(A_133,B_134)
      | v1_xboole_0(k3_xboole_0(A_133,B_134)) ) ),
    inference(resolution,[status(thm)],[c_4,c_242])).

tff(c_867,plain,(
    ! [A_135] :
      ( ~ r1_xboole_0(A_135,A_135)
      | v1_xboole_0(A_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_835])).

tff(c_879,plain,(
    ! [A_90] :
      ( v1_xboole_0(A_90)
      | k4_xboole_0(A_90,A_90) != A_90 ) ),
    inference(resolution,[status(thm)],[c_161,c_867])).

tff(c_903,plain,(
    ! [A_139] :
      ( v1_xboole_0(A_139)
      | k1_xboole_0 != A_139 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_879])).

tff(c_34,plain,(
    ! [C_33] : r2_hidden(C_33,k1_tarski(C_33)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_100,plain,(
    ! [B_77,A_78] :
      ( ~ r2_hidden(B_77,A_78)
      | ~ v1_xboole_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_104,plain,(
    ! [C_33] : ~ v1_xboole_0(k1_tarski(C_33)) ),
    inference(resolution,[status(thm)],[c_34,c_100])).

tff(c_911,plain,(
    ! [C_33] : k1_tarski(C_33) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_903,c_104])).

tff(c_133,plain,(
    ! [A_87] :
      ( r2_hidden('#skF_3'(A_87),A_87)
      | k1_xboole_0 = A_87 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_32,plain,(
    ! [C_33,A_29] :
      ( C_33 = A_29
      | ~ r2_hidden(C_33,k1_tarski(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_141,plain,(
    ! [A_29] :
      ( '#skF_3'(k1_tarski(A_29)) = A_29
      | k1_tarski(A_29) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_133,c_32])).

tff(c_912,plain,(
    ! [A_29] : '#skF_3'(k1_tarski(A_29)) = A_29 ),
    inference(negUnitSimplification,[status(thm)],[c_911,c_141])).

tff(c_68,plain,(
    r1_tarski(k1_tarski('#skF_6'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1064,plain,(
    ! [B_148,A_149] :
      ( k1_tarski(B_148) = A_149
      | k1_xboole_0 = A_149
      | ~ r1_tarski(A_149,k1_tarski(B_148)) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1070,plain,
    ( k1_tarski('#skF_7') = k1_tarski('#skF_6')
    | k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_68,c_1064])).

tff(c_1080,plain,(
    k1_tarski('#skF_7') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_911,c_1070])).

tff(c_1100,plain,(
    '#skF_3'(k1_tarski('#skF_6')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_1080,c_912])).

tff(c_1125,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_912,c_1100])).

tff(c_1127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1125])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:34:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.45  
% 2.70/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.45  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_3 > #skF_2 > #skF_5 > #skF_4
% 2.70/1.45  
% 2.70/1.45  %Foreground sorts:
% 2.70/1.45  
% 2.70/1.45  
% 2.70/1.45  %Background operators:
% 2.70/1.45  
% 2.70/1.45  
% 2.70/1.45  %Foreground operators:
% 2.70/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.70/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.70/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.70/1.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.70/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.70/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.70/1.45  tff('#skF_7', type, '#skF_7': $i).
% 2.70/1.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.70/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.70/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.70/1.45  tff('#skF_6', type, '#skF_6': $i).
% 2.70/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.70/1.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.70/1.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.70/1.45  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.70/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.45  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.70/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.70/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.70/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.70/1.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.70/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.70/1.45  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.70/1.45  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.70/1.45  
% 2.97/1.46  tff(f_111, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.97/1.46  tff(f_71, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.97/1.46  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.97/1.46  tff(f_59, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.97/1.46  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.97/1.46  tff(f_75, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.97/1.46  tff(f_67, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.97/1.46  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.97/1.46  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.97/1.46  tff(f_84, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.97/1.46  tff(f_106, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.97/1.46  tff(c_66, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.97/1.46  tff(c_24, plain, (![A_23, B_24]: (r1_xboole_0(k4_xboole_0(A_23, B_24), B_24))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.97/1.46  tff(c_106, plain, (![B_80, A_81]: (r1_xboole_0(B_80, A_81) | ~r1_xboole_0(A_81, B_80))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.97/1.46  tff(c_109, plain, (![B_24, A_23]: (r1_xboole_0(B_24, k4_xboole_0(A_23, B_24)))), inference(resolution, [status(thm)], [c_24, c_106])).
% 2.97/1.46  tff(c_14, plain, (![A_14]: (r2_hidden('#skF_3'(A_14), A_14) | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.97/1.46  tff(c_242, plain, (![A_102, B_103, C_104]: (~r1_xboole_0(A_102, B_103) | ~r2_hidden(C_104, k3_xboole_0(A_102, B_103)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.97/1.46  tff(c_276, plain, (![A_109, B_110]: (~r1_xboole_0(A_109, B_110) | k3_xboole_0(A_109, B_110)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_242])).
% 2.97/1.46  tff(c_291, plain, (![B_24, A_23]: (k3_xboole_0(B_24, k4_xboole_0(A_23, B_24))=k1_xboole_0)), inference(resolution, [status(thm)], [c_109, c_276])).
% 2.97/1.46  tff(c_192, plain, (![A_97, B_98]: (k4_xboole_0(A_97, B_98)=A_97 | ~r1_xboole_0(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.97/1.46  tff(c_203, plain, (![B_24, A_23]: (k4_xboole_0(B_24, k4_xboole_0(A_23, B_24))=B_24)), inference(resolution, [status(thm)], [c_109, c_192])).
% 2.97/1.46  tff(c_349, plain, (![A_116, B_117]: (k4_xboole_0(A_116, k4_xboole_0(A_116, B_117))=k3_xboole_0(A_116, B_117))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.97/1.46  tff(c_383, plain, (![B_24, A_23]: (k3_xboole_0(B_24, k4_xboole_0(A_23, B_24))=k4_xboole_0(B_24, B_24))), inference(superposition, [status(thm), theory('equality')], [c_203, c_349])).
% 2.97/1.46  tff(c_391, plain, (![B_24]: (k4_xboole_0(B_24, B_24)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_291, c_383])).
% 2.97/1.46  tff(c_158, plain, (![A_90, B_91]: (r1_xboole_0(A_90, B_91) | k4_xboole_0(A_90, B_91)!=A_90)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.97/1.46  tff(c_8, plain, (![B_8, A_7]: (r1_xboole_0(B_8, A_7) | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.97/1.46  tff(c_161, plain, (![B_91, A_90]: (r1_xboole_0(B_91, A_90) | k4_xboole_0(A_90, B_91)!=A_90)), inference(resolution, [status(thm)], [c_158, c_8])).
% 2.97/1.46  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.97/1.46  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.97/1.46  tff(c_835, plain, (![A_133, B_134]: (~r1_xboole_0(A_133, B_134) | v1_xboole_0(k3_xboole_0(A_133, B_134)))), inference(resolution, [status(thm)], [c_4, c_242])).
% 2.97/1.46  tff(c_867, plain, (![A_135]: (~r1_xboole_0(A_135, A_135) | v1_xboole_0(A_135))), inference(superposition, [status(thm), theory('equality')], [c_6, c_835])).
% 2.97/1.46  tff(c_879, plain, (![A_90]: (v1_xboole_0(A_90) | k4_xboole_0(A_90, A_90)!=A_90)), inference(resolution, [status(thm)], [c_161, c_867])).
% 2.97/1.46  tff(c_903, plain, (![A_139]: (v1_xboole_0(A_139) | k1_xboole_0!=A_139)), inference(demodulation, [status(thm), theory('equality')], [c_391, c_879])).
% 2.97/1.46  tff(c_34, plain, (![C_33]: (r2_hidden(C_33, k1_tarski(C_33)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.97/1.46  tff(c_100, plain, (![B_77, A_78]: (~r2_hidden(B_77, A_78) | ~v1_xboole_0(A_78))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.97/1.46  tff(c_104, plain, (![C_33]: (~v1_xboole_0(k1_tarski(C_33)))), inference(resolution, [status(thm)], [c_34, c_100])).
% 2.97/1.46  tff(c_911, plain, (![C_33]: (k1_tarski(C_33)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_903, c_104])).
% 2.97/1.46  tff(c_133, plain, (![A_87]: (r2_hidden('#skF_3'(A_87), A_87) | k1_xboole_0=A_87)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.97/1.46  tff(c_32, plain, (![C_33, A_29]: (C_33=A_29 | ~r2_hidden(C_33, k1_tarski(A_29)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.97/1.46  tff(c_141, plain, (![A_29]: ('#skF_3'(k1_tarski(A_29))=A_29 | k1_tarski(A_29)=k1_xboole_0)), inference(resolution, [status(thm)], [c_133, c_32])).
% 2.97/1.46  tff(c_912, plain, (![A_29]: ('#skF_3'(k1_tarski(A_29))=A_29)), inference(negUnitSimplification, [status(thm)], [c_911, c_141])).
% 2.97/1.46  tff(c_68, plain, (r1_tarski(k1_tarski('#skF_6'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.97/1.46  tff(c_1064, plain, (![B_148, A_149]: (k1_tarski(B_148)=A_149 | k1_xboole_0=A_149 | ~r1_tarski(A_149, k1_tarski(B_148)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.97/1.46  tff(c_1070, plain, (k1_tarski('#skF_7')=k1_tarski('#skF_6') | k1_tarski('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_68, c_1064])).
% 2.97/1.46  tff(c_1080, plain, (k1_tarski('#skF_7')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_911, c_1070])).
% 2.97/1.46  tff(c_1100, plain, ('#skF_3'(k1_tarski('#skF_6'))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_1080, c_912])).
% 2.97/1.46  tff(c_1125, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_912, c_1100])).
% 2.97/1.46  tff(c_1127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1125])).
% 2.97/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.46  
% 2.97/1.46  Inference rules
% 2.97/1.46  ----------------------
% 2.97/1.46  #Ref     : 0
% 2.97/1.46  #Sup     : 245
% 2.97/1.46  #Fact    : 0
% 2.97/1.46  #Define  : 0
% 2.97/1.46  #Split   : 1
% 2.97/1.46  #Chain   : 0
% 2.97/1.46  #Close   : 0
% 2.97/1.46  
% 2.97/1.46  Ordering : KBO
% 2.97/1.46  
% 2.97/1.46  Simplification rules
% 2.97/1.46  ----------------------
% 2.97/1.46  #Subsume      : 15
% 2.97/1.46  #Demod        : 134
% 2.97/1.46  #Tautology    : 166
% 2.97/1.46  #SimpNegUnit  : 9
% 2.97/1.46  #BackRed      : 6
% 2.97/1.46  
% 2.97/1.46  #Partial instantiations: 0
% 2.97/1.46  #Strategies tried      : 1
% 2.97/1.46  
% 2.97/1.46  Timing (in seconds)
% 2.97/1.46  ----------------------
% 2.97/1.47  Preprocessing        : 0.36
% 2.97/1.47  Parsing              : 0.19
% 2.97/1.47  CNF conversion       : 0.03
% 2.97/1.47  Main loop            : 0.32
% 2.97/1.47  Inferencing          : 0.12
% 2.97/1.47  Reduction            : 0.11
% 2.97/1.47  Demodulation         : 0.08
% 2.97/1.47  BG Simplification    : 0.02
% 2.97/1.47  Subsumption          : 0.05
% 2.97/1.47  Abstraction          : 0.02
% 2.97/1.47  MUC search           : 0.00
% 2.97/1.47  Cooper               : 0.00
% 2.97/1.47  Total                : 0.71
% 2.97/1.47  Index Insertion      : 0.00
% 2.97/1.47  Index Deletion       : 0.00
% 2.97/1.47  Index Matching       : 0.00
% 2.97/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
