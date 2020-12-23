%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:44 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   65 (  81 expanded)
%              Number of leaves         :   31 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   90 ( 130 expanded)
%              Number of equality atoms :   21 (  32 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_64,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_xboole_0(k2_relat_1(A),k1_relat_1(B))
           => k5_relat_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_relat_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_49,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_67,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(c_44,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2')
    | k7_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_88,plain,(
    k7_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_42,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_50,plain,
    ( k7_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_112,plain,(
    r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_50])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_115,plain,(
    r1_xboole_0('#skF_2',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_112,c_2])).

tff(c_22,plain,(
    ! [A_26] : v1_relat_1(k6_relat_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_32,plain,(
    ! [A_30] : k2_relat_1(k6_relat_1(A_30)) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_223,plain,(
    ! [A_79,B_80] :
      ( k5_relat_1(A_79,B_80) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(A_79),k1_relat_1(B_80))
      | ~ v1_relat_1(B_80)
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_226,plain,(
    ! [A_30,B_80] :
      ( k5_relat_1(k6_relat_1(A_30),B_80) = k1_xboole_0
      | ~ r1_xboole_0(A_30,k1_relat_1(B_80))
      | ~ v1_relat_1(B_80)
      | ~ v1_relat_1(k6_relat_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_223])).

tff(c_245,plain,(
    ! [A_81,B_82] :
      ( k5_relat_1(k6_relat_1(A_81),B_82) = k1_xboole_0
      | ~ r1_xboole_0(A_81,k1_relat_1(B_82))
      | ~ v1_relat_1(B_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_226])).

tff(c_248,plain,
    ( k5_relat_1(k6_relat_1('#skF_2'),'#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_115,c_245])).

tff(c_261,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_248])).

tff(c_40,plain,(
    ! [A_34,B_35] :
      ( k5_relat_1(k6_relat_1(A_34),B_35) = k7_relat_1(B_35,A_34)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_270,plain,
    ( k7_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_40])).

tff(c_277,plain,(
    k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_270])).

tff(c_279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_277])).

tff(c_280,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_297,plain,(
    ! [A_85,C_86,B_87] :
      ( ~ r2_hidden(A_85,C_86)
      | ~ r1_xboole_0(k2_tarski(A_85,B_87),C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_302,plain,(
    ! [A_85] : ~ r2_hidden(A_85,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_297])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_281,plain,(
    k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_431,plain,(
    ! [A_120,C_121,B_122] :
      ( r2_hidden(A_120,k1_relat_1(k7_relat_1(C_121,B_122)))
      | ~ r2_hidden(A_120,k1_relat_1(C_121))
      | ~ r2_hidden(A_120,B_122)
      | ~ v1_relat_1(C_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_440,plain,(
    ! [A_120] :
      ( r2_hidden(A_120,k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(A_120,k1_relat_1('#skF_3'))
      | ~ r2_hidden(A_120,'#skF_2')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_431])).

tff(c_444,plain,(
    ! [A_120] :
      ( r2_hidden(A_120,k1_xboole_0)
      | ~ r2_hidden(A_120,k1_relat_1('#skF_3'))
      | ~ r2_hidden(A_120,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_26,c_440])).

tff(c_446,plain,(
    ! [A_123] :
      ( ~ r2_hidden(A_123,k1_relat_1('#skF_3'))
      | ~ r2_hidden(A_123,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_302,c_444])).

tff(c_712,plain,(
    ! [A_135] :
      ( ~ r2_hidden('#skF_1'(A_135,k1_relat_1('#skF_3')),'#skF_2')
      | r1_xboole_0(A_135,k1_relat_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_6,c_446])).

tff(c_717,plain,(
    r1_xboole_0('#skF_2',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_712])).

tff(c_724,plain,(
    r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_717,c_2])).

tff(c_732,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_280,c_724])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:58:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.38  
% 2.56/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.38  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.56/1.38  
% 2.56/1.38  %Foreground sorts:
% 2.56/1.38  
% 2.56/1.38  
% 2.56/1.38  %Background operators:
% 2.56/1.38  
% 2.56/1.38  
% 2.56/1.38  %Foreground operators:
% 2.56/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.56/1.38  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.56/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.56/1.38  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.56/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.56/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.56/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.56/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.56/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.56/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.56/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.56/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.56/1.38  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.56/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.56/1.38  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.56/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.56/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.56/1.38  
% 2.76/1.39  tff(f_99, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 2.76/1.39  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.76/1.39  tff(f_64, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.76/1.39  tff(f_80, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.76/1.39  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k2_relat_1(A), k1_relat_1(B)) => (k5_relat_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_relat_1)).
% 2.76/1.39  tff(f_92, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.76/1.39  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.76/1.39  tff(f_49, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.76/1.39  tff(f_62, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.76/1.39  tff(f_67, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.76/1.39  tff(f_88, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 2.76/1.39  tff(c_44, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2') | k7_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.76/1.39  tff(c_88, plain, (k7_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_44])).
% 2.76/1.39  tff(c_42, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.76/1.39  tff(c_50, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.76/1.39  tff(c_112, plain, (r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_88, c_50])).
% 2.76/1.39  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.76/1.39  tff(c_115, plain, (r1_xboole_0('#skF_2', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_112, c_2])).
% 2.76/1.39  tff(c_22, plain, (![A_26]: (v1_relat_1(k6_relat_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.76/1.39  tff(c_32, plain, (![A_30]: (k2_relat_1(k6_relat_1(A_30))=A_30)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.76/1.39  tff(c_223, plain, (![A_79, B_80]: (k5_relat_1(A_79, B_80)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(A_79), k1_relat_1(B_80)) | ~v1_relat_1(B_80) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.76/1.39  tff(c_226, plain, (![A_30, B_80]: (k5_relat_1(k6_relat_1(A_30), B_80)=k1_xboole_0 | ~r1_xboole_0(A_30, k1_relat_1(B_80)) | ~v1_relat_1(B_80) | ~v1_relat_1(k6_relat_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_223])).
% 2.76/1.39  tff(c_245, plain, (![A_81, B_82]: (k5_relat_1(k6_relat_1(A_81), B_82)=k1_xboole_0 | ~r1_xboole_0(A_81, k1_relat_1(B_82)) | ~v1_relat_1(B_82))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_226])).
% 2.76/1.39  tff(c_248, plain, (k5_relat_1(k6_relat_1('#skF_2'), '#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_115, c_245])).
% 2.76/1.39  tff(c_261, plain, (k5_relat_1(k6_relat_1('#skF_2'), '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_248])).
% 2.76/1.39  tff(c_40, plain, (![A_34, B_35]: (k5_relat_1(k6_relat_1(A_34), B_35)=k7_relat_1(B_35, A_34) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.76/1.39  tff(c_270, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_261, c_40])).
% 2.76/1.39  tff(c_277, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_270])).
% 2.76/1.39  tff(c_279, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_277])).
% 2.76/1.39  tff(c_280, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 2.76/1.39  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.76/1.39  tff(c_6, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.76/1.39  tff(c_10, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.76/1.39  tff(c_297, plain, (![A_85, C_86, B_87]: (~r2_hidden(A_85, C_86) | ~r1_xboole_0(k2_tarski(A_85, B_87), C_86))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.76/1.39  tff(c_302, plain, (![A_85]: (~r2_hidden(A_85, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_297])).
% 2.76/1.39  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.76/1.39  tff(c_281, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_44])).
% 2.76/1.39  tff(c_431, plain, (![A_120, C_121, B_122]: (r2_hidden(A_120, k1_relat_1(k7_relat_1(C_121, B_122))) | ~r2_hidden(A_120, k1_relat_1(C_121)) | ~r2_hidden(A_120, B_122) | ~v1_relat_1(C_121))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.76/1.39  tff(c_440, plain, (![A_120]: (r2_hidden(A_120, k1_relat_1(k1_xboole_0)) | ~r2_hidden(A_120, k1_relat_1('#skF_3')) | ~r2_hidden(A_120, '#skF_2') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_281, c_431])).
% 2.76/1.40  tff(c_444, plain, (![A_120]: (r2_hidden(A_120, k1_xboole_0) | ~r2_hidden(A_120, k1_relat_1('#skF_3')) | ~r2_hidden(A_120, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_26, c_440])).
% 2.76/1.40  tff(c_446, plain, (![A_123]: (~r2_hidden(A_123, k1_relat_1('#skF_3')) | ~r2_hidden(A_123, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_302, c_444])).
% 2.76/1.40  tff(c_712, plain, (![A_135]: (~r2_hidden('#skF_1'(A_135, k1_relat_1('#skF_3')), '#skF_2') | r1_xboole_0(A_135, k1_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_6, c_446])).
% 2.76/1.40  tff(c_717, plain, (r1_xboole_0('#skF_2', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_8, c_712])).
% 2.76/1.40  tff(c_724, plain, (r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_717, c_2])).
% 2.76/1.40  tff(c_732, plain, $false, inference(negUnitSimplification, [status(thm)], [c_280, c_724])).
% 2.76/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.40  
% 2.76/1.40  Inference rules
% 2.76/1.40  ----------------------
% 2.76/1.40  #Ref     : 0
% 2.76/1.40  #Sup     : 137
% 2.76/1.40  #Fact    : 0
% 2.76/1.40  #Define  : 0
% 2.76/1.40  #Split   : 3
% 2.76/1.40  #Chain   : 0
% 2.76/1.40  #Close   : 0
% 2.76/1.40  
% 2.76/1.40  Ordering : KBO
% 2.76/1.40  
% 2.76/1.40  Simplification rules
% 2.76/1.40  ----------------------
% 2.76/1.40  #Subsume      : 28
% 2.76/1.40  #Demod        : 87
% 2.76/1.40  #Tautology    : 71
% 2.76/1.40  #SimpNegUnit  : 12
% 2.76/1.40  #BackRed      : 0
% 2.76/1.40  
% 2.76/1.40  #Partial instantiations: 0
% 2.76/1.40  #Strategies tried      : 1
% 2.76/1.40  
% 2.76/1.40  Timing (in seconds)
% 2.76/1.40  ----------------------
% 2.76/1.40  Preprocessing        : 0.29
% 2.76/1.40  Parsing              : 0.15
% 2.76/1.40  CNF conversion       : 0.02
% 2.76/1.40  Main loop            : 0.29
% 2.76/1.40  Inferencing          : 0.12
% 2.76/1.40  Reduction            : 0.09
% 2.76/1.40  Demodulation         : 0.06
% 2.76/1.40  BG Simplification    : 0.02
% 2.76/1.40  Subsumption          : 0.04
% 2.76/1.40  Abstraction          : 0.02
% 2.76/1.40  MUC search           : 0.00
% 2.76/1.40  Cooper               : 0.00
% 2.76/1.40  Total                : 0.61
% 2.76/1.40  Index Insertion      : 0.00
% 2.76/1.40  Index Deletion       : 0.00
% 2.76/1.40  Index Matching       : 0.00
% 2.76/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
