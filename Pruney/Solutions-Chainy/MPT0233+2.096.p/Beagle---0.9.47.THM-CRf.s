%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:33 EST 2020

% Result     : Theorem 4.55s
% Output     : CNFRefutation 4.55s
% Verified   : 
% Statistics : Number of formulae       :   73 (  94 expanded)
%              Number of leaves         :   36 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :   89 ( 135 expanded)
%              Number of equality atoms :   33 (  50 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_72,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_74,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(c_68,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_66,plain,(
    '#skF_5' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_54,plain,(
    ! [A_52,B_53] :
      ( r1_xboole_0(k1_tarski(A_52),B_53)
      | r2_hidden(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_226,plain,(
    ! [A_97,B_98,C_99] :
      ( ~ r1_xboole_0(A_97,B_98)
      | ~ r2_hidden(C_99,k3_xboole_0(A_97,B_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_277,plain,(
    ! [A_105,B_106] :
      ( ~ r1_xboole_0(A_105,B_106)
      | v1_xboole_0(k3_xboole_0(A_105,B_106)) ) ),
    inference(resolution,[status(thm)],[c_6,c_226])).

tff(c_289,plain,(
    ! [A_1,B_2] :
      ( ~ r1_xboole_0(A_1,B_2)
      | v1_xboole_0(k3_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_277])).

tff(c_385,plain,(
    ! [A_122,B_123] :
      ( r2_hidden('#skF_2'(A_122,B_123),k3_xboole_0(A_122,B_123))
      | r1_xboole_0(A_122,B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_418,plain,(
    ! [A_124,B_125] :
      ( ~ v1_xboole_0(k3_xboole_0(A_124,B_125))
      | r1_xboole_0(A_124,B_125) ) ),
    inference(resolution,[status(thm)],[c_385,c_4])).

tff(c_449,plain,(
    ! [B_126,A_127] :
      ( r1_xboole_0(B_126,A_127)
      | ~ r1_xboole_0(A_127,B_126) ) ),
    inference(resolution,[status(thm)],[c_289,c_418])).

tff(c_452,plain,(
    ! [B_53,A_52] :
      ( r1_xboole_0(B_53,k1_tarski(A_52))
      | r2_hidden(A_52,B_53) ) ),
    inference(resolution,[status(thm)],[c_54,c_449])).

tff(c_40,plain,(
    ! [A_24] : k2_tarski(A_24,A_24) = k1_tarski(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_159,plain,(
    ! [A_87,B_88] : k1_enumset1(A_87,A_87,B_88) = k2_tarski(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_85,plain,(
    ! [E_63,A_64,B_65] : r2_hidden(E_63,k1_enumset1(A_64,B_65,E_63)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_89,plain,(
    ! [A_64,B_65,E_63] : ~ v1_xboole_0(k1_enumset1(A_64,B_65,E_63)) ),
    inference(resolution,[status(thm)],[c_85,c_4])).

tff(c_208,plain,(
    ! [A_91,B_92] : ~ v1_xboole_0(k2_tarski(A_91,B_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_89])).

tff(c_210,plain,(
    ! [A_24] : ~ v1_xboole_0(k1_tarski(A_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_208])).

tff(c_62,plain,(
    ! [B_55,C_56] : r1_tarski(k1_tarski(B_55),k2_tarski(B_55,C_56)) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_70,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_179,plain,(
    ! [A_89,B_90] :
      ( k3_xboole_0(A_89,B_90) = A_89
      | ~ r1_tarski(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_205,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) = k2_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_179])).

tff(c_314,plain,(
    ! [A_110,B_111,C_112] :
      ( r1_tarski(A_110,B_111)
      | ~ r1_tarski(A_110,k3_xboole_0(B_111,C_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_609,plain,(
    ! [A_147,A_148,B_149] :
      ( r1_tarski(A_147,A_148)
      | ~ r1_tarski(A_147,k3_xboole_0(B_149,A_148)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_314])).

tff(c_734,plain,(
    ! [A_162] :
      ( r1_tarski(A_162,k2_tarski('#skF_7','#skF_8'))
      | ~ r1_tarski(A_162,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_609])).

tff(c_14,plain,(
    ! [A_15,B_16] :
      ( k3_xboole_0(A_15,B_16) = A_15
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_911,plain,(
    ! [A_176] :
      ( k3_xboole_0(A_176,k2_tarski('#skF_7','#skF_8')) = A_176
      | ~ r1_tarski(A_176,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_734,c_14])).

tff(c_935,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_911])).

tff(c_963,plain,
    ( ~ r1_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_tarski('#skF_5'))
    | v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_935,c_289])).

tff(c_975,plain,(
    ~ r1_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_tarski('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_210,c_963])).

tff(c_981,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_452,c_975])).

tff(c_42,plain,(
    ! [A_25,B_26] : k1_enumset1(A_25,A_25,B_26) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_636,plain,(
    ! [E_152,C_153,B_154,A_155] :
      ( E_152 = C_153
      | E_152 = B_154
      | E_152 = A_155
      | ~ r2_hidden(E_152,k1_enumset1(A_155,B_154,C_153)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2828,plain,(
    ! [E_280,B_281,A_282] :
      ( E_280 = B_281
      | E_280 = A_282
      | E_280 = A_282
      | ~ r2_hidden(E_280,k2_tarski(A_282,B_281)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_636])).

tff(c_2865,plain,
    ( '#skF_5' = '#skF_8'
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_981,c_2828])).

tff(c_2902,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_68,c_66,c_2865])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:55:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.55/1.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/1.87  
% 4.55/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/1.87  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_2 > #skF_3
% 4.55/1.87  
% 4.55/1.87  %Foreground sorts:
% 4.55/1.87  
% 4.55/1.87  
% 4.55/1.87  %Background operators:
% 4.55/1.87  
% 4.55/1.87  
% 4.55/1.87  %Foreground operators:
% 4.55/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.55/1.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.55/1.87  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.55/1.87  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.55/1.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.55/1.87  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.55/1.87  tff('#skF_7', type, '#skF_7': $i).
% 4.55/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.55/1.87  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.55/1.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.55/1.87  tff('#skF_5', type, '#skF_5': $i).
% 4.55/1.87  tff('#skF_6', type, '#skF_6': $i).
% 4.55/1.87  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.55/1.87  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.55/1.87  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.55/1.87  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 4.55/1.87  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.55/1.87  tff('#skF_8', type, '#skF_8': $i).
% 4.55/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.55/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.55/1.87  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.55/1.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.55/1.87  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.55/1.87  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.55/1.87  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.55/1.87  
% 4.55/1.88  tff(f_114, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 4.55/1.88  tff(f_89, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 4.55/1.88  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.55/1.88  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.55/1.88  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.55/1.88  tff(f_72, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.55/1.88  tff(f_74, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.55/1.88  tff(f_70, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 4.55/1.88  tff(f_104, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 4.55/1.88  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.55/1.88  tff(f_51, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 4.55/1.88  tff(c_68, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.55/1.88  tff(c_66, plain, ('#skF_5'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.55/1.88  tff(c_54, plain, (![A_52, B_53]: (r1_xboole_0(k1_tarski(A_52), B_53) | r2_hidden(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.55/1.88  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.55/1.88  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.55/1.88  tff(c_226, plain, (![A_97, B_98, C_99]: (~r1_xboole_0(A_97, B_98) | ~r2_hidden(C_99, k3_xboole_0(A_97, B_98)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.55/1.88  tff(c_277, plain, (![A_105, B_106]: (~r1_xboole_0(A_105, B_106) | v1_xboole_0(k3_xboole_0(A_105, B_106)))), inference(resolution, [status(thm)], [c_6, c_226])).
% 4.55/1.88  tff(c_289, plain, (![A_1, B_2]: (~r1_xboole_0(A_1, B_2) | v1_xboole_0(k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_277])).
% 4.55/1.88  tff(c_385, plain, (![A_122, B_123]: (r2_hidden('#skF_2'(A_122, B_123), k3_xboole_0(A_122, B_123)) | r1_xboole_0(A_122, B_123))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.55/1.88  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.55/1.88  tff(c_418, plain, (![A_124, B_125]: (~v1_xboole_0(k3_xboole_0(A_124, B_125)) | r1_xboole_0(A_124, B_125))), inference(resolution, [status(thm)], [c_385, c_4])).
% 4.55/1.88  tff(c_449, plain, (![B_126, A_127]: (r1_xboole_0(B_126, A_127) | ~r1_xboole_0(A_127, B_126))), inference(resolution, [status(thm)], [c_289, c_418])).
% 4.55/1.88  tff(c_452, plain, (![B_53, A_52]: (r1_xboole_0(B_53, k1_tarski(A_52)) | r2_hidden(A_52, B_53))), inference(resolution, [status(thm)], [c_54, c_449])).
% 4.55/1.88  tff(c_40, plain, (![A_24]: (k2_tarski(A_24, A_24)=k1_tarski(A_24))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.55/1.88  tff(c_159, plain, (![A_87, B_88]: (k1_enumset1(A_87, A_87, B_88)=k2_tarski(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.55/1.88  tff(c_85, plain, (![E_63, A_64, B_65]: (r2_hidden(E_63, k1_enumset1(A_64, B_65, E_63)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.55/1.88  tff(c_89, plain, (![A_64, B_65, E_63]: (~v1_xboole_0(k1_enumset1(A_64, B_65, E_63)))), inference(resolution, [status(thm)], [c_85, c_4])).
% 4.55/1.88  tff(c_208, plain, (![A_91, B_92]: (~v1_xboole_0(k2_tarski(A_91, B_92)))), inference(superposition, [status(thm), theory('equality')], [c_159, c_89])).
% 4.55/1.88  tff(c_210, plain, (![A_24]: (~v1_xboole_0(k1_tarski(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_208])).
% 4.55/1.88  tff(c_62, plain, (![B_55, C_56]: (r1_tarski(k1_tarski(B_55), k2_tarski(B_55, C_56)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.55/1.88  tff(c_70, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.55/1.88  tff(c_179, plain, (![A_89, B_90]: (k3_xboole_0(A_89, B_90)=A_89 | ~r1_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.55/1.88  tff(c_205, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))=k2_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_70, c_179])).
% 4.55/1.88  tff(c_314, plain, (![A_110, B_111, C_112]: (r1_tarski(A_110, B_111) | ~r1_tarski(A_110, k3_xboole_0(B_111, C_112)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.55/1.88  tff(c_609, plain, (![A_147, A_148, B_149]: (r1_tarski(A_147, A_148) | ~r1_tarski(A_147, k3_xboole_0(B_149, A_148)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_314])).
% 4.55/1.88  tff(c_734, plain, (![A_162]: (r1_tarski(A_162, k2_tarski('#skF_7', '#skF_8')) | ~r1_tarski(A_162, k2_tarski('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_205, c_609])).
% 4.55/1.88  tff(c_14, plain, (![A_15, B_16]: (k3_xboole_0(A_15, B_16)=A_15 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.55/1.88  tff(c_911, plain, (![A_176]: (k3_xboole_0(A_176, k2_tarski('#skF_7', '#skF_8'))=A_176 | ~r1_tarski(A_176, k2_tarski('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_734, c_14])).
% 4.55/1.88  tff(c_935, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_62, c_911])).
% 4.55/1.88  tff(c_963, plain, (~r1_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_tarski('#skF_5')) | v1_xboole_0(k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_935, c_289])).
% 4.55/1.88  tff(c_975, plain, (~r1_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_tarski('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_210, c_963])).
% 4.55/1.88  tff(c_981, plain, (r2_hidden('#skF_5', k2_tarski('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_452, c_975])).
% 4.55/1.88  tff(c_42, plain, (![A_25, B_26]: (k1_enumset1(A_25, A_25, B_26)=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.55/1.88  tff(c_636, plain, (![E_152, C_153, B_154, A_155]: (E_152=C_153 | E_152=B_154 | E_152=A_155 | ~r2_hidden(E_152, k1_enumset1(A_155, B_154, C_153)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.55/1.88  tff(c_2828, plain, (![E_280, B_281, A_282]: (E_280=B_281 | E_280=A_282 | E_280=A_282 | ~r2_hidden(E_280, k2_tarski(A_282, B_281)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_636])).
% 4.55/1.88  tff(c_2865, plain, ('#skF_5'='#skF_8' | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_981, c_2828])).
% 4.55/1.88  tff(c_2902, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_68, c_66, c_2865])).
% 4.55/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/1.88  
% 4.55/1.88  Inference rules
% 4.55/1.88  ----------------------
% 4.55/1.88  #Ref     : 0
% 4.55/1.88  #Sup     : 704
% 4.55/1.88  #Fact    : 0
% 4.55/1.88  #Define  : 0
% 4.55/1.88  #Split   : 5
% 4.55/1.88  #Chain   : 0
% 4.55/1.88  #Close   : 0
% 4.55/1.88  
% 4.55/1.88  Ordering : KBO
% 4.55/1.88  
% 4.55/1.88  Simplification rules
% 4.55/1.88  ----------------------
% 4.55/1.88  #Subsume      : 253
% 4.55/1.88  #Demod        : 227
% 4.55/1.88  #Tautology    : 249
% 4.55/1.88  #SimpNegUnit  : 98
% 4.55/1.88  #BackRed      : 17
% 4.55/1.88  
% 4.55/1.88  #Partial instantiations: 0
% 4.55/1.88  #Strategies tried      : 1
% 4.55/1.88  
% 4.55/1.88  Timing (in seconds)
% 4.55/1.88  ----------------------
% 4.55/1.89  Preprocessing        : 0.35
% 4.55/1.89  Parsing              : 0.17
% 4.55/1.89  CNF conversion       : 0.03
% 4.55/1.89  Main loop            : 0.76
% 4.55/1.89  Inferencing          : 0.24
% 4.55/1.89  Reduction            : 0.28
% 4.55/1.89  Demodulation         : 0.20
% 4.55/1.89  BG Simplification    : 0.03
% 4.55/1.89  Subsumption          : 0.15
% 4.55/1.89  Abstraction          : 0.04
% 4.55/1.89  MUC search           : 0.00
% 4.55/1.89  Cooper               : 0.00
% 4.55/1.89  Total                : 1.15
% 4.55/1.89  Index Insertion      : 0.00
% 4.55/1.89  Index Deletion       : 0.00
% 4.55/1.89  Index Matching       : 0.00
% 4.55/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
