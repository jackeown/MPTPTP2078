%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:21 EST 2020

% Result     : Theorem 5.17s
% Output     : CNFRefutation 5.17s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 122 expanded)
%              Number of leaves         :   36 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :  112 ( 253 expanded)
%              Number of equality atoms :   42 ( 178 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_129,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_79,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(c_62,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_73,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_60,plain,
    ( k1_xboole_0 != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_72,plain,(
    k1_tarski('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_66,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_80,plain,(
    ! [A_59,B_60] : r1_tarski(A_59,k2_xboole_0(A_59,B_60)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_83,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_80])).

tff(c_726,plain,(
    ! [B_144,A_145] :
      ( k1_tarski(B_144) = A_145
      | k1_xboole_0 = A_145
      | ~ r1_tarski(A_145,k1_tarski(B_144)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_741,plain,
    ( k1_tarski('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_83,c_726])).

tff(c_750,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_72,c_741])).

tff(c_751,plain,(
    k1_tarski('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_752,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_755,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_752,c_12])).

tff(c_913,plain,(
    ! [A_174,B_175] :
      ( r2_hidden('#skF_2'(A_174,B_175),A_174)
      | r1_tarski(A_174,B_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_919,plain,(
    ! [A_177,B_178] :
      ( ~ v1_xboole_0(A_177)
      | r1_tarski(A_177,B_178) ) ),
    inference(resolution,[status(thm)],[c_913,c_2])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( k2_xboole_0(A_12,B_13) = B_13
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_964,plain,(
    ! [A_187,B_188] :
      ( k2_xboole_0(A_187,B_188) = B_188
      | ~ v1_xboole_0(A_187) ) ),
    inference(resolution,[status(thm)],[c_919,c_16])).

tff(c_967,plain,(
    ! [B_188] : k2_xboole_0('#skF_4',B_188) = B_188 ),
    inference(resolution,[status(thm)],[c_755,c_964])).

tff(c_969,plain,(
    k1_tarski('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_967,c_66])).

tff(c_971,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_751,c_969])).

tff(c_973,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_64,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1007,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_973,c_973,c_64])).

tff(c_975,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_973,c_66])).

tff(c_1027,plain,(
    ! [A_199,B_200] :
      ( r1_xboole_0(k1_tarski(A_199),B_200)
      | r2_hidden(A_199,B_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( r1_xboole_0(B_11,A_10)
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1302,plain,(
    ! [B_223,A_224] :
      ( r1_xboole_0(B_223,k1_tarski(A_224))
      | r2_hidden(A_224,B_223) ) ),
    inference(resolution,[status(thm)],[c_1027,c_14])).

tff(c_1311,plain,(
    ! [B_223] :
      ( r1_xboole_0(B_223,'#skF_4')
      | r2_hidden('#skF_3',B_223) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_973,c_1302])).

tff(c_30,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2531,plain,(
    ! [A_337,B_338,C_339] :
      ( r1_tarski(k2_tarski(A_337,B_338),C_339)
      | ~ r2_hidden(B_338,C_339)
      | ~ r2_hidden(A_337,C_339) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_3767,plain,(
    ! [A_434,C_435] :
      ( r1_tarski(k1_tarski(A_434),C_435)
      | ~ r2_hidden(A_434,C_435)
      | ~ r2_hidden(A_434,C_435) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2531])).

tff(c_3803,plain,(
    ! [A_436,C_437] :
      ( k2_xboole_0(k1_tarski(A_436),C_437) = C_437
      | ~ r2_hidden(A_436,C_437) ) ),
    inference(resolution,[status(thm)],[c_3767,c_16])).

tff(c_28,plain,(
    ! [A_18,B_19] : r1_tarski(A_18,k2_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_3960,plain,(
    ! [A_438,C_439] :
      ( r1_tarski(k1_tarski(A_438),C_439)
      | ~ r2_hidden(A_438,C_439) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3803,c_28])).

tff(c_3996,plain,(
    ! [C_440] :
      ( r1_tarski('#skF_4',C_440)
      | ~ r2_hidden('#skF_3',C_440) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_973,c_3960])).

tff(c_4324,plain,(
    ! [B_445] :
      ( r1_tarski('#skF_4',B_445)
      | r1_xboole_0(B_445,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1311,c_3996])).

tff(c_972,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1154,plain,(
    ! [A_212,C_213,B_214] :
      ( r1_xboole_0(A_212,C_213)
      | ~ r1_xboole_0(A_212,k2_xboole_0(B_214,C_213)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1216,plain,(
    ! [A_216] :
      ( r1_xboole_0(A_216,'#skF_5')
      | ~ r1_xboole_0(A_216,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_975,c_1154])).

tff(c_20,plain,(
    ! [A_14] :
      ( ~ r1_xboole_0(A_14,A_14)
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1222,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1216,c_20])).

tff(c_1226,plain,(
    ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_972,c_1222])).

tff(c_4343,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_4324,c_1226])).

tff(c_4362,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_4343,c_16])).

tff(c_4372,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_975,c_4362])).

tff(c_4374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1007,c_4372])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:09:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.17/2.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.17/2.09  
% 5.17/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.17/2.09  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 5.17/2.09  
% 5.17/2.09  %Foreground sorts:
% 5.17/2.09  
% 5.17/2.09  
% 5.17/2.09  %Background operators:
% 5.17/2.09  
% 5.17/2.09  
% 5.17/2.09  %Foreground operators:
% 5.17/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.17/2.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.17/2.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.17/2.09  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.17/2.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.17/2.09  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.17/2.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.17/2.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.17/2.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.17/2.09  tff('#skF_5', type, '#skF_5': $i).
% 5.17/2.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.17/2.09  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.17/2.09  tff('#skF_3', type, '#skF_3': $i).
% 5.17/2.09  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.17/2.09  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.17/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.17/2.09  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.17/2.09  tff('#skF_4', type, '#skF_4': $i).
% 5.17/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.17/2.09  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.17/2.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.17/2.09  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.17/2.09  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.17/2.09  
% 5.17/2.11  tff(f_129, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 5.17/2.11  tff(f_77, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.17/2.11  tff(f_102, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 5.17/2.11  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.17/2.11  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.17/2.11  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.17/2.11  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.17/2.11  tff(f_96, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 5.17/2.11  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 5.17/2.11  tff(f_79, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.17/2.11  tff(f_110, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 5.17/2.11  tff(f_75, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 5.17/2.11  tff(f_59, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 5.17/2.11  tff(c_62, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.17/2.11  tff(c_73, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_62])).
% 5.17/2.11  tff(c_60, plain, (k1_xboole_0!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.17/2.11  tff(c_72, plain, (k1_tarski('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_60])).
% 5.17/2.11  tff(c_66, plain, (k2_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.17/2.11  tff(c_80, plain, (![A_59, B_60]: (r1_tarski(A_59, k2_xboole_0(A_59, B_60)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.17/2.11  tff(c_83, plain, (r1_tarski('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_80])).
% 5.17/2.11  tff(c_726, plain, (![B_144, A_145]: (k1_tarski(B_144)=A_145 | k1_xboole_0=A_145 | ~r1_tarski(A_145, k1_tarski(B_144)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.17/2.11  tff(c_741, plain, (k1_tarski('#skF_3')='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_83, c_726])).
% 5.17/2.11  tff(c_750, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_72, c_741])).
% 5.17/2.11  tff(c_751, plain, (k1_tarski('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_62])).
% 5.17/2.11  tff(c_752, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_62])).
% 5.17/2.11  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.17/2.11  tff(c_755, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_752, c_12])).
% 5.17/2.11  tff(c_913, plain, (![A_174, B_175]: (r2_hidden('#skF_2'(A_174, B_175), A_174) | r1_tarski(A_174, B_175))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.17/2.11  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.17/2.11  tff(c_919, plain, (![A_177, B_178]: (~v1_xboole_0(A_177) | r1_tarski(A_177, B_178))), inference(resolution, [status(thm)], [c_913, c_2])).
% 5.17/2.11  tff(c_16, plain, (![A_12, B_13]: (k2_xboole_0(A_12, B_13)=B_13 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.17/2.11  tff(c_964, plain, (![A_187, B_188]: (k2_xboole_0(A_187, B_188)=B_188 | ~v1_xboole_0(A_187))), inference(resolution, [status(thm)], [c_919, c_16])).
% 5.17/2.11  tff(c_967, plain, (![B_188]: (k2_xboole_0('#skF_4', B_188)=B_188)), inference(resolution, [status(thm)], [c_755, c_964])).
% 5.17/2.11  tff(c_969, plain, (k1_tarski('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_967, c_66])).
% 5.17/2.11  tff(c_971, plain, $false, inference(negUnitSimplification, [status(thm)], [c_751, c_969])).
% 5.17/2.11  tff(c_973, plain, (k1_tarski('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_60])).
% 5.17/2.11  tff(c_64, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.17/2.11  tff(c_1007, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_973, c_973, c_64])).
% 5.17/2.11  tff(c_975, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_973, c_66])).
% 5.17/2.11  tff(c_1027, plain, (![A_199, B_200]: (r1_xboole_0(k1_tarski(A_199), B_200) | r2_hidden(A_199, B_200))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.17/2.11  tff(c_14, plain, (![B_11, A_10]: (r1_xboole_0(B_11, A_10) | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.17/2.11  tff(c_1302, plain, (![B_223, A_224]: (r1_xboole_0(B_223, k1_tarski(A_224)) | r2_hidden(A_224, B_223))), inference(resolution, [status(thm)], [c_1027, c_14])).
% 5.17/2.11  tff(c_1311, plain, (![B_223]: (r1_xboole_0(B_223, '#skF_4') | r2_hidden('#skF_3', B_223))), inference(superposition, [status(thm), theory('equality')], [c_973, c_1302])).
% 5.17/2.11  tff(c_30, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.17/2.11  tff(c_2531, plain, (![A_337, B_338, C_339]: (r1_tarski(k2_tarski(A_337, B_338), C_339) | ~r2_hidden(B_338, C_339) | ~r2_hidden(A_337, C_339))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.17/2.11  tff(c_3767, plain, (![A_434, C_435]: (r1_tarski(k1_tarski(A_434), C_435) | ~r2_hidden(A_434, C_435) | ~r2_hidden(A_434, C_435))), inference(superposition, [status(thm), theory('equality')], [c_30, c_2531])).
% 5.17/2.11  tff(c_3803, plain, (![A_436, C_437]: (k2_xboole_0(k1_tarski(A_436), C_437)=C_437 | ~r2_hidden(A_436, C_437))), inference(resolution, [status(thm)], [c_3767, c_16])).
% 5.17/2.11  tff(c_28, plain, (![A_18, B_19]: (r1_tarski(A_18, k2_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.17/2.11  tff(c_3960, plain, (![A_438, C_439]: (r1_tarski(k1_tarski(A_438), C_439) | ~r2_hidden(A_438, C_439))), inference(superposition, [status(thm), theory('equality')], [c_3803, c_28])).
% 5.17/2.11  tff(c_3996, plain, (![C_440]: (r1_tarski('#skF_4', C_440) | ~r2_hidden('#skF_3', C_440))), inference(superposition, [status(thm), theory('equality')], [c_973, c_3960])).
% 5.17/2.11  tff(c_4324, plain, (![B_445]: (r1_tarski('#skF_4', B_445) | r1_xboole_0(B_445, '#skF_4'))), inference(resolution, [status(thm)], [c_1311, c_3996])).
% 5.17/2.11  tff(c_972, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_60])).
% 5.17/2.11  tff(c_1154, plain, (![A_212, C_213, B_214]: (r1_xboole_0(A_212, C_213) | ~r1_xboole_0(A_212, k2_xboole_0(B_214, C_213)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.17/2.11  tff(c_1216, plain, (![A_216]: (r1_xboole_0(A_216, '#skF_5') | ~r1_xboole_0(A_216, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_975, c_1154])).
% 5.17/2.11  tff(c_20, plain, (![A_14]: (~r1_xboole_0(A_14, A_14) | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.17/2.11  tff(c_1222, plain, (k1_xboole_0='#skF_5' | ~r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1216, c_20])).
% 5.17/2.11  tff(c_1226, plain, (~r1_xboole_0('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_972, c_1222])).
% 5.17/2.11  tff(c_4343, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_4324, c_1226])).
% 5.17/2.11  tff(c_4362, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_4343, c_16])).
% 5.17/2.11  tff(c_4372, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_975, c_4362])).
% 5.17/2.11  tff(c_4374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1007, c_4372])).
% 5.17/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.17/2.11  
% 5.17/2.11  Inference rules
% 5.17/2.11  ----------------------
% 5.17/2.11  #Ref     : 0
% 5.17/2.11  #Sup     : 1026
% 5.17/2.11  #Fact    : 0
% 5.17/2.11  #Define  : 0
% 5.17/2.11  #Split   : 10
% 5.17/2.11  #Chain   : 0
% 5.17/2.11  #Close   : 0
% 5.17/2.11  
% 5.17/2.11  Ordering : KBO
% 5.17/2.11  
% 5.17/2.11  Simplification rules
% 5.17/2.11  ----------------------
% 5.17/2.11  #Subsume      : 407
% 5.17/2.11  #Demod        : 301
% 5.17/2.11  #Tautology    : 388
% 5.17/2.11  #SimpNegUnit  : 33
% 5.17/2.11  #BackRed      : 21
% 5.17/2.11  
% 5.17/2.11  #Partial instantiations: 0
% 5.17/2.11  #Strategies tried      : 1
% 5.17/2.11  
% 5.17/2.11  Timing (in seconds)
% 5.17/2.11  ----------------------
% 5.17/2.11  Preprocessing        : 0.44
% 5.17/2.11  Parsing              : 0.24
% 5.17/2.11  CNF conversion       : 0.03
% 5.17/2.11  Main loop            : 0.84
% 5.17/2.11  Inferencing          : 0.30
% 5.17/2.11  Reduction            : 0.26
% 5.30/2.11  Demodulation         : 0.18
% 5.30/2.11  BG Simplification    : 0.03
% 5.30/2.11  Subsumption          : 0.16
% 5.30/2.11  Abstraction          : 0.03
% 5.30/2.11  MUC search           : 0.00
% 5.30/2.11  Cooper               : 0.00
% 5.30/2.11  Total                : 1.31
% 5.30/2.11  Index Insertion      : 0.00
% 5.30/2.11  Index Deletion       : 0.00
% 5.30/2.11  Index Matching       : 0.00
% 5.30/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
