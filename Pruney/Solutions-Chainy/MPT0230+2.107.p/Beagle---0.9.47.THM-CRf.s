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
% DateTime   : Thu Dec  3 09:49:09 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   67 (  80 expanded)
%              Number of leaves         :   34 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :   74 (  97 expanded)
%              Number of equality atoms :   45 (  64 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_70,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_72,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_47,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(c_62,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_60,plain,(
    '#skF_6' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_42,plain,(
    ! [A_23] : k2_tarski(A_23,A_23) = k1_tarski(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_105,plain,(
    ! [A_61,B_62] : k1_enumset1(A_61,A_61,B_62) = k2_tarski(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20,plain,(
    ! [E_22,A_16,B_17] : r2_hidden(E_22,k1_enumset1(A_16,B_17,E_22)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_123,plain,(
    ! [B_63,A_64] : r2_hidden(B_63,k2_tarski(A_64,B_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_20])).

tff(c_126,plain,(
    ! [A_23] : r2_hidden(A_23,k1_tarski(A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_123])).

tff(c_12,plain,(
    ! [A_10,B_11] : k3_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_128,plain,(
    ! [A_66,B_67,C_68] :
      ( ~ r1_xboole_0(A_66,B_67)
      | ~ r2_hidden(C_68,k3_xboole_0(A_66,B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_168,plain,(
    ! [A_74,B_75,C_76] :
      ( ~ r1_xboole_0(A_74,k2_xboole_0(A_74,B_75))
      | ~ r2_hidden(C_76,A_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_128])).

tff(c_171,plain,(
    ! [C_76,A_1,B_75] :
      ( ~ r2_hidden(C_76,A_1)
      | k3_xboole_0(A_1,k2_xboole_0(A_1,B_75)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_168])).

tff(c_175,plain,(
    ! [C_77,A_78] :
      ( ~ r2_hidden(C_77,A_78)
      | k1_xboole_0 != A_78 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_171])).

tff(c_195,plain,(
    ! [A_23] : k1_tarski(A_23) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_126,c_175])).

tff(c_16,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k2_xboole_0(A_14,B_15)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_138,plain,(
    ! [A_71,B_72] : k5_xboole_0(A_71,k3_xboole_0(A_71,B_72)) = k4_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_147,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = k5_xboole_0(A_10,A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_138])).

tff(c_150,plain,(
    ! [A_10] : k5_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_147])).

tff(c_64,plain,(
    r1_tarski(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_94,plain,(
    ! [A_55,B_56] :
      ( k3_xboole_0(A_55,B_56) = A_55
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_98,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6')) = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_94])).

tff(c_10,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_154,plain,(
    k5_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) = k4_xboole_0(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_10])).

tff(c_276,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_154])).

tff(c_56,plain,(
    ! [B_39,C_40] :
      ( k4_xboole_0(k2_tarski(B_39,B_39),C_40) = k1_tarski(B_39)
      | r2_hidden(B_39,C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_65,plain,(
    ! [B_39,C_40] :
      ( k4_xboole_0(k1_tarski(B_39),C_40) = k1_tarski(B_39)
      | r2_hidden(B_39,C_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_56])).

tff(c_280,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | r2_hidden('#skF_4',k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_65])).

tff(c_286,plain,(
    r2_hidden('#skF_4',k2_tarski('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_280])).

tff(c_44,plain,(
    ! [A_24,B_25] : k1_enumset1(A_24,A_24,B_25) = k2_tarski(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_319,plain,(
    ! [E_105,C_106,B_107,A_108] :
      ( E_105 = C_106
      | E_105 = B_107
      | E_105 = A_108
      | ~ r2_hidden(E_105,k1_enumset1(A_108,B_107,C_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_347,plain,(
    ! [E_112,B_113,A_114] :
      ( E_112 = B_113
      | E_112 = A_114
      | E_112 = A_114
      | ~ r2_hidden(E_112,k2_tarski(A_114,B_113)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_319])).

tff(c_350,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_286,c_347])).

tff(c_363,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_62,c_60,c_350])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:30:10 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.48  
% 2.47/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.48  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.47/1.48  
% 2.47/1.48  %Foreground sorts:
% 2.47/1.48  
% 2.47/1.48  
% 2.47/1.48  %Background operators:
% 2.47/1.48  
% 2.47/1.48  
% 2.47/1.48  %Foreground operators:
% 2.47/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.47/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.47/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.47/1.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.47/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.47/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.47/1.48  tff('#skF_5', type, '#skF_5': $i).
% 2.47/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.47/1.48  tff('#skF_6', type, '#skF_6': $i).
% 2.47/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.47/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.47/1.48  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.47/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.48  tff('#skF_4', type, '#skF_4': $i).
% 2.47/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.47/1.48  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.47/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.47/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.47/1.48  
% 2.47/1.50  tff(f_97, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.47/1.50  tff(f_70, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.47/1.50  tff(f_72, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.47/1.50  tff(f_68, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.47/1.50  tff(f_47, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.47/1.50  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.47/1.50  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.47/1.50  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.47/1.50  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.47/1.50  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.47/1.50  tff(f_87, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 2.47/1.50  tff(c_62, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.47/1.50  tff(c_60, plain, ('#skF_6'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.47/1.50  tff(c_42, plain, (![A_23]: (k2_tarski(A_23, A_23)=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.47/1.50  tff(c_105, plain, (![A_61, B_62]: (k1_enumset1(A_61, A_61, B_62)=k2_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.47/1.50  tff(c_20, plain, (![E_22, A_16, B_17]: (r2_hidden(E_22, k1_enumset1(A_16, B_17, E_22)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.47/1.50  tff(c_123, plain, (![B_63, A_64]: (r2_hidden(B_63, k2_tarski(A_64, B_63)))), inference(superposition, [status(thm), theory('equality')], [c_105, c_20])).
% 2.47/1.50  tff(c_126, plain, (![A_23]: (r2_hidden(A_23, k1_tarski(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_123])).
% 2.47/1.50  tff(c_12, plain, (![A_10, B_11]: (k3_xboole_0(A_10, k2_xboole_0(A_10, B_11))=A_10)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.47/1.50  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.47/1.50  tff(c_128, plain, (![A_66, B_67, C_68]: (~r1_xboole_0(A_66, B_67) | ~r2_hidden(C_68, k3_xboole_0(A_66, B_67)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.47/1.50  tff(c_168, plain, (![A_74, B_75, C_76]: (~r1_xboole_0(A_74, k2_xboole_0(A_74, B_75)) | ~r2_hidden(C_76, A_74))), inference(superposition, [status(thm), theory('equality')], [c_12, c_128])).
% 2.47/1.50  tff(c_171, plain, (![C_76, A_1, B_75]: (~r2_hidden(C_76, A_1) | k3_xboole_0(A_1, k2_xboole_0(A_1, B_75))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_168])).
% 2.47/1.50  tff(c_175, plain, (![C_77, A_78]: (~r2_hidden(C_77, A_78) | k1_xboole_0!=A_78)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_171])).
% 2.47/1.50  tff(c_195, plain, (![A_23]: (k1_tarski(A_23)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_126, c_175])).
% 2.47/1.50  tff(c_16, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k2_xboole_0(A_14, B_15))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.47/1.50  tff(c_138, plain, (![A_71, B_72]: (k5_xboole_0(A_71, k3_xboole_0(A_71, B_72))=k4_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.47/1.50  tff(c_147, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k2_xboole_0(A_10, B_11))=k5_xboole_0(A_10, A_10))), inference(superposition, [status(thm), theory('equality')], [c_12, c_138])).
% 2.47/1.50  tff(c_150, plain, (![A_10]: (k5_xboole_0(A_10, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_147])).
% 2.47/1.50  tff(c_64, plain, (r1_tarski(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.47/1.50  tff(c_94, plain, (![A_55, B_56]: (k3_xboole_0(A_55, B_56)=A_55 | ~r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.47/1.50  tff(c_98, plain, (k3_xboole_0(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6'))=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_64, c_94])).
% 2.47/1.50  tff(c_10, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.47/1.50  tff(c_154, plain, (k5_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))=k4_xboole_0(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_98, c_10])).
% 2.47/1.50  tff(c_276, plain, (k4_xboole_0(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_150, c_154])).
% 2.47/1.50  tff(c_56, plain, (![B_39, C_40]: (k4_xboole_0(k2_tarski(B_39, B_39), C_40)=k1_tarski(B_39) | r2_hidden(B_39, C_40))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.47/1.50  tff(c_65, plain, (![B_39, C_40]: (k4_xboole_0(k1_tarski(B_39), C_40)=k1_tarski(B_39) | r2_hidden(B_39, C_40))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_56])).
% 2.47/1.50  tff(c_280, plain, (k1_tarski('#skF_4')=k1_xboole_0 | r2_hidden('#skF_4', k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_276, c_65])).
% 2.47/1.50  tff(c_286, plain, (r2_hidden('#skF_4', k2_tarski('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_195, c_280])).
% 2.47/1.50  tff(c_44, plain, (![A_24, B_25]: (k1_enumset1(A_24, A_24, B_25)=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.47/1.50  tff(c_319, plain, (![E_105, C_106, B_107, A_108]: (E_105=C_106 | E_105=B_107 | E_105=A_108 | ~r2_hidden(E_105, k1_enumset1(A_108, B_107, C_106)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.47/1.50  tff(c_347, plain, (![E_112, B_113, A_114]: (E_112=B_113 | E_112=A_114 | E_112=A_114 | ~r2_hidden(E_112, k2_tarski(A_114, B_113)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_319])).
% 2.47/1.50  tff(c_350, plain, ('#skF_6'='#skF_4' | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_286, c_347])).
% 2.47/1.50  tff(c_363, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_62, c_60, c_350])).
% 2.47/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.50  
% 2.47/1.50  Inference rules
% 2.47/1.50  ----------------------
% 2.47/1.50  #Ref     : 0
% 2.47/1.50  #Sup     : 69
% 2.47/1.50  #Fact    : 0
% 2.47/1.50  #Define  : 0
% 2.47/1.50  #Split   : 1
% 2.47/1.50  #Chain   : 0
% 2.47/1.50  #Close   : 0
% 2.47/1.50  
% 2.47/1.50  Ordering : KBO
% 2.47/1.50  
% 2.47/1.50  Simplification rules
% 2.47/1.50  ----------------------
% 2.47/1.50  #Subsume      : 13
% 2.47/1.50  #Demod        : 11
% 2.47/1.50  #Tautology    : 33
% 2.47/1.50  #SimpNegUnit  : 6
% 2.47/1.50  #BackRed      : 0
% 2.47/1.50  
% 2.47/1.50  #Partial instantiations: 0
% 2.47/1.50  #Strategies tried      : 1
% 2.47/1.50  
% 2.47/1.50  Timing (in seconds)
% 2.47/1.50  ----------------------
% 2.65/1.50  Preprocessing        : 0.42
% 2.65/1.50  Parsing              : 0.24
% 2.65/1.50  CNF conversion       : 0.03
% 2.65/1.50  Main loop            : 0.22
% 2.65/1.50  Inferencing          : 0.08
% 2.65/1.50  Reduction            : 0.08
% 2.65/1.50  Demodulation         : 0.05
% 2.65/1.50  BG Simplification    : 0.02
% 2.65/1.50  Subsumption          : 0.04
% 2.65/1.50  Abstraction          : 0.01
% 2.65/1.50  MUC search           : 0.00
% 2.65/1.50  Cooper               : 0.00
% 2.65/1.50  Total                : 0.68
% 2.65/1.50  Index Insertion      : 0.00
% 2.65/1.50  Index Deletion       : 0.00
% 2.65/1.50  Index Matching       : 0.00
% 2.65/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
