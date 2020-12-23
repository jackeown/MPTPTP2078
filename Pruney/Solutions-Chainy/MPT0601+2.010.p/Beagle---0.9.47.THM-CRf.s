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
% DateTime   : Thu Dec  3 10:02:15 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   72 (  95 expanded)
%              Number of leaves         :   41 (  52 expanded)
%              Depth                    :    7
%              Number of atoms          :   86 ( 140 expanded)
%              Number of equality atoms :   29 (  43 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_6 > #skF_11 > #skF_1 > #skF_8 > #skF_3 > #skF_10 > #skF_7 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_48,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k1_relat_1(B))
          & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).

tff(c_52,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_54,plain,
    ( k11_relat_1('#skF_11','#skF_10') = k1_xboole_0
    | ~ r2_hidden('#skF_10',k1_relat_1('#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_97,plain,(
    ~ r2_hidden('#skF_10',k1_relat_1('#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_60,plain,
    ( r2_hidden('#skF_10',k1_relat_1('#skF_11'))
    | k11_relat_1('#skF_11','#skF_10') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_103,plain,(
    k11_relat_1('#skF_11','#skF_10') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_60])).

tff(c_30,plain,(
    ! [A_37] :
      ( r2_hidden('#skF_1'(A_37),A_37)
      | v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_144,plain,(
    ! [A_115,B_116,C_117] :
      ( r2_hidden(k4_tarski(A_115,B_116),C_117)
      | ~ r2_hidden(B_116,k11_relat_1(C_117,A_115))
      | ~ v1_relat_1(C_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_34,plain,(
    ! [C_70,A_55,D_73] :
      ( r2_hidden(C_70,k1_relat_1(A_55))
      | ~ r2_hidden(k4_tarski(C_70,D_73),A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_153,plain,(
    ! [A_118,C_119,B_120] :
      ( r2_hidden(A_118,k1_relat_1(C_119))
      | ~ r2_hidden(B_120,k11_relat_1(C_119,A_118))
      | ~ v1_relat_1(C_119) ) ),
    inference(resolution,[status(thm)],[c_144,c_34])).

tff(c_169,plain,(
    ! [A_121,C_122] :
      ( r2_hidden(A_121,k1_relat_1(C_122))
      | ~ v1_relat_1(C_122)
      | v1_relat_1(k11_relat_1(C_122,A_121)) ) ),
    inference(resolution,[status(thm)],[c_30,c_153])).

tff(c_180,plain,
    ( ~ v1_relat_1('#skF_11')
    | v1_relat_1(k11_relat_1('#skF_11','#skF_10')) ),
    inference(resolution,[status(thm)],[c_169,c_97])).

tff(c_185,plain,(
    v1_relat_1(k11_relat_1('#skF_11','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_180])).

tff(c_50,plain,(
    ! [A_79] :
      ( k1_xboole_0 = A_79
      | r2_hidden(k4_tarski('#skF_8'(A_79),'#skF_9'(A_79)),A_79)
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_429,plain,(
    ! [A_173,C_174] :
      ( r2_hidden(A_173,k1_relat_1(C_174))
      | ~ v1_relat_1(C_174)
      | k11_relat_1(C_174,A_173) = k1_xboole_0
      | ~ v1_relat_1(k11_relat_1(C_174,A_173)) ) ),
    inference(resolution,[status(thm)],[c_50,c_153])).

tff(c_455,plain,
    ( ~ v1_relat_1('#skF_11')
    | k11_relat_1('#skF_11','#skF_10') = k1_xboole_0
    | ~ v1_relat_1(k11_relat_1('#skF_11','#skF_10')) ),
    inference(resolution,[status(thm)],[c_429,c_97])).

tff(c_464,plain,(
    k11_relat_1('#skF_11','#skF_10') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_52,c_455])).

tff(c_466,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_464])).

tff(c_467,plain,(
    k11_relat_1('#skF_11','#skF_10') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_24,plain,(
    ! [A_34,B_36] :
      ( k9_relat_1(A_34,k1_tarski(B_36)) = k11_relat_1(A_34,B_36)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_468,plain,(
    r2_hidden('#skF_10',k1_relat_1('#skF_11')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_70,plain,(
    ! [A_83,B_84] : k2_xboole_0(k1_tarski(A_83),B_84) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_74,plain,(
    ! [A_83] : k1_tarski(A_83) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_70])).

tff(c_20,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(k1_tarski(A_30),B_31)
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_536,plain,(
    ! [B_197,A_198] :
      ( k9_relat_1(B_197,A_198) != k1_xboole_0
      | ~ r1_tarski(A_198,k1_relat_1(B_197))
      | k1_xboole_0 = A_198
      | ~ v1_relat_1(B_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_540,plain,(
    ! [B_197,A_30] :
      ( k9_relat_1(B_197,k1_tarski(A_30)) != k1_xboole_0
      | k1_tarski(A_30) = k1_xboole_0
      | ~ v1_relat_1(B_197)
      | ~ r2_hidden(A_30,k1_relat_1(B_197)) ) ),
    inference(resolution,[status(thm)],[c_20,c_536])).

tff(c_550,plain,(
    ! [B_201,A_202] :
      ( k9_relat_1(B_201,k1_tarski(A_202)) != k1_xboole_0
      | ~ v1_relat_1(B_201)
      | ~ r2_hidden(A_202,k1_relat_1(B_201)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_540])).

tff(c_567,plain,
    ( k9_relat_1('#skF_11',k1_tarski('#skF_10')) != k1_xboole_0
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_468,c_550])).

tff(c_578,plain,(
    k9_relat_1('#skF_11',k1_tarski('#skF_10')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_567])).

tff(c_582,plain,
    ( k11_relat_1('#skF_11','#skF_10') != k1_xboole_0
    | ~ v1_relat_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_578])).

tff(c_585,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_467,c_582])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:43:25 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.49  
% 2.81/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.49  %$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_6 > #skF_11 > #skF_1 > #skF_8 > #skF_3 > #skF_10 > #skF_7 > #skF_2 > #skF_5 > #skF_4
% 2.81/1.49  
% 2.81/1.49  %Foreground sorts:
% 2.81/1.49  
% 2.81/1.49  
% 2.81/1.49  %Background operators:
% 2.81/1.49  
% 2.81/1.49  
% 2.81/1.49  %Foreground operators:
% 2.81/1.49  tff('#skF_9', type, '#skF_9': $i > $i).
% 2.81/1.49  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.81/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.49  tff('#skF_11', type, '#skF_11': $i).
% 2.81/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.81/1.49  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.81/1.49  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.81/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.81/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.81/1.49  tff('#skF_8', type, '#skF_8': $i > $i).
% 2.81/1.49  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.81/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.81/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.81/1.49  tff('#skF_10', type, '#skF_10': $i).
% 2.81/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.81/1.49  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.81/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.81/1.49  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.81/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.81/1.49  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 2.81/1.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.81/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.81/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.81/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.81/1.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.81/1.49  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.81/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.81/1.49  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.81/1.49  
% 2.96/1.50  tff(f_103, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 2.96/1.50  tff(f_63, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.96/1.50  tff(f_87, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 2.96/1.50  tff(f_71, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 2.96/1.50  tff(f_95, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 2.96/1.50  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 2.96/1.50  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.96/1.50  tff(f_48, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.96/1.50  tff(f_45, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.96/1.50  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_relat_1)).
% 2.96/1.50  tff(c_52, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.96/1.50  tff(c_54, plain, (k11_relat_1('#skF_11', '#skF_10')=k1_xboole_0 | ~r2_hidden('#skF_10', k1_relat_1('#skF_11'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.96/1.50  tff(c_97, plain, (~r2_hidden('#skF_10', k1_relat_1('#skF_11'))), inference(splitLeft, [status(thm)], [c_54])).
% 2.96/1.50  tff(c_60, plain, (r2_hidden('#skF_10', k1_relat_1('#skF_11')) | k11_relat_1('#skF_11', '#skF_10')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.96/1.50  tff(c_103, plain, (k11_relat_1('#skF_11', '#skF_10')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_97, c_60])).
% 2.96/1.50  tff(c_30, plain, (![A_37]: (r2_hidden('#skF_1'(A_37), A_37) | v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.96/1.50  tff(c_144, plain, (![A_115, B_116, C_117]: (r2_hidden(k4_tarski(A_115, B_116), C_117) | ~r2_hidden(B_116, k11_relat_1(C_117, A_115)) | ~v1_relat_1(C_117))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.96/1.50  tff(c_34, plain, (![C_70, A_55, D_73]: (r2_hidden(C_70, k1_relat_1(A_55)) | ~r2_hidden(k4_tarski(C_70, D_73), A_55))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.96/1.50  tff(c_153, plain, (![A_118, C_119, B_120]: (r2_hidden(A_118, k1_relat_1(C_119)) | ~r2_hidden(B_120, k11_relat_1(C_119, A_118)) | ~v1_relat_1(C_119))), inference(resolution, [status(thm)], [c_144, c_34])).
% 2.96/1.50  tff(c_169, plain, (![A_121, C_122]: (r2_hidden(A_121, k1_relat_1(C_122)) | ~v1_relat_1(C_122) | v1_relat_1(k11_relat_1(C_122, A_121)))), inference(resolution, [status(thm)], [c_30, c_153])).
% 2.96/1.50  tff(c_180, plain, (~v1_relat_1('#skF_11') | v1_relat_1(k11_relat_1('#skF_11', '#skF_10'))), inference(resolution, [status(thm)], [c_169, c_97])).
% 2.96/1.50  tff(c_185, plain, (v1_relat_1(k11_relat_1('#skF_11', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_180])).
% 2.96/1.50  tff(c_50, plain, (![A_79]: (k1_xboole_0=A_79 | r2_hidden(k4_tarski('#skF_8'(A_79), '#skF_9'(A_79)), A_79) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.96/1.50  tff(c_429, plain, (![A_173, C_174]: (r2_hidden(A_173, k1_relat_1(C_174)) | ~v1_relat_1(C_174) | k11_relat_1(C_174, A_173)=k1_xboole_0 | ~v1_relat_1(k11_relat_1(C_174, A_173)))), inference(resolution, [status(thm)], [c_50, c_153])).
% 2.96/1.50  tff(c_455, plain, (~v1_relat_1('#skF_11') | k11_relat_1('#skF_11', '#skF_10')=k1_xboole_0 | ~v1_relat_1(k11_relat_1('#skF_11', '#skF_10'))), inference(resolution, [status(thm)], [c_429, c_97])).
% 2.96/1.50  tff(c_464, plain, (k11_relat_1('#skF_11', '#skF_10')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_185, c_52, c_455])).
% 2.96/1.50  tff(c_466, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_464])).
% 2.96/1.50  tff(c_467, plain, (k11_relat_1('#skF_11', '#skF_10')=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 2.96/1.50  tff(c_24, plain, (![A_34, B_36]: (k9_relat_1(A_34, k1_tarski(B_36))=k11_relat_1(A_34, B_36) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.96/1.50  tff(c_468, plain, (r2_hidden('#skF_10', k1_relat_1('#skF_11'))), inference(splitRight, [status(thm)], [c_54])).
% 2.96/1.50  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.96/1.50  tff(c_70, plain, (![A_83, B_84]: (k2_xboole_0(k1_tarski(A_83), B_84)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.96/1.51  tff(c_74, plain, (![A_83]: (k1_tarski(A_83)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_70])).
% 2.96/1.51  tff(c_20, plain, (![A_30, B_31]: (r1_tarski(k1_tarski(A_30), B_31) | ~r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.96/1.51  tff(c_536, plain, (![B_197, A_198]: (k9_relat_1(B_197, A_198)!=k1_xboole_0 | ~r1_tarski(A_198, k1_relat_1(B_197)) | k1_xboole_0=A_198 | ~v1_relat_1(B_197))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.96/1.51  tff(c_540, plain, (![B_197, A_30]: (k9_relat_1(B_197, k1_tarski(A_30))!=k1_xboole_0 | k1_tarski(A_30)=k1_xboole_0 | ~v1_relat_1(B_197) | ~r2_hidden(A_30, k1_relat_1(B_197)))), inference(resolution, [status(thm)], [c_20, c_536])).
% 2.96/1.51  tff(c_550, plain, (![B_201, A_202]: (k9_relat_1(B_201, k1_tarski(A_202))!=k1_xboole_0 | ~v1_relat_1(B_201) | ~r2_hidden(A_202, k1_relat_1(B_201)))), inference(negUnitSimplification, [status(thm)], [c_74, c_540])).
% 2.96/1.51  tff(c_567, plain, (k9_relat_1('#skF_11', k1_tarski('#skF_10'))!=k1_xboole_0 | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_468, c_550])).
% 2.96/1.51  tff(c_578, plain, (k9_relat_1('#skF_11', k1_tarski('#skF_10'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_567])).
% 2.96/1.51  tff(c_582, plain, (k11_relat_1('#skF_11', '#skF_10')!=k1_xboole_0 | ~v1_relat_1('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_24, c_578])).
% 2.96/1.51  tff(c_585, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_467, c_582])).
% 2.96/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.51  
% 2.96/1.51  Inference rules
% 2.96/1.51  ----------------------
% 2.96/1.51  #Ref     : 1
% 2.96/1.51  #Sup     : 105
% 2.96/1.51  #Fact    : 0
% 2.96/1.51  #Define  : 0
% 2.96/1.51  #Split   : 1
% 2.96/1.51  #Chain   : 0
% 2.96/1.51  #Close   : 0
% 2.96/1.51  
% 2.96/1.51  Ordering : KBO
% 2.96/1.51  
% 2.96/1.51  Simplification rules
% 2.96/1.51  ----------------------
% 2.96/1.51  #Subsume      : 6
% 2.96/1.51  #Demod        : 10
% 2.96/1.51  #Tautology    : 35
% 2.96/1.51  #SimpNegUnit  : 4
% 2.96/1.51  #BackRed      : 0
% 2.96/1.51  
% 2.96/1.51  #Partial instantiations: 0
% 2.96/1.51  #Strategies tried      : 1
% 2.96/1.51  
% 2.96/1.51  Timing (in seconds)
% 2.96/1.51  ----------------------
% 2.96/1.51  Preprocessing        : 0.37
% 2.96/1.51  Parsing              : 0.19
% 2.96/1.51  CNF conversion       : 0.03
% 2.96/1.51  Main loop            : 0.29
% 2.96/1.51  Inferencing          : 0.12
% 2.96/1.51  Reduction            : 0.07
% 2.96/1.51  Demodulation         : 0.04
% 2.96/1.51  BG Simplification    : 0.02
% 2.96/1.51  Subsumption          : 0.05
% 2.96/1.51  Abstraction          : 0.02
% 2.96/1.51  MUC search           : 0.00
% 2.96/1.51  Cooper               : 0.00
% 2.96/1.51  Total                : 0.68
% 2.96/1.51  Index Insertion      : 0.00
% 2.96/1.51  Index Deletion       : 0.00
% 2.96/1.51  Index Matching       : 0.00
% 2.96/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
