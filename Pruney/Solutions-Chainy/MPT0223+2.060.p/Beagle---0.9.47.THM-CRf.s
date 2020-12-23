%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:24 EST 2020

% Result     : Theorem 5.01s
% Output     : CNFRefutation 5.01s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 315 expanded)
%              Number of leaves         :   30 ( 115 expanded)
%              Depth                    :   18
%              Number of atoms          :   95 ( 435 expanded)
%              Number of equality atoms :   56 ( 295 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_47,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_43,axiom,(
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

tff(f_74,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_76,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_129,plain,(
    ! [A_56,B_57] : k4_xboole_0(A_56,k4_xboole_0(A_56,B_57)) = k3_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_132,plain,(
    ! [A_56,B_57] : k4_xboole_0(A_56,k3_xboole_0(A_56,B_57)) = k3_xboole_0(A_56,k4_xboole_0(A_56,B_57)) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_14])).

tff(c_333,plain,(
    ! [A_78,B_79] : k3_xboole_0(A_78,k4_xboole_0(A_78,B_79)) = k4_xboole_0(A_78,B_79) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_132])).

tff(c_16,plain,(
    ! [A_12,B_13] : k2_xboole_0(k3_xboole_0(A_12,B_13),k4_xboole_0(A_12,B_13)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_342,plain,(
    ! [A_78,B_79] : k2_xboole_0(k4_xboole_0(A_78,B_79),k4_xboole_0(A_78,k4_xboole_0(A_78,B_79))) = A_78 ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_16])).

tff(c_369,plain,(
    ! [A_80,B_81] : k2_xboole_0(k4_xboole_0(A_80,B_81),k3_xboole_0(A_80,B_81)) = A_80 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_342])).

tff(c_411,plain,(
    ! [A_82] : k2_xboole_0(k4_xboole_0(A_82,k1_xboole_0),k1_xboole_0) = A_82 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_369])).

tff(c_8,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_417,plain,(
    ! [A_82] : k4_xboole_0(A_82,k1_xboole_0) = A_82 ),
    inference(superposition,[status(thm),theory(equality)],[c_411,c_8])).

tff(c_54,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_434,plain,(
    ! [A_83] : k4_xboole_0(A_83,k1_xboole_0) = A_83 ),
    inference(superposition,[status(thm),theory(equality)],[c_411,c_8])).

tff(c_453,plain,(
    ! [A_83] : k4_xboole_0(A_83,A_83) = k3_xboole_0(A_83,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_434,c_14])).

tff(c_466,plain,(
    ! [A_83] : k4_xboole_0(A_83,A_83) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_453])).

tff(c_56,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_144,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k3_xboole_0(A_58,B_59)) = k4_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_156,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_144])).

tff(c_563,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_156])).

tff(c_52,plain,(
    ! [A_29,B_30] :
      ( r1_xboole_0(k1_tarski(A_29),B_30)
      | r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_120,plain,(
    ! [A_54,B_55] :
      ( k4_xboole_0(A_54,B_55) = A_54
      | ~ r1_xboole_0(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_128,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(k1_tarski(A_29),B_30) = k1_tarski(A_29)
      | r2_hidden(A_29,B_30) ) ),
    inference(resolution,[status(thm)],[c_52,c_120])).

tff(c_619,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | r2_hidden('#skF_4',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_563,c_128])).

tff(c_639,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_619])).

tff(c_26,plain,(
    ! [E_22,A_16,C_18] : r2_hidden(E_22,k1_enumset1(A_16,E_22,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_257,plain,(
    ! [A_69,B_70,C_71] :
      ( ~ r1_xboole_0(A_69,B_70)
      | ~ r2_hidden(C_71,B_70)
      | ~ r2_hidden(C_71,A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_644,plain,(
    ! [C_95,B_96,A_97] :
      ( ~ r2_hidden(C_95,B_96)
      | ~ r2_hidden(C_95,k1_tarski(A_97))
      | r2_hidden(A_97,B_96) ) ),
    inference(resolution,[status(thm)],[c_52,c_257])).

tff(c_1605,plain,(
    ! [E_2034,A_2035,A_2036,C_2037] :
      ( ~ r2_hidden(E_2034,k1_tarski(A_2035))
      | r2_hidden(A_2035,k1_enumset1(A_2036,E_2034,C_2037)) ) ),
    inference(resolution,[status(thm)],[c_26,c_644])).

tff(c_1638,plain,(
    ! [A_2064,C_2065] : r2_hidden('#skF_5',k1_enumset1(A_2064,'#skF_4',C_2065)) ),
    inference(resolution,[status(thm)],[c_639,c_1605])).

tff(c_22,plain,(
    ! [E_22,C_18,B_17,A_16] :
      ( E_22 = C_18
      | E_22 = B_17
      | E_22 = A_16
      | ~ r2_hidden(E_22,k1_enumset1(A_16,B_17,C_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1645,plain,(
    ! [C_2065,A_2064] :
      ( C_2065 = '#skF_5'
      | '#skF_5' = '#skF_4'
      | A_2064 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_1638,c_22])).

tff(c_1703,plain,(
    ! [C_2065,A_2064] :
      ( C_2065 = '#skF_5'
      | A_2064 = '#skF_5' ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1645])).

tff(c_2442,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1703])).

tff(c_1705,plain,(
    ! [A_2064] : A_2064 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1703])).

tff(c_2696,plain,(
    ! [A_5997] : A_5997 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2442,c_1705])).

tff(c_2949,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_2696,c_54])).

tff(c_2951,plain,(
    ! [C_8026] : C_8026 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1703])).

tff(c_3185,plain,(
    ! [C_8026] : C_8026 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2951,c_54])).

tff(c_3201,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3185])).

tff(c_3202,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_619])).

tff(c_46,plain,(
    ! [A_23] : k2_tarski(A_23,A_23) = k1_tarski(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_86,plain,(
    ! [A_45,B_46] : k1_enumset1(A_45,A_45,B_46) = k2_tarski(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_28,plain,(
    ! [E_22,B_17,C_18] : r2_hidden(E_22,k1_enumset1(E_22,B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_108,plain,(
    ! [A_47,B_48] : r2_hidden(A_47,k2_tarski(A_47,B_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_28])).

tff(c_111,plain,(
    ! [A_23] : r2_hidden(A_23,k1_tarski(A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_108])).

tff(c_3212,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3202,c_111])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( r1_xboole_0(A_14,B_15)
      | k4_xboole_0(A_14,B_15) != A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4210,plain,(
    ! [C_11584,B_11585,A_11586] :
      ( ~ r2_hidden(C_11584,B_11585)
      | ~ r2_hidden(C_11584,A_11586)
      | k4_xboole_0(A_11586,B_11585) != A_11586 ) ),
    inference(resolution,[status(thm)],[c_20,c_257])).

tff(c_4230,plain,(
    ! [A_11586] :
      ( ~ r2_hidden('#skF_4',A_11586)
      | k4_xboole_0(A_11586,k1_xboole_0) != A_11586 ) ),
    inference(resolution,[status(thm)],[c_3212,c_4210])).

tff(c_4258,plain,(
    ! [A_11586] : ~ r2_hidden('#skF_4',A_11586) ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_4230])).

tff(c_4273,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4258,c_3212])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:30:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.01/1.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.01/1.99  
% 5.01/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.01/1.99  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 5.01/1.99  
% 5.01/1.99  %Foreground sorts:
% 5.01/1.99  
% 5.01/1.99  
% 5.01/1.99  %Background operators:
% 5.01/1.99  
% 5.01/1.99  
% 5.01/1.99  %Foreground operators:
% 5.01/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.01/1.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.01/1.99  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.01/1.99  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.01/1.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.01/1.99  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.01/1.99  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.01/1.99  tff('#skF_5', type, '#skF_5': $i).
% 5.01/1.99  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 5.01/1.99  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.01/1.99  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.01/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.01/1.99  tff('#skF_4', type, '#skF_4': $i).
% 5.01/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.01/1.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.01/1.99  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.01/1.99  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.01/1.99  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.01/1.99  
% 5.01/2.00  tff(f_47, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 5.01/2.00  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.01/2.00  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 5.01/2.00  tff(f_53, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 5.01/2.00  tff(f_45, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 5.01/2.00  tff(f_88, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 5.01/2.00  tff(f_83, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 5.01/2.00  tff(f_57, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 5.01/2.00  tff(f_72, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 5.01/2.00  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.01/2.00  tff(f_74, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.01/2.00  tff(f_76, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 5.01/2.00  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.01/2.00  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.01/2.00  tff(c_12, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.01/2.00  tff(c_129, plain, (![A_56, B_57]: (k4_xboole_0(A_56, k4_xboole_0(A_56, B_57))=k3_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.01/2.00  tff(c_132, plain, (![A_56, B_57]: (k4_xboole_0(A_56, k3_xboole_0(A_56, B_57))=k3_xboole_0(A_56, k4_xboole_0(A_56, B_57)))), inference(superposition, [status(thm), theory('equality')], [c_129, c_14])).
% 5.01/2.00  tff(c_333, plain, (![A_78, B_79]: (k3_xboole_0(A_78, k4_xboole_0(A_78, B_79))=k4_xboole_0(A_78, B_79))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_132])).
% 5.01/2.00  tff(c_16, plain, (![A_12, B_13]: (k2_xboole_0(k3_xboole_0(A_12, B_13), k4_xboole_0(A_12, B_13))=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.01/2.00  tff(c_342, plain, (![A_78, B_79]: (k2_xboole_0(k4_xboole_0(A_78, B_79), k4_xboole_0(A_78, k4_xboole_0(A_78, B_79)))=A_78)), inference(superposition, [status(thm), theory('equality')], [c_333, c_16])).
% 5.01/2.00  tff(c_369, plain, (![A_80, B_81]: (k2_xboole_0(k4_xboole_0(A_80, B_81), k3_xboole_0(A_80, B_81))=A_80)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_342])).
% 5.01/2.00  tff(c_411, plain, (![A_82]: (k2_xboole_0(k4_xboole_0(A_82, k1_xboole_0), k1_xboole_0)=A_82)), inference(superposition, [status(thm), theory('equality')], [c_10, c_369])).
% 5.01/2.00  tff(c_8, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.01/2.00  tff(c_417, plain, (![A_82]: (k4_xboole_0(A_82, k1_xboole_0)=A_82)), inference(superposition, [status(thm), theory('equality')], [c_411, c_8])).
% 5.01/2.00  tff(c_54, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.01/2.00  tff(c_434, plain, (![A_83]: (k4_xboole_0(A_83, k1_xboole_0)=A_83)), inference(superposition, [status(thm), theory('equality')], [c_411, c_8])).
% 5.01/2.00  tff(c_453, plain, (![A_83]: (k4_xboole_0(A_83, A_83)=k3_xboole_0(A_83, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_434, c_14])).
% 5.01/2.00  tff(c_466, plain, (![A_83]: (k4_xboole_0(A_83, A_83)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_453])).
% 5.01/2.00  tff(c_56, plain, (k3_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.01/2.00  tff(c_144, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k3_xboole_0(A_58, B_59))=k4_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.01/2.00  tff(c_156, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_144])).
% 5.01/2.00  tff(c_563, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_466, c_156])).
% 5.01/2.00  tff(c_52, plain, (![A_29, B_30]: (r1_xboole_0(k1_tarski(A_29), B_30) | r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.01/2.00  tff(c_120, plain, (![A_54, B_55]: (k4_xboole_0(A_54, B_55)=A_54 | ~r1_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.01/2.00  tff(c_128, plain, (![A_29, B_30]: (k4_xboole_0(k1_tarski(A_29), B_30)=k1_tarski(A_29) | r2_hidden(A_29, B_30))), inference(resolution, [status(thm)], [c_52, c_120])).
% 5.01/2.00  tff(c_619, plain, (k1_tarski('#skF_4')=k1_xboole_0 | r2_hidden('#skF_4', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_563, c_128])).
% 5.01/2.00  tff(c_639, plain, (r2_hidden('#skF_4', k1_tarski('#skF_5'))), inference(splitLeft, [status(thm)], [c_619])).
% 5.01/2.00  tff(c_26, plain, (![E_22, A_16, C_18]: (r2_hidden(E_22, k1_enumset1(A_16, E_22, C_18)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.01/2.00  tff(c_257, plain, (![A_69, B_70, C_71]: (~r1_xboole_0(A_69, B_70) | ~r2_hidden(C_71, B_70) | ~r2_hidden(C_71, A_69))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.01/2.00  tff(c_644, plain, (![C_95, B_96, A_97]: (~r2_hidden(C_95, B_96) | ~r2_hidden(C_95, k1_tarski(A_97)) | r2_hidden(A_97, B_96))), inference(resolution, [status(thm)], [c_52, c_257])).
% 5.01/2.00  tff(c_1605, plain, (![E_2034, A_2035, A_2036, C_2037]: (~r2_hidden(E_2034, k1_tarski(A_2035)) | r2_hidden(A_2035, k1_enumset1(A_2036, E_2034, C_2037)))), inference(resolution, [status(thm)], [c_26, c_644])).
% 5.01/2.00  tff(c_1638, plain, (![A_2064, C_2065]: (r2_hidden('#skF_5', k1_enumset1(A_2064, '#skF_4', C_2065)))), inference(resolution, [status(thm)], [c_639, c_1605])).
% 5.01/2.00  tff(c_22, plain, (![E_22, C_18, B_17, A_16]: (E_22=C_18 | E_22=B_17 | E_22=A_16 | ~r2_hidden(E_22, k1_enumset1(A_16, B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.01/2.00  tff(c_1645, plain, (![C_2065, A_2064]: (C_2065='#skF_5' | '#skF_5'='#skF_4' | A_2064='#skF_5')), inference(resolution, [status(thm)], [c_1638, c_22])).
% 5.01/2.00  tff(c_1703, plain, (![C_2065, A_2064]: (C_2065='#skF_5' | A_2064='#skF_5')), inference(negUnitSimplification, [status(thm)], [c_54, c_1645])).
% 5.01/2.00  tff(c_2442, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_1703])).
% 5.01/2.00  tff(c_1705, plain, (![A_2064]: (A_2064='#skF_5')), inference(splitLeft, [status(thm)], [c_1703])).
% 5.01/2.00  tff(c_2696, plain, (![A_5997]: (A_5997='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2442, c_1705])).
% 5.01/2.00  tff(c_2949, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_2696, c_54])).
% 5.01/2.00  tff(c_2951, plain, (![C_8026]: (C_8026='#skF_5')), inference(splitRight, [status(thm)], [c_1703])).
% 5.01/2.00  tff(c_3185, plain, (![C_8026]: (C_8026!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2951, c_54])).
% 5.01/2.00  tff(c_3201, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_3185])).
% 5.01/2.00  tff(c_3202, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_619])).
% 5.01/2.00  tff(c_46, plain, (![A_23]: (k2_tarski(A_23, A_23)=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.01/2.00  tff(c_86, plain, (![A_45, B_46]: (k1_enumset1(A_45, A_45, B_46)=k2_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.01/2.00  tff(c_28, plain, (![E_22, B_17, C_18]: (r2_hidden(E_22, k1_enumset1(E_22, B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.01/2.00  tff(c_108, plain, (![A_47, B_48]: (r2_hidden(A_47, k2_tarski(A_47, B_48)))), inference(superposition, [status(thm), theory('equality')], [c_86, c_28])).
% 5.01/2.00  tff(c_111, plain, (![A_23]: (r2_hidden(A_23, k1_tarski(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_108])).
% 5.01/2.00  tff(c_3212, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3202, c_111])).
% 5.01/2.00  tff(c_20, plain, (![A_14, B_15]: (r1_xboole_0(A_14, B_15) | k4_xboole_0(A_14, B_15)!=A_14)), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.01/2.00  tff(c_4210, plain, (![C_11584, B_11585, A_11586]: (~r2_hidden(C_11584, B_11585) | ~r2_hidden(C_11584, A_11586) | k4_xboole_0(A_11586, B_11585)!=A_11586)), inference(resolution, [status(thm)], [c_20, c_257])).
% 5.01/2.00  tff(c_4230, plain, (![A_11586]: (~r2_hidden('#skF_4', A_11586) | k4_xboole_0(A_11586, k1_xboole_0)!=A_11586)), inference(resolution, [status(thm)], [c_3212, c_4210])).
% 5.01/2.00  tff(c_4258, plain, (![A_11586]: (~r2_hidden('#skF_4', A_11586))), inference(demodulation, [status(thm), theory('equality')], [c_417, c_4230])).
% 5.01/2.00  tff(c_4273, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4258, c_3212])).
% 5.01/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.01/2.00  
% 5.01/2.00  Inference rules
% 5.01/2.00  ----------------------
% 5.01/2.00  #Ref     : 1
% 5.01/2.00  #Sup     : 930
% 5.01/2.00  #Fact    : 18
% 5.01/2.00  #Define  : 0
% 5.01/2.00  #Split   : 2
% 5.01/2.00  #Chain   : 0
% 5.01/2.00  #Close   : 0
% 5.01/2.00  
% 5.01/2.00  Ordering : KBO
% 5.01/2.00  
% 5.01/2.00  Simplification rules
% 5.01/2.00  ----------------------
% 5.01/2.00  #Subsume      : 179
% 5.01/2.00  #Demod        : 238
% 5.01/2.00  #Tautology    : 233
% 5.01/2.00  #SimpNegUnit  : 16
% 5.01/2.00  #BackRed      : 13
% 5.01/2.00  
% 5.01/2.00  #Partial instantiations: 2917
% 5.01/2.00  #Strategies tried      : 1
% 5.01/2.00  
% 5.01/2.00  Timing (in seconds)
% 5.01/2.00  ----------------------
% 5.01/2.01  Preprocessing        : 0.33
% 5.01/2.01  Parsing              : 0.17
% 5.01/2.01  CNF conversion       : 0.02
% 5.01/2.01  Main loop            : 0.90
% 5.01/2.01  Inferencing          : 0.45
% 5.01/2.01  Reduction            : 0.23
% 5.01/2.01  Demodulation         : 0.18
% 5.01/2.01  BG Simplification    : 0.04
% 5.01/2.01  Subsumption          : 0.13
% 5.01/2.01  Abstraction          : 0.04
% 5.01/2.01  MUC search           : 0.00
% 5.01/2.01  Cooper               : 0.00
% 5.01/2.01  Total                : 1.26
% 5.01/2.01  Index Insertion      : 0.00
% 5.01/2.01  Index Deletion       : 0.00
% 5.01/2.01  Index Matching       : 0.00
% 5.01/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
