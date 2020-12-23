%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:45 EST 2020

% Result     : Theorem 8.51s
% Output     : CNFRefutation 8.51s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 100 expanded)
%              Number of leaves         :   35 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :   70 ( 115 expanded)
%              Number of equality atoms :   38 (  75 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_67,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_71,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & k4_xboole_0(B,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_xboole_1)).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_16,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_2'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_46,plain,(
    k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_44,plain,(
    ! [A_46,B_47] :
      ( r1_xboole_0(k1_tarski(A_46),B_47)
      | r2_hidden(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_22,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_50,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_272,plain,(
    ! [A_77,B_78] : k5_xboole_0(A_77,k3_xboole_0(A_77,B_78)) = k4_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_285,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_272])).

tff(c_92,plain,(
    ! [B_53,A_54] : k5_xboole_0(B_53,A_54) = k5_xboole_0(A_54,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_108,plain,(
    ! [A_54] : k5_xboole_0(k1_xboole_0,A_54) = A_54 ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_22])).

tff(c_26,plain,(
    ! [A_22] : k5_xboole_0(A_22,A_22) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_364,plain,(
    ! [A_86,B_87,C_88] : k5_xboole_0(k5_xboole_0(A_86,B_87),C_88) = k5_xboole_0(A_86,k5_xboole_0(B_87,C_88)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_439,plain,(
    ! [A_22,C_88] : k5_xboole_0(A_22,k5_xboole_0(A_22,C_88)) = k5_xboole_0(k1_xboole_0,C_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_364])).

tff(c_453,plain,(
    ! [A_89,C_90] : k5_xboole_0(A_89,k5_xboole_0(A_89,C_90)) = C_90 ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_439])).

tff(c_903,plain,(
    ! [A_123,B_124] : k5_xboole_0(A_123,k4_xboole_0(A_123,B_124)) = k3_xboole_0(B_124,A_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_453])).

tff(c_949,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),'#skF_3') = k5_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_903])).

tff(c_956,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_949])).

tff(c_14,plain,(
    ! [A_7,B_8,C_11] :
      ( ~ r1_xboole_0(A_7,B_8)
      | ~ r2_hidden(C_11,k3_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_972,plain,(
    ! [C_11] :
      ( ~ r1_xboole_0(k1_tarski('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_11,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_956,c_14])).

tff(c_1017,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_972])).

tff(c_1021,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_1017])).

tff(c_42,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(k1_tarski(A_44),B_45)
      | ~ r2_hidden(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_257,plain,(
    ! [A_75,B_76] :
      ( r2_xboole_0(A_75,B_76)
      | B_76 = A_75
      | ~ r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_20,plain,(
    ! [B_17,A_16] :
      ( k4_xboole_0(B_17,A_16) != k1_xboole_0
      | ~ r2_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1009,plain,(
    ! [B_125,A_126] :
      ( k4_xboole_0(B_125,A_126) != k1_xboole_0
      | B_125 = A_126
      | ~ r1_tarski(A_126,B_125) ) ),
    inference(resolution,[status(thm)],[c_257,c_20])).

tff(c_12207,plain,(
    ! [B_219,A_220] :
      ( k4_xboole_0(B_219,k1_tarski(A_220)) != k1_xboole_0
      | k1_tarski(A_220) = B_219
      | ~ r2_hidden(A_220,B_219) ) ),
    inference(resolution,[status(thm)],[c_42,c_1009])).

tff(c_12225,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_12207])).

tff(c_12229,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1021,c_12225])).

tff(c_12231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_12229])).

tff(c_12234,plain,(
    ! [C_221] : ~ r2_hidden(C_221,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_972])).

tff(c_12238,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_16,c_12234])).

tff(c_12242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_12238])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 13:01:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.51/3.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.51/3.61  
% 8.51/3.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.51/3.62  %$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 8.51/3.62  
% 8.51/3.62  %Foreground sorts:
% 8.51/3.62  
% 8.51/3.62  
% 8.51/3.62  %Background operators:
% 8.51/3.62  
% 8.51/3.62  
% 8.51/3.62  %Foreground operators:
% 8.51/3.62  tff('#skF_2', type, '#skF_2': $i > $i).
% 8.51/3.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.51/3.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.51/3.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.51/3.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.51/3.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.51/3.62  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.51/3.62  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.51/3.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.51/3.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.51/3.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.51/3.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.51/3.62  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.51/3.62  tff('#skF_3', type, '#skF_3': $i).
% 8.51/3.62  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.51/3.62  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 8.51/3.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.51/3.62  tff('#skF_4', type, '#skF_4': $i).
% 8.51/3.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.51/3.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.51/3.62  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.51/3.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.51/3.62  
% 8.51/3.63  tff(f_102, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 8.51/3.63  tff(f_58, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 8.51/3.63  tff(f_92, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 8.51/3.63  tff(f_67, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 8.51/3.63  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.51/3.63  tff(f_60, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.51/3.63  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 8.51/3.63  tff(f_71, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 8.51/3.63  tff(f_69, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.51/3.63  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 8.51/3.63  tff(f_87, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 8.51/3.63  tff(f_36, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 8.51/3.63  tff(f_65, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (k4_xboole_0(B, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_xboole_1)).
% 8.51/3.63  tff(c_48, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.51/3.63  tff(c_16, plain, (![A_12]: (r2_hidden('#skF_2'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.51/3.63  tff(c_46, plain, (k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.51/3.63  tff(c_44, plain, (![A_46, B_47]: (r1_xboole_0(k1_tarski(A_46), B_47) | r2_hidden(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.51/3.63  tff(c_22, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.51/3.63  tff(c_50, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.51/3.63  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.51/3.63  tff(c_272, plain, (![A_77, B_78]: (k5_xboole_0(A_77, k3_xboole_0(A_77, B_78))=k4_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.51/3.63  tff(c_285, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_272])).
% 8.51/3.63  tff(c_92, plain, (![B_53, A_54]: (k5_xboole_0(B_53, A_54)=k5_xboole_0(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.51/3.63  tff(c_108, plain, (![A_54]: (k5_xboole_0(k1_xboole_0, A_54)=A_54)), inference(superposition, [status(thm), theory('equality')], [c_92, c_22])).
% 8.51/3.63  tff(c_26, plain, (![A_22]: (k5_xboole_0(A_22, A_22)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.51/3.63  tff(c_364, plain, (![A_86, B_87, C_88]: (k5_xboole_0(k5_xboole_0(A_86, B_87), C_88)=k5_xboole_0(A_86, k5_xboole_0(B_87, C_88)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.51/3.63  tff(c_439, plain, (![A_22, C_88]: (k5_xboole_0(A_22, k5_xboole_0(A_22, C_88))=k5_xboole_0(k1_xboole_0, C_88))), inference(superposition, [status(thm), theory('equality')], [c_26, c_364])).
% 8.51/3.63  tff(c_453, plain, (![A_89, C_90]: (k5_xboole_0(A_89, k5_xboole_0(A_89, C_90))=C_90)), inference(demodulation, [status(thm), theory('equality')], [c_108, c_439])).
% 8.51/3.63  tff(c_903, plain, (![A_123, B_124]: (k5_xboole_0(A_123, k4_xboole_0(A_123, B_124))=k3_xboole_0(B_124, A_123))), inference(superposition, [status(thm), theory('equality')], [c_285, c_453])).
% 8.51/3.63  tff(c_949, plain, (k3_xboole_0(k1_tarski('#skF_4'), '#skF_3')=k5_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_50, c_903])).
% 8.51/3.63  tff(c_956, plain, (k3_xboole_0(k1_tarski('#skF_4'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_949])).
% 8.51/3.63  tff(c_14, plain, (![A_7, B_8, C_11]: (~r1_xboole_0(A_7, B_8) | ~r2_hidden(C_11, k3_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.51/3.63  tff(c_972, plain, (![C_11]: (~r1_xboole_0(k1_tarski('#skF_4'), '#skF_3') | ~r2_hidden(C_11, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_956, c_14])).
% 8.51/3.63  tff(c_1017, plain, (~r1_xboole_0(k1_tarski('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_972])).
% 8.51/3.63  tff(c_1021, plain, (r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_1017])).
% 8.51/3.63  tff(c_42, plain, (![A_44, B_45]: (r1_tarski(k1_tarski(A_44), B_45) | ~r2_hidden(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.51/3.63  tff(c_257, plain, (![A_75, B_76]: (r2_xboole_0(A_75, B_76) | B_76=A_75 | ~r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.51/3.63  tff(c_20, plain, (![B_17, A_16]: (k4_xboole_0(B_17, A_16)!=k1_xboole_0 | ~r2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.51/3.63  tff(c_1009, plain, (![B_125, A_126]: (k4_xboole_0(B_125, A_126)!=k1_xboole_0 | B_125=A_126 | ~r1_tarski(A_126, B_125))), inference(resolution, [status(thm)], [c_257, c_20])).
% 8.51/3.63  tff(c_12207, plain, (![B_219, A_220]: (k4_xboole_0(B_219, k1_tarski(A_220))!=k1_xboole_0 | k1_tarski(A_220)=B_219 | ~r2_hidden(A_220, B_219))), inference(resolution, [status(thm)], [c_42, c_1009])).
% 8.51/3.63  tff(c_12225, plain, (k1_tarski('#skF_4')='#skF_3' | ~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_50, c_12207])).
% 8.51/3.63  tff(c_12229, plain, (k1_tarski('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1021, c_12225])).
% 8.51/3.63  tff(c_12231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_12229])).
% 8.51/3.63  tff(c_12234, plain, (![C_221]: (~r2_hidden(C_221, '#skF_3'))), inference(splitRight, [status(thm)], [c_972])).
% 8.51/3.63  tff(c_12238, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_16, c_12234])).
% 8.51/3.63  tff(c_12242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_12238])).
% 8.51/3.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.51/3.63  
% 8.51/3.63  Inference rules
% 8.51/3.63  ----------------------
% 8.51/3.63  #Ref     : 0
% 8.51/3.63  #Sup     : 3139
% 8.51/3.63  #Fact    : 0
% 8.51/3.63  #Define  : 0
% 8.51/3.63  #Split   : 2
% 8.51/3.63  #Chain   : 0
% 8.51/3.63  #Close   : 0
% 8.51/3.63  
% 8.51/3.63  Ordering : KBO
% 8.51/3.63  
% 8.51/3.63  Simplification rules
% 8.51/3.63  ----------------------
% 8.51/3.63  #Subsume      : 318
% 8.51/3.63  #Demod        : 3453
% 8.51/3.63  #Tautology    : 1303
% 8.51/3.63  #SimpNegUnit  : 14
% 8.51/3.63  #BackRed      : 1
% 8.51/3.63  
% 8.51/3.63  #Partial instantiations: 0
% 8.51/3.63  #Strategies tried      : 1
% 8.51/3.63  
% 8.51/3.63  Timing (in seconds)
% 8.51/3.63  ----------------------
% 8.51/3.63  Preprocessing        : 0.31
% 8.51/3.63  Parsing              : 0.16
% 8.51/3.63  CNF conversion       : 0.02
% 8.51/3.63  Main loop            : 2.53
% 8.51/3.64  Inferencing          : 0.45
% 8.51/3.64  Reduction            : 1.66
% 8.51/3.64  Demodulation         : 1.53
% 8.51/3.64  BG Simplification    : 0.07
% 8.51/3.64  Subsumption          : 0.26
% 8.51/3.64  Abstraction          : 0.10
% 8.51/3.64  MUC search           : 0.00
% 8.51/3.64  Cooper               : 0.00
% 8.51/3.64  Total                : 2.87
% 8.51/3.64  Index Insertion      : 0.00
% 8.51/3.64  Index Deletion       : 0.00
% 8.51/3.64  Index Matching       : 0.00
% 8.51/3.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
