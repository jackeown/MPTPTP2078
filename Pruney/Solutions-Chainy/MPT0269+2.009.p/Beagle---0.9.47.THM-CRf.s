%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:45 EST 2020

% Result     : Theorem 9.52s
% Output     : CNFRefutation 9.63s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 138 expanded)
%              Number of leaves         :   38 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :   88 ( 170 expanded)
%              Number of equality atoms :   37 (  97 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_69,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_62,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_73,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_91,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & k4_xboole_0(B,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_xboole_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_52,plain,(
    k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_50,plain,(
    ! [A_56,B_57] :
      ( r1_xboole_0(k1_tarski(A_56),B_57)
      | r2_hidden(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_26,plain,(
    ! [A_21] : k5_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_56,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_22,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_137,plain,(
    ! [B_68,A_69] : k5_xboole_0(B_68,A_69) = k5_xboole_0(A_69,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_153,plain,(
    ! [A_69] : k5_xboole_0(k1_xboole_0,A_69) = A_69 ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_26])).

tff(c_30,plain,(
    ! [A_25] : k5_xboole_0(A_25,A_25) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_417,plain,(
    ! [A_108,B_109,C_110] : k5_xboole_0(k5_xboole_0(A_108,B_109),C_110) = k5_xboole_0(A_108,k5_xboole_0(B_109,C_110)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_485,plain,(
    ! [A_25,C_110] : k5_xboole_0(A_25,k5_xboole_0(A_25,C_110)) = k5_xboole_0(k1_xboole_0,C_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_417])).

tff(c_506,plain,(
    ! [A_111,C_112] : k5_xboole_0(A_111,k5_xboole_0(A_111,C_112)) = C_112 ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_485])).

tff(c_971,plain,(
    ! [A_144,B_145] : k5_xboole_0(A_144,k4_xboole_0(A_144,B_145)) = k3_xboole_0(A_144,B_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_506])).

tff(c_1017,plain,(
    k3_xboole_0('#skF_3',k1_tarski('#skF_4')) = k5_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_971])).

tff(c_1024,plain,(
    k3_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1017])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_873,plain,(
    ! [A_119,B_120] :
      ( r2_hidden('#skF_2'(A_119,B_120),k3_xboole_0(A_119,B_120))
      | r1_xboole_0(A_119,B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6,plain,(
    ! [B_8,A_5] :
      ( ~ r2_hidden(B_8,A_5)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_909,plain,(
    ! [A_127,B_128] :
      ( ~ v1_xboole_0(k3_xboole_0(A_127,B_128))
      | r1_xboole_0(A_127,B_128) ) ),
    inference(resolution,[status(thm)],[c_873,c_6])).

tff(c_918,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(k3_xboole_0(B_2,A_1))
      | r1_xboole_0(A_1,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_909])).

tff(c_1028,plain,
    ( ~ v1_xboole_0('#skF_3')
    | r1_xboole_0(k1_tarski('#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1024,c_918])).

tff(c_1057,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1028])).

tff(c_8,plain,(
    ! [A_5] :
      ( v1_xboole_0(A_5)
      | r2_hidden('#skF_1'(A_5),A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_252,plain,(
    ! [A_83,B_84,C_85] :
      ( ~ r1_xboole_0(A_83,B_84)
      | ~ r2_hidden(C_85,k3_xboole_0(A_83,B_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_264,plain,(
    ! [A_86,B_87] :
      ( ~ r1_xboole_0(A_86,B_87)
      | v1_xboole_0(k3_xboole_0(A_86,B_87)) ) ),
    inference(resolution,[status(thm)],[c_8,c_252])).

tff(c_270,plain,(
    ! [A_1,B_2] :
      ( ~ r1_xboole_0(A_1,B_2)
      | v1_xboole_0(k3_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_264])).

tff(c_1046,plain,
    ( ~ r1_xboole_0(k1_tarski('#skF_4'),'#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1024,c_270])).

tff(c_1067,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1057,c_1046])).

tff(c_1071,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1067])).

tff(c_48,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(k1_tarski(A_54),B_55)
      | ~ r2_hidden(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_280,plain,(
    ! [A_90,B_91] :
      ( r2_xboole_0(A_90,B_91)
      | B_91 = A_90
      | ~ r1_tarski(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_24,plain,(
    ! [B_20,A_19] :
      ( k4_xboole_0(B_20,A_19) != k1_xboole_0
      | ~ r2_xboole_0(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1261,plain,(
    ! [B_157,A_158] :
      ( k4_xboole_0(B_157,A_158) != k1_xboole_0
      | B_157 = A_158
      | ~ r1_tarski(A_158,B_157) ) ),
    inference(resolution,[status(thm)],[c_280,c_24])).

tff(c_14851,plain,(
    ! [B_257,A_258] :
      ( k4_xboole_0(B_257,k1_tarski(A_258)) != k1_xboole_0
      | k1_tarski(A_258) = B_257
      | ~ r2_hidden(A_258,B_257) ) ),
    inference(resolution,[status(thm)],[c_48,c_1261])).

tff(c_14869,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_14851])).

tff(c_14873,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1071,c_14869])).

tff(c_14875,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_14873])).

tff(c_14877,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1028])).

tff(c_16,plain,(
    ! [A_11] :
      ( k1_xboole_0 = A_11
      | ~ v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_14880,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_14877,c_16])).

tff(c_14884,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_14880])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 21:17:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.52/4.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.52/4.12  
% 9.52/4.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.63/4.12  %$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 9.63/4.12  
% 9.63/4.12  %Foreground sorts:
% 9.63/4.12  
% 9.63/4.12  
% 9.63/4.12  %Background operators:
% 9.63/4.12  
% 9.63/4.12  
% 9.63/4.12  %Foreground operators:
% 9.63/4.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.63/4.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.63/4.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.63/4.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.63/4.12  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.63/4.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.63/4.12  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.63/4.12  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.63/4.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.63/4.12  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.63/4.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.63/4.12  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.63/4.12  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.63/4.12  tff('#skF_3', type, '#skF_3': $i).
% 9.63/4.12  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.63/4.12  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 9.63/4.12  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.63/4.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.63/4.12  tff('#skF_4', type, '#skF_4': $i).
% 9.63/4.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.63/4.12  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.63/4.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.63/4.12  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.63/4.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.63/4.12  
% 9.63/4.13  tff(f_106, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 9.63/4.13  tff(f_96, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 9.63/4.13  tff(f_69, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 9.63/4.13  tff(f_62, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.63/4.13  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 9.63/4.13  tff(f_73, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 9.63/4.13  tff(f_71, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 9.63/4.13  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.63/4.13  tff(f_60, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 9.63/4.13  tff(f_35, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.63/4.13  tff(f_91, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 9.63/4.13  tff(f_42, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 9.63/4.13  tff(f_67, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (k4_xboole_0(B, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_xboole_1)).
% 9.63/4.13  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 9.63/4.13  tff(c_54, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.63/4.13  tff(c_52, plain, (k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.63/4.13  tff(c_50, plain, (![A_56, B_57]: (r1_xboole_0(k1_tarski(A_56), B_57) | r2_hidden(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.63/4.13  tff(c_26, plain, (![A_21]: (k5_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.63/4.13  tff(c_56, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.63/4.13  tff(c_22, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.63/4.13  tff(c_137, plain, (![B_68, A_69]: (k5_xboole_0(B_68, A_69)=k5_xboole_0(A_69, B_68))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.63/4.13  tff(c_153, plain, (![A_69]: (k5_xboole_0(k1_xboole_0, A_69)=A_69)), inference(superposition, [status(thm), theory('equality')], [c_137, c_26])).
% 9.63/4.13  tff(c_30, plain, (![A_25]: (k5_xboole_0(A_25, A_25)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.63/4.13  tff(c_417, plain, (![A_108, B_109, C_110]: (k5_xboole_0(k5_xboole_0(A_108, B_109), C_110)=k5_xboole_0(A_108, k5_xboole_0(B_109, C_110)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.63/4.13  tff(c_485, plain, (![A_25, C_110]: (k5_xboole_0(A_25, k5_xboole_0(A_25, C_110))=k5_xboole_0(k1_xboole_0, C_110))), inference(superposition, [status(thm), theory('equality')], [c_30, c_417])).
% 9.63/4.13  tff(c_506, plain, (![A_111, C_112]: (k5_xboole_0(A_111, k5_xboole_0(A_111, C_112))=C_112)), inference(demodulation, [status(thm), theory('equality')], [c_153, c_485])).
% 9.63/4.13  tff(c_971, plain, (![A_144, B_145]: (k5_xboole_0(A_144, k4_xboole_0(A_144, B_145))=k3_xboole_0(A_144, B_145))), inference(superposition, [status(thm), theory('equality')], [c_22, c_506])).
% 9.63/4.13  tff(c_1017, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_4'))=k5_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_56, c_971])).
% 9.63/4.13  tff(c_1024, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1017])).
% 9.63/4.13  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.63/4.13  tff(c_873, plain, (![A_119, B_120]: (r2_hidden('#skF_2'(A_119, B_120), k3_xboole_0(A_119, B_120)) | r1_xboole_0(A_119, B_120))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.63/4.13  tff(c_6, plain, (![B_8, A_5]: (~r2_hidden(B_8, A_5) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.63/4.13  tff(c_909, plain, (![A_127, B_128]: (~v1_xboole_0(k3_xboole_0(A_127, B_128)) | r1_xboole_0(A_127, B_128))), inference(resolution, [status(thm)], [c_873, c_6])).
% 9.63/4.13  tff(c_918, plain, (![B_2, A_1]: (~v1_xboole_0(k3_xboole_0(B_2, A_1)) | r1_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_909])).
% 9.63/4.13  tff(c_1028, plain, (~v1_xboole_0('#skF_3') | r1_xboole_0(k1_tarski('#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1024, c_918])).
% 9.63/4.13  tff(c_1057, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_1028])).
% 9.63/4.13  tff(c_8, plain, (![A_5]: (v1_xboole_0(A_5) | r2_hidden('#skF_1'(A_5), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.63/4.13  tff(c_252, plain, (![A_83, B_84, C_85]: (~r1_xboole_0(A_83, B_84) | ~r2_hidden(C_85, k3_xboole_0(A_83, B_84)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.63/4.13  tff(c_264, plain, (![A_86, B_87]: (~r1_xboole_0(A_86, B_87) | v1_xboole_0(k3_xboole_0(A_86, B_87)))), inference(resolution, [status(thm)], [c_8, c_252])).
% 9.63/4.13  tff(c_270, plain, (![A_1, B_2]: (~r1_xboole_0(A_1, B_2) | v1_xboole_0(k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_264])).
% 9.63/4.13  tff(c_1046, plain, (~r1_xboole_0(k1_tarski('#skF_4'), '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1024, c_270])).
% 9.63/4.13  tff(c_1067, plain, (~r1_xboole_0(k1_tarski('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1057, c_1046])).
% 9.63/4.13  tff(c_1071, plain, (r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_1067])).
% 9.63/4.13  tff(c_48, plain, (![A_54, B_55]: (r1_tarski(k1_tarski(A_54), B_55) | ~r2_hidden(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.63/4.13  tff(c_280, plain, (![A_90, B_91]: (r2_xboole_0(A_90, B_91) | B_91=A_90 | ~r1_tarski(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.63/4.13  tff(c_24, plain, (![B_20, A_19]: (k4_xboole_0(B_20, A_19)!=k1_xboole_0 | ~r2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.63/4.13  tff(c_1261, plain, (![B_157, A_158]: (k4_xboole_0(B_157, A_158)!=k1_xboole_0 | B_157=A_158 | ~r1_tarski(A_158, B_157))), inference(resolution, [status(thm)], [c_280, c_24])).
% 9.63/4.13  tff(c_14851, plain, (![B_257, A_258]: (k4_xboole_0(B_257, k1_tarski(A_258))!=k1_xboole_0 | k1_tarski(A_258)=B_257 | ~r2_hidden(A_258, B_257))), inference(resolution, [status(thm)], [c_48, c_1261])).
% 9.63/4.13  tff(c_14869, plain, (k1_tarski('#skF_4')='#skF_3' | ~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_56, c_14851])).
% 9.63/4.13  tff(c_14873, plain, (k1_tarski('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1071, c_14869])).
% 9.63/4.13  tff(c_14875, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_14873])).
% 9.63/4.13  tff(c_14877, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_1028])).
% 9.63/4.13  tff(c_16, plain, (![A_11]: (k1_xboole_0=A_11 | ~v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.63/4.13  tff(c_14880, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_14877, c_16])).
% 9.63/4.13  tff(c_14884, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_14880])).
% 9.63/4.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.63/4.13  
% 9.63/4.13  Inference rules
% 9.63/4.13  ----------------------
% 9.63/4.13  #Ref     : 0
% 9.63/4.13  #Sup     : 3814
% 9.63/4.13  #Fact    : 0
% 9.63/4.13  #Define  : 0
% 9.63/4.13  #Split   : 2
% 9.63/4.13  #Chain   : 0
% 9.63/4.13  #Close   : 0
% 9.63/4.13  
% 9.63/4.13  Ordering : KBO
% 9.63/4.13  
% 9.63/4.13  Simplification rules
% 9.63/4.13  ----------------------
% 9.63/4.13  #Subsume      : 428
% 9.63/4.13  #Demod        : 4186
% 9.63/4.13  #Tautology    : 1440
% 9.63/4.13  #SimpNegUnit  : 20
% 9.63/4.13  #BackRed      : 1
% 9.63/4.13  
% 9.63/4.13  #Partial instantiations: 0
% 9.63/4.13  #Strategies tried      : 1
% 9.63/4.13  
% 9.63/4.13  Timing (in seconds)
% 9.63/4.13  ----------------------
% 9.63/4.14  Preprocessing        : 0.33
% 9.63/4.14  Parsing              : 0.17
% 9.63/4.14  CNF conversion       : 0.02
% 9.63/4.14  Main loop            : 3.05
% 9.63/4.14  Inferencing          : 0.53
% 9.63/4.14  Reduction            : 2.01
% 9.63/4.14  Demodulation         : 1.86
% 9.63/4.14  BG Simplification    : 0.08
% 9.63/4.14  Subsumption          : 0.33
% 9.63/4.14  Abstraction          : 0.12
% 9.63/4.14  MUC search           : 0.00
% 9.63/4.14  Cooper               : 0.00
% 9.63/4.14  Total                : 3.41
% 9.63/4.14  Index Insertion      : 0.00
% 9.63/4.14  Index Deletion       : 0.00
% 9.63/4.14  Index Matching       : 0.00
% 9.63/4.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
