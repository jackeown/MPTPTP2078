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
% DateTime   : Thu Dec  3 09:55:08 EST 2020

% Result     : Theorem 3.96s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 119 expanded)
%              Number of leaves         :   30 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :   90 ( 177 expanded)
%              Number of equality atoms :   23 (  49 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_49,axiom,(
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

tff(f_92,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
        & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

tff(c_40,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_38,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_371,plain,(
    ! [A_71,B_72,C_73] :
      ( ~ r1_xboole_0(A_71,B_72)
      | ~ r2_hidden(C_73,B_72)
      | ~ r2_hidden(C_73,A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_393,plain,(
    ! [C_74] :
      ( ~ r2_hidden(C_74,'#skF_4')
      | ~ r2_hidden(C_74,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_38,c_371])).

tff(c_407,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_393])).

tff(c_34,plain,(
    ! [A_35,B_36] :
      ( r1_xboole_0(k1_tarski(A_35),B_36)
      | r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_22,plain,(
    ! [A_19,B_20,C_21] :
      ( ~ r1_xboole_0(A_19,B_20)
      | r1_xboole_0(A_19,k3_xboole_0(B_20,C_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_599,plain,(
    ! [A_96,B_97] :
      ( r2_hidden('#skF_2'(A_96,B_97),k3_xboole_0(A_96,B_97))
      | r1_xboole_0(A_96,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_219,plain,(
    ! [A_63,B_64,C_65] :
      ( ~ r1_xboole_0(A_63,B_64)
      | ~ r2_hidden(C_65,k3_xboole_0(A_63,B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_245,plain,(
    ! [B_2,A_1,C_65] :
      ( ~ r1_xboole_0(B_2,A_1)
      | ~ r2_hidden(C_65,k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_219])).

tff(c_648,plain,(
    ! [B_98,A_99] :
      ( ~ r1_xboole_0(B_98,A_99)
      | r1_xboole_0(A_99,B_98) ) ),
    inference(resolution,[status(thm)],[c_599,c_245])).

tff(c_673,plain,(
    ! [B_20,C_21,A_19] :
      ( r1_xboole_0(k3_xboole_0(B_20,C_21),A_19)
      | ~ r1_xboole_0(A_19,B_20) ) ),
    inference(resolution,[status(thm)],[c_22,c_648])).

tff(c_42,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_43,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_42])).

tff(c_105,plain,(
    ! [A_46,B_47] :
      ( k2_xboole_0(A_46,B_47) = B_47
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_109,plain,(
    k2_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(resolution,[status(thm)],[c_43,c_105])).

tff(c_20,plain,(
    ! [A_17,B_18] : k3_xboole_0(A_17,k2_xboole_0(A_17,B_18)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_239,plain,(
    ! [A_17,B_18,C_65] :
      ( ~ r1_xboole_0(A_17,k2_xboole_0(A_17,B_18))
      | ~ r2_hidden(C_65,A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_219])).

tff(c_542,plain,(
    ! [C_65] :
      ( ~ r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6'))
      | ~ r2_hidden(C_65,k3_xboole_0('#skF_4','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_239])).

tff(c_2480,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_542])).

tff(c_2520,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_673,c_2480])).

tff(c_2549,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_2520])).

tff(c_2558,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_407,c_2549])).

tff(c_2559,plain,(
    ! [C_65] : ~ r2_hidden(C_65,k3_xboole_0('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_542])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_116,plain,(
    ! [A_50,B_51] :
      ( k3_xboole_0(A_50,B_51) = k1_xboole_0
      | ~ r1_xboole_0(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_116])).

tff(c_132,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_2])).

tff(c_914,plain,(
    ! [A_119,B_120,C_121] :
      ( k3_xboole_0(A_119,k2_xboole_0(B_120,C_121)) = k3_xboole_0(A_119,C_121)
      | ~ r1_xboole_0(A_119,B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_110,plain,(
    ! [A_48,B_49] :
      ( r1_xboole_0(A_48,B_49)
      | k3_xboole_0(A_48,B_49) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_113,plain,(
    k3_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_110,c_36])).

tff(c_115,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_3','#skF_5')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_113])).

tff(c_944,plain,
    ( k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_914,c_115])).

tff(c_982,plain,(
    ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_944])).

tff(c_1001,plain,(
    k3_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_982])).

tff(c_545,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_20])).

tff(c_1311,plain,(
    ! [A_140,B_141] :
      ( k3_xboole_0(k1_tarski(A_140),B_141) = k1_xboole_0
      | r2_hidden(A_140,B_141) ) ),
    inference(resolution,[status(thm)],[c_34,c_116])).

tff(c_1358,plain,(
    ! [B_141,A_140] :
      ( k3_xboole_0(B_141,k1_tarski(A_140)) = k1_xboole_0
      | r2_hidden(A_140,B_141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1311,c_2])).

tff(c_1882,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | r2_hidden('#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_545,c_1358])).

tff(c_1960,plain,(
    r2_hidden('#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_1001,c_1882])).

tff(c_2562,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2559,c_1960])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:29:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.96/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.96/1.71  
% 3.96/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.96/1.71  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.96/1.71  
% 3.96/1.71  %Foreground sorts:
% 3.96/1.71  
% 3.96/1.71  
% 3.96/1.71  %Background operators:
% 3.96/1.71  
% 3.96/1.71  
% 3.96/1.71  %Foreground operators:
% 3.96/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.96/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.96/1.71  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.96/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.96/1.71  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.96/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.96/1.71  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.96/1.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.96/1.71  tff('#skF_5', type, '#skF_5': $i).
% 3.96/1.71  tff('#skF_6', type, '#skF_6': $i).
% 3.96/1.71  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.96/1.71  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.96/1.71  tff('#skF_3', type, '#skF_3': $i).
% 3.96/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.96/1.71  tff('#skF_4', type, '#skF_4': $i).
% 3.96/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.96/1.71  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.96/1.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.96/1.71  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.96/1.71  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.96/1.71  
% 3.96/1.73  tff(f_101, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 3.96/1.73  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.96/1.73  tff(f_92, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.96/1.73  tff(f_75, axiom, (![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_xboole_1)).
% 3.96/1.73  tff(f_63, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.96/1.73  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.96/1.73  tff(f_67, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.96/1.73  tff(f_69, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 3.96/1.73  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.96/1.73  tff(f_79, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_xboole_1)).
% 3.96/1.73  tff(c_40, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.96/1.73  tff(c_38, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.96/1.73  tff(c_371, plain, (![A_71, B_72, C_73]: (~r1_xboole_0(A_71, B_72) | ~r2_hidden(C_73, B_72) | ~r2_hidden(C_73, A_71))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.96/1.73  tff(c_393, plain, (![C_74]: (~r2_hidden(C_74, '#skF_4') | ~r2_hidden(C_74, '#skF_5'))), inference(resolution, [status(thm)], [c_38, c_371])).
% 3.96/1.73  tff(c_407, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_393])).
% 3.96/1.73  tff(c_34, plain, (![A_35, B_36]: (r1_xboole_0(k1_tarski(A_35), B_36) | r2_hidden(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.96/1.73  tff(c_22, plain, (![A_19, B_20, C_21]: (~r1_xboole_0(A_19, B_20) | r1_xboole_0(A_19, k3_xboole_0(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.96/1.73  tff(c_599, plain, (![A_96, B_97]: (r2_hidden('#skF_2'(A_96, B_97), k3_xboole_0(A_96, B_97)) | r1_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.96/1.73  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.96/1.73  tff(c_219, plain, (![A_63, B_64, C_65]: (~r1_xboole_0(A_63, B_64) | ~r2_hidden(C_65, k3_xboole_0(A_63, B_64)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.96/1.73  tff(c_245, plain, (![B_2, A_1, C_65]: (~r1_xboole_0(B_2, A_1) | ~r2_hidden(C_65, k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_219])).
% 3.96/1.73  tff(c_648, plain, (![B_98, A_99]: (~r1_xboole_0(B_98, A_99) | r1_xboole_0(A_99, B_98))), inference(resolution, [status(thm)], [c_599, c_245])).
% 3.96/1.73  tff(c_673, plain, (![B_20, C_21, A_19]: (r1_xboole_0(k3_xboole_0(B_20, C_21), A_19) | ~r1_xboole_0(A_19, B_20))), inference(resolution, [status(thm)], [c_22, c_648])).
% 3.96/1.73  tff(c_42, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.96/1.73  tff(c_43, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_42])).
% 3.96/1.73  tff(c_105, plain, (![A_46, B_47]: (k2_xboole_0(A_46, B_47)=B_47 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.96/1.73  tff(c_109, plain, (k2_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(resolution, [status(thm)], [c_43, c_105])).
% 3.96/1.73  tff(c_20, plain, (![A_17, B_18]: (k3_xboole_0(A_17, k2_xboole_0(A_17, B_18))=A_17)), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.96/1.73  tff(c_239, plain, (![A_17, B_18, C_65]: (~r1_xboole_0(A_17, k2_xboole_0(A_17, B_18)) | ~r2_hidden(C_65, A_17))), inference(superposition, [status(thm), theory('equality')], [c_20, c_219])).
% 3.96/1.73  tff(c_542, plain, (![C_65]: (~r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6')) | ~r2_hidden(C_65, k3_xboole_0('#skF_4', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_109, c_239])).
% 3.96/1.73  tff(c_2480, plain, (~r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))), inference(splitLeft, [status(thm)], [c_542])).
% 3.96/1.73  tff(c_2520, plain, (~r1_xboole_0(k1_tarski('#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_673, c_2480])).
% 3.96/1.73  tff(c_2549, plain, (r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_2520])).
% 3.96/1.73  tff(c_2558, plain, $false, inference(negUnitSimplification, [status(thm)], [c_407, c_2549])).
% 3.96/1.73  tff(c_2559, plain, (![C_65]: (~r2_hidden(C_65, k3_xboole_0('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_542])).
% 3.96/1.73  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.96/1.73  tff(c_116, plain, (![A_50, B_51]: (k3_xboole_0(A_50, B_51)=k1_xboole_0 | ~r1_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.96/1.73  tff(c_128, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_116])).
% 3.96/1.73  tff(c_132, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_128, c_2])).
% 3.96/1.73  tff(c_914, plain, (![A_119, B_120, C_121]: (k3_xboole_0(A_119, k2_xboole_0(B_120, C_121))=k3_xboole_0(A_119, C_121) | ~r1_xboole_0(A_119, B_120))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.96/1.73  tff(c_110, plain, (![A_48, B_49]: (r1_xboole_0(A_48, B_49) | k3_xboole_0(A_48, B_49)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.96/1.73  tff(c_36, plain, (~r1_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.96/1.73  tff(c_113, plain, (k3_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_110, c_36])).
% 3.96/1.73  tff(c_115, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_3', '#skF_5'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_113])).
% 3.96/1.73  tff(c_944, plain, (k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0 | ~r1_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_914, c_115])).
% 3.96/1.73  tff(c_982, plain, (~r1_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_944])).
% 3.96/1.73  tff(c_1001, plain, (k3_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_982])).
% 3.96/1.73  tff(c_545, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_109, c_20])).
% 3.96/1.73  tff(c_1311, plain, (![A_140, B_141]: (k3_xboole_0(k1_tarski(A_140), B_141)=k1_xboole_0 | r2_hidden(A_140, B_141))), inference(resolution, [status(thm)], [c_34, c_116])).
% 3.96/1.73  tff(c_1358, plain, (![B_141, A_140]: (k3_xboole_0(B_141, k1_tarski(A_140))=k1_xboole_0 | r2_hidden(A_140, B_141))), inference(superposition, [status(thm), theory('equality')], [c_1311, c_2])).
% 3.96/1.73  tff(c_1882, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0 | r2_hidden('#skF_6', k3_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_545, c_1358])).
% 3.96/1.73  tff(c_1960, plain, (r2_hidden('#skF_6', k3_xboole_0('#skF_4', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1001, c_1882])).
% 3.96/1.73  tff(c_2562, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2559, c_1960])).
% 3.96/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.96/1.73  
% 3.96/1.73  Inference rules
% 3.96/1.73  ----------------------
% 3.96/1.73  #Ref     : 1
% 3.96/1.73  #Sup     : 653
% 3.96/1.73  #Fact    : 0
% 3.96/1.73  #Define  : 0
% 3.96/1.73  #Split   : 2
% 3.96/1.73  #Chain   : 0
% 3.96/1.73  #Close   : 0
% 3.96/1.73  
% 3.96/1.73  Ordering : KBO
% 3.96/1.73  
% 3.96/1.73  Simplification rules
% 3.96/1.73  ----------------------
% 3.96/1.73  #Subsume      : 254
% 3.96/1.73  #Demod        : 153
% 3.96/1.73  #Tautology    : 205
% 3.96/1.73  #SimpNegUnit  : 38
% 3.96/1.73  #BackRed      : 1
% 3.96/1.73  
% 3.96/1.73  #Partial instantiations: 0
% 3.96/1.73  #Strategies tried      : 1
% 3.96/1.73  
% 3.96/1.73  Timing (in seconds)
% 3.96/1.73  ----------------------
% 3.96/1.73  Preprocessing        : 0.31
% 3.96/1.73  Parsing              : 0.17
% 3.96/1.73  CNF conversion       : 0.02
% 3.96/1.73  Main loop            : 0.60
% 3.96/1.73  Inferencing          : 0.20
% 3.96/1.73  Reduction            : 0.22
% 3.96/1.73  Demodulation         : 0.16
% 3.96/1.73  BG Simplification    : 0.02
% 3.96/1.73  Subsumption          : 0.12
% 3.96/1.73  Abstraction          : 0.03
% 3.96/1.73  MUC search           : 0.00
% 3.96/1.73  Cooper               : 0.00
% 3.96/1.73  Total                : 0.94
% 3.96/1.73  Index Insertion      : 0.00
% 3.96/1.73  Index Deletion       : 0.00
% 3.96/1.73  Index Matching       : 0.00
% 3.96/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
