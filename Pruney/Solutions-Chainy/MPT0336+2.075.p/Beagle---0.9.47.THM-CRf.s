%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:10 EST 2020

% Result     : Theorem 7.28s
% Output     : CNFRefutation 7.59s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 120 expanded)
%              Number of leaves         :   28 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :   98 ( 195 expanded)
%              Number of equality atoms :   17 (  33 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_91,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_121,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_112,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
        & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_105,plain,(
    ! [A_50,B_51] :
      ( r1_xboole_0(A_50,B_51)
      | k4_xboole_0(A_50,B_51) != A_50 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_111,plain,(
    ! [B_51,A_50] :
      ( r1_xboole_0(B_51,A_50)
      | k4_xboole_0(A_50,B_51) != A_50 ) ),
    inference(resolution,[status(thm)],[c_105,c_4])).

tff(c_48,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_64,plain,(
    ! [B_46,A_47] :
      ( r1_xboole_0(B_46,A_47)
      | ~ r1_xboole_0(A_47,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_67,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_64])).

tff(c_1109,plain,(
    ! [A_120,C_121,B_122] :
      ( ~ r1_xboole_0(A_120,C_121)
      | ~ r1_xboole_0(A_120,B_122)
      | r1_xboole_0(A_120,k2_xboole_0(B_122,C_121)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_10580,plain,(
    ! [B_329,C_330,A_331] :
      ( r1_xboole_0(k2_xboole_0(B_329,C_330),A_331)
      | ~ r1_xboole_0(A_331,C_330)
      | ~ r1_xboole_0(A_331,B_329) ) ),
    inference(resolution,[status(thm)],[c_1109,c_4])).

tff(c_46,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_10607,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_10580,c_46])).

tff(c_10618,plain,(
    ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_10607])).

tff(c_10629,plain,(
    k4_xboole_0('#skF_2','#skF_3') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_111,c_10618])).

tff(c_113,plain,(
    ! [A_52,B_53] :
      ( k4_xboole_0(A_52,B_53) = A_52
      | ~ r1_xboole_0(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_124,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_67,c_113])).

tff(c_140,plain,(
    ! [A_54,B_55] :
      ( r1_xboole_0(k1_tarski(A_54),B_55)
      | r2_hidden(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_147,plain,(
    ! [B_55,A_54] :
      ( r1_xboole_0(B_55,k1_tarski(A_54))
      | r2_hidden(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_140,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_52,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_53,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_52])).

tff(c_157,plain,(
    ! [A_58,B_59] :
      ( k3_xboole_0(A_58,B_59) = A_58
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_172,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_53,c_157])).

tff(c_360,plain,(
    ! [A_79,B_80,C_81] :
      ( ~ r1_xboole_0(A_79,B_80)
      | r1_xboole_0(A_79,k3_xboole_0(B_80,C_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1134,plain,(
    ! [B_123,C_124,A_125] :
      ( r1_xboole_0(k3_xboole_0(B_123,C_124),A_125)
      | ~ r1_xboole_0(A_125,B_123) ) ),
    inference(resolution,[status(thm)],[c_360,c_4])).

tff(c_3728,plain,(
    ! [B_218,A_219,A_220] :
      ( r1_xboole_0(k3_xboole_0(B_218,A_219),A_220)
      | ~ r1_xboole_0(A_220,A_219) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1134])).

tff(c_9513,plain,(
    ! [A_300] :
      ( r1_xboole_0(k3_xboole_0('#skF_3','#skF_2'),A_300)
      | ~ r1_xboole_0(A_300,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_3728])).

tff(c_11047,plain,(
    ! [B_340] :
      ( r1_xboole_0(k3_xboole_0('#skF_3','#skF_2'),B_340)
      | r2_hidden('#skF_5',B_340) ) ),
    inference(resolution,[status(thm)],[c_147,c_9513])).

tff(c_218,plain,(
    ! [A_67,B_68] :
      ( ~ r1_xboole_0(k3_xboole_0(A_67,B_68),B_68)
      | r1_xboole_0(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_242,plain,(
    ! [A_1,B_2] :
      ( ~ r1_xboole_0(k3_xboole_0(A_1,B_2),A_1)
      | r1_xboole_0(B_2,A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_218])).

tff(c_11083,plain,
    ( r1_xboole_0('#skF_2','#skF_3')
    | r2_hidden('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_11047,c_242])).

tff(c_11106,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_11083])).

tff(c_50,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_32,plain,(
    ! [A_27,B_28] :
      ( r1_xboole_0(A_27,B_28)
      | k4_xboole_0(A_27,B_28) != A_27 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_564,plain,(
    ! [A_96,B_97,C_98] :
      ( ~ r1_xboole_0(A_96,B_97)
      | ~ r2_hidden(C_98,B_97)
      | ~ r2_hidden(C_98,A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_9855,plain,(
    ! [C_308,B_309,A_310] :
      ( ~ r2_hidden(C_308,B_309)
      | ~ r2_hidden(C_308,A_310)
      | k4_xboole_0(A_310,B_309) != A_310 ) ),
    inference(resolution,[status(thm)],[c_32,c_564])).

tff(c_9873,plain,(
    ! [A_310] :
      ( ~ r2_hidden('#skF_5',A_310)
      | k4_xboole_0(A_310,'#skF_4') != A_310 ) ),
    inference(resolution,[status(thm)],[c_50,c_9855])).

tff(c_11164,plain,(
    k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_11106,c_9873])).

tff(c_11178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_11164])).

tff(c_11179,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_11083])).

tff(c_30,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(A_27,B_28) = A_27
      | ~ r1_xboole_0(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_11185,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_11179,c_30])).

tff(c_11192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10629,c_11185])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:28:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.28/2.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.59/2.76  
% 7.59/2.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.59/2.76  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 7.59/2.76  
% 7.59/2.76  %Foreground sorts:
% 7.59/2.76  
% 7.59/2.76  
% 7.59/2.76  %Background operators:
% 7.59/2.76  
% 7.59/2.76  
% 7.59/2.76  %Foreground operators:
% 7.59/2.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.59/2.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.59/2.76  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.59/2.76  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.59/2.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.59/2.76  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.59/2.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.59/2.76  tff('#skF_5', type, '#skF_5': $i).
% 7.59/2.76  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.59/2.76  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.59/2.76  tff('#skF_2', type, '#skF_2': $i).
% 7.59/2.76  tff('#skF_3', type, '#skF_3': $i).
% 7.59/2.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.59/2.76  tff('#skF_4', type, '#skF_4': $i).
% 7.59/2.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.59/2.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.59/2.76  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.59/2.76  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.59/2.76  
% 7.59/2.78  tff(f_91, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 7.59/2.78  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 7.59/2.78  tff(f_121, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 7.59/2.78  tff(f_75, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 7.59/2.78  tff(f_112, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 7.59/2.78  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.59/2.78  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.59/2.78  tff(f_81, axiom, (![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_xboole_1)).
% 7.59/2.78  tff(f_87, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 7.59/2.78  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 7.59/2.78  tff(c_105, plain, (![A_50, B_51]: (r1_xboole_0(A_50, B_51) | k4_xboole_0(A_50, B_51)!=A_50)), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.59/2.78  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.59/2.78  tff(c_111, plain, (![B_51, A_50]: (r1_xboole_0(B_51, A_50) | k4_xboole_0(A_50, B_51)!=A_50)), inference(resolution, [status(thm)], [c_105, c_4])).
% 7.59/2.78  tff(c_48, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.59/2.78  tff(c_64, plain, (![B_46, A_47]: (r1_xboole_0(B_46, A_47) | ~r1_xboole_0(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.59/2.78  tff(c_67, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_64])).
% 7.59/2.78  tff(c_1109, plain, (![A_120, C_121, B_122]: (~r1_xboole_0(A_120, C_121) | ~r1_xboole_0(A_120, B_122) | r1_xboole_0(A_120, k2_xboole_0(B_122, C_121)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.59/2.78  tff(c_10580, plain, (![B_329, C_330, A_331]: (r1_xboole_0(k2_xboole_0(B_329, C_330), A_331) | ~r1_xboole_0(A_331, C_330) | ~r1_xboole_0(A_331, B_329))), inference(resolution, [status(thm)], [c_1109, c_4])).
% 7.59/2.78  tff(c_46, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.59/2.78  tff(c_10607, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_10580, c_46])).
% 7.59/2.78  tff(c_10618, plain, (~r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_10607])).
% 7.59/2.78  tff(c_10629, plain, (k4_xboole_0('#skF_2', '#skF_3')!='#skF_2'), inference(resolution, [status(thm)], [c_111, c_10618])).
% 7.59/2.78  tff(c_113, plain, (![A_52, B_53]: (k4_xboole_0(A_52, B_53)=A_52 | ~r1_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.59/2.78  tff(c_124, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_67, c_113])).
% 7.59/2.78  tff(c_140, plain, (![A_54, B_55]: (r1_xboole_0(k1_tarski(A_54), B_55) | r2_hidden(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.59/2.78  tff(c_147, plain, (![B_55, A_54]: (r1_xboole_0(B_55, k1_tarski(A_54)) | r2_hidden(A_54, B_55))), inference(resolution, [status(thm)], [c_140, c_4])).
% 7.59/2.78  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.59/2.78  tff(c_52, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.59/2.78  tff(c_53, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_52])).
% 7.59/2.78  tff(c_157, plain, (![A_58, B_59]: (k3_xboole_0(A_58, B_59)=A_58 | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.59/2.78  tff(c_172, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))=k3_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_53, c_157])).
% 7.59/2.78  tff(c_360, plain, (![A_79, B_80, C_81]: (~r1_xboole_0(A_79, B_80) | r1_xboole_0(A_79, k3_xboole_0(B_80, C_81)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.59/2.78  tff(c_1134, plain, (![B_123, C_124, A_125]: (r1_xboole_0(k3_xboole_0(B_123, C_124), A_125) | ~r1_xboole_0(A_125, B_123))), inference(resolution, [status(thm)], [c_360, c_4])).
% 7.59/2.78  tff(c_3728, plain, (![B_218, A_219, A_220]: (r1_xboole_0(k3_xboole_0(B_218, A_219), A_220) | ~r1_xboole_0(A_220, A_219))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1134])).
% 7.59/2.78  tff(c_9513, plain, (![A_300]: (r1_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), A_300) | ~r1_xboole_0(A_300, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_172, c_3728])).
% 7.59/2.78  tff(c_11047, plain, (![B_340]: (r1_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), B_340) | r2_hidden('#skF_5', B_340))), inference(resolution, [status(thm)], [c_147, c_9513])).
% 7.59/2.78  tff(c_218, plain, (![A_67, B_68]: (~r1_xboole_0(k3_xboole_0(A_67, B_68), B_68) | r1_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.59/2.78  tff(c_242, plain, (![A_1, B_2]: (~r1_xboole_0(k3_xboole_0(A_1, B_2), A_1) | r1_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_218])).
% 7.59/2.78  tff(c_11083, plain, (r1_xboole_0('#skF_2', '#skF_3') | r2_hidden('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_11047, c_242])).
% 7.59/2.78  tff(c_11106, plain, (r2_hidden('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_11083])).
% 7.59/2.78  tff(c_50, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.59/2.78  tff(c_32, plain, (![A_27, B_28]: (r1_xboole_0(A_27, B_28) | k4_xboole_0(A_27, B_28)!=A_27)), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.59/2.78  tff(c_564, plain, (![A_96, B_97, C_98]: (~r1_xboole_0(A_96, B_97) | ~r2_hidden(C_98, B_97) | ~r2_hidden(C_98, A_96))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.59/2.78  tff(c_9855, plain, (![C_308, B_309, A_310]: (~r2_hidden(C_308, B_309) | ~r2_hidden(C_308, A_310) | k4_xboole_0(A_310, B_309)!=A_310)), inference(resolution, [status(thm)], [c_32, c_564])).
% 7.59/2.78  tff(c_9873, plain, (![A_310]: (~r2_hidden('#skF_5', A_310) | k4_xboole_0(A_310, '#skF_4')!=A_310)), inference(resolution, [status(thm)], [c_50, c_9855])).
% 7.59/2.78  tff(c_11164, plain, (k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(resolution, [status(thm)], [c_11106, c_9873])).
% 7.59/2.78  tff(c_11178, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_11164])).
% 7.59/2.78  tff(c_11179, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_11083])).
% 7.59/2.78  tff(c_30, plain, (![A_27, B_28]: (k4_xboole_0(A_27, B_28)=A_27 | ~r1_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.59/2.78  tff(c_11185, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_11179, c_30])).
% 7.59/2.78  tff(c_11192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10629, c_11185])).
% 7.59/2.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.59/2.78  
% 7.59/2.78  Inference rules
% 7.59/2.78  ----------------------
% 7.59/2.78  #Ref     : 0
% 7.59/2.78  #Sup     : 2706
% 7.59/2.78  #Fact    : 0
% 7.59/2.78  #Define  : 0
% 7.59/2.78  #Split   : 7
% 7.59/2.78  #Chain   : 0
% 7.59/2.78  #Close   : 0
% 7.59/2.78  
% 7.59/2.78  Ordering : KBO
% 7.59/2.78  
% 7.59/2.78  Simplification rules
% 7.59/2.78  ----------------------
% 7.59/2.78  #Subsume      : 192
% 7.59/2.78  #Demod        : 1879
% 7.59/2.78  #Tautology    : 1478
% 7.59/2.78  #SimpNegUnit  : 4
% 7.59/2.78  #BackRed      : 0
% 7.59/2.78  
% 7.59/2.78  #Partial instantiations: 0
% 7.59/2.78  #Strategies tried      : 1
% 7.59/2.78  
% 7.59/2.78  Timing (in seconds)
% 7.59/2.78  ----------------------
% 7.59/2.78  Preprocessing        : 0.32
% 7.59/2.78  Parsing              : 0.17
% 7.59/2.78  CNF conversion       : 0.02
% 7.59/2.78  Main loop            : 1.69
% 7.59/2.78  Inferencing          : 0.43
% 7.59/2.78  Reduction            : 0.79
% 7.59/2.78  Demodulation         : 0.65
% 7.59/2.78  BG Simplification    : 0.05
% 7.59/2.78  Subsumption          : 0.31
% 7.59/2.78  Abstraction          : 0.06
% 7.59/2.78  MUC search           : 0.00
% 7.59/2.78  Cooper               : 0.00
% 7.59/2.78  Total                : 2.04
% 7.59/2.78  Index Insertion      : 0.00
% 7.59/2.78  Index Deletion       : 0.00
% 7.59/2.78  Index Matching       : 0.00
% 7.59/2.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
