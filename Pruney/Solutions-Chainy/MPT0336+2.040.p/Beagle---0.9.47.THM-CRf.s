%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:05 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :   67 (  82 expanded)
%              Number of leaves         :   32 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :   81 ( 112 expanded)
%              Number of equality atoms :   27 (  37 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_76,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_53,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

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

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_148,plain,(
    ! [A_54,B_55] :
      ( k3_xboole_0(A_54,B_55) = k1_xboole_0
      | ~ r1_xboole_0(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_159,plain,(
    k3_xboole_0('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_148])).

tff(c_432,plain,(
    ! [A_84,B_85,C_86] :
      ( k3_xboole_0(A_84,k2_xboole_0(B_85,C_86)) = k3_xboole_0(A_84,C_86)
      | ~ r1_xboole_0(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_142,plain,(
    ! [A_52,B_53] :
      ( r1_xboole_0(A_52,B_53)
      | k3_xboole_0(A_52,B_53) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_145,plain,(
    k3_xboole_0(k2_xboole_0('#skF_4','#skF_6'),'#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_142,c_54])).

tff(c_147,plain,(
    k3_xboole_0('#skF_5',k2_xboole_0('#skF_4','#skF_6')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_145])).

tff(c_442,plain,
    ( k3_xboole_0('#skF_5','#skF_6') != k1_xboole_0
    | ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_147])).

tff(c_476,plain,(
    ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_2,c_442])).

tff(c_482,plain,(
    k3_xboole_0('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_476])).

tff(c_484,plain,(
    k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_482])).

tff(c_60,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_287,plain,(
    ! [B_69,A_70] :
      ( k1_tarski(B_69) = A_70
      | k1_xboole_0 = A_70
      | ~ r1_tarski(A_70,k1_tarski(B_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_308,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_7')
    | k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_287])).

tff(c_508,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_484,c_308])).

tff(c_84,plain,(
    ! [B_46,A_47] : k3_xboole_0(B_46,A_47) = k3_xboole_0(A_47,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_tarski(k3_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_99,plain,(
    ! [B_46,A_47] : r1_tarski(k3_xboole_0(B_46,A_47),A_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_14])).

tff(c_515,plain,(
    r1_tarski(k1_tarski('#skF_7'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_508,c_99])).

tff(c_67,plain,(
    ! [A_44] : k2_tarski(A_44,A_44) = k1_tarski(A_44) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_24,plain,(
    ! [D_24,A_19] : r2_hidden(D_24,k2_tarski(A_19,D_24)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_73,plain,(
    ! [A_44] : r2_hidden(A_44,k1_tarski(A_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_24])).

tff(c_58,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_16,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_536,plain,(
    ! [A_90,B_91,C_92] :
      ( ~ r1_xboole_0(A_90,k3_xboole_0(B_91,C_92))
      | ~ r1_tarski(A_90,C_92)
      | r1_xboole_0(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_558,plain,(
    ! [A_90] :
      ( ~ r1_xboole_0(A_90,k1_xboole_0)
      | ~ r1_tarski(A_90,'#skF_5')
      | r1_xboole_0(A_90,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_536])).

tff(c_581,plain,(
    ! [A_93] :
      ( ~ r1_tarski(A_93,'#skF_5')
      | r1_xboole_0(A_93,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_558])).

tff(c_8,plain,(
    ! [A_5,B_6,C_9] :
      ( ~ r1_xboole_0(A_5,B_6)
      | ~ r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_881,plain,(
    ! [C_110,A_111] :
      ( ~ r2_hidden(C_110,'#skF_6')
      | ~ r2_hidden(C_110,A_111)
      | ~ r1_tarski(A_111,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_581,c_8])).

tff(c_893,plain,(
    ! [A_112] :
      ( ~ r2_hidden('#skF_7',A_112)
      | ~ r1_tarski(A_112,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_881])).

tff(c_897,plain,(
    ~ r1_tarski(k1_tarski('#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_73,c_893])).

tff(c_912,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_515,c_897])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:28:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.41  
% 2.65/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.42  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.65/1.42  
% 2.65/1.42  %Foreground sorts:
% 2.65/1.42  
% 2.65/1.42  
% 2.65/1.42  %Background operators:
% 2.65/1.42  
% 2.65/1.42  
% 2.65/1.42  %Foreground operators:
% 2.65/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.65/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.65/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.65/1.42  tff('#skF_7', type, '#skF_7': $i).
% 2.65/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.65/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.65/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.65/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.65/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.65/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.65/1.42  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.65/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.42  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.65/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.65/1.42  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.65/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.65/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.65/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.65/1.42  
% 2.93/1.43  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.93/1.43  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.93/1.43  tff(f_97, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 2.93/1.43  tff(f_65, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 2.93/1.43  tff(f_86, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.93/1.43  tff(f_51, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.93/1.43  tff(f_76, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.93/1.43  tff(f_74, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.93/1.43  tff(f_53, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.93/1.43  tff(f_61, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 2.93/1.43  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.93/1.43  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.93/1.43  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.93/1.43  tff(c_56, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.93/1.43  tff(c_148, plain, (![A_54, B_55]: (k3_xboole_0(A_54, B_55)=k1_xboole_0 | ~r1_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.93/1.43  tff(c_159, plain, (k3_xboole_0('#skF_6', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_148])).
% 2.93/1.43  tff(c_432, plain, (![A_84, B_85, C_86]: (k3_xboole_0(A_84, k2_xboole_0(B_85, C_86))=k3_xboole_0(A_84, C_86) | ~r1_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.93/1.43  tff(c_142, plain, (![A_52, B_53]: (r1_xboole_0(A_52, B_53) | k3_xboole_0(A_52, B_53)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.93/1.43  tff(c_54, plain, (~r1_xboole_0(k2_xboole_0('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.93/1.43  tff(c_145, plain, (k3_xboole_0(k2_xboole_0('#skF_4', '#skF_6'), '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_142, c_54])).
% 2.93/1.43  tff(c_147, plain, (k3_xboole_0('#skF_5', k2_xboole_0('#skF_4', '#skF_6'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_145])).
% 2.93/1.43  tff(c_442, plain, (k3_xboole_0('#skF_5', '#skF_6')!=k1_xboole_0 | ~r1_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_432, c_147])).
% 2.93/1.43  tff(c_476, plain, (~r1_xboole_0('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_2, c_442])).
% 2.93/1.43  tff(c_482, plain, (k3_xboole_0('#skF_5', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_476])).
% 2.93/1.43  tff(c_484, plain, (k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_482])).
% 2.93/1.43  tff(c_60, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.93/1.43  tff(c_287, plain, (![B_69, A_70]: (k1_tarski(B_69)=A_70 | k1_xboole_0=A_70 | ~r1_tarski(A_70, k1_tarski(B_69)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.93/1.43  tff(c_308, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_7') | k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_60, c_287])).
% 2.93/1.43  tff(c_508, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_484, c_308])).
% 2.93/1.43  tff(c_84, plain, (![B_46, A_47]: (k3_xboole_0(B_46, A_47)=k3_xboole_0(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.93/1.43  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(k3_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.93/1.43  tff(c_99, plain, (![B_46, A_47]: (r1_tarski(k3_xboole_0(B_46, A_47), A_47))), inference(superposition, [status(thm), theory('equality')], [c_84, c_14])).
% 2.93/1.43  tff(c_515, plain, (r1_tarski(k1_tarski('#skF_7'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_508, c_99])).
% 2.93/1.43  tff(c_67, plain, (![A_44]: (k2_tarski(A_44, A_44)=k1_tarski(A_44))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.93/1.43  tff(c_24, plain, (![D_24, A_19]: (r2_hidden(D_24, k2_tarski(A_19, D_24)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.93/1.43  tff(c_73, plain, (![A_44]: (r2_hidden(A_44, k1_tarski(A_44)))), inference(superposition, [status(thm), theory('equality')], [c_67, c_24])).
% 2.93/1.43  tff(c_58, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.93/1.43  tff(c_16, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.93/1.43  tff(c_536, plain, (![A_90, B_91, C_92]: (~r1_xboole_0(A_90, k3_xboole_0(B_91, C_92)) | ~r1_tarski(A_90, C_92) | r1_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.93/1.43  tff(c_558, plain, (![A_90]: (~r1_xboole_0(A_90, k1_xboole_0) | ~r1_tarski(A_90, '#skF_5') | r1_xboole_0(A_90, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_159, c_536])).
% 2.93/1.43  tff(c_581, plain, (![A_93]: (~r1_tarski(A_93, '#skF_5') | r1_xboole_0(A_93, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_558])).
% 2.93/1.43  tff(c_8, plain, (![A_5, B_6, C_9]: (~r1_xboole_0(A_5, B_6) | ~r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.93/1.43  tff(c_881, plain, (![C_110, A_111]: (~r2_hidden(C_110, '#skF_6') | ~r2_hidden(C_110, A_111) | ~r1_tarski(A_111, '#skF_5'))), inference(resolution, [status(thm)], [c_581, c_8])).
% 2.93/1.43  tff(c_893, plain, (![A_112]: (~r2_hidden('#skF_7', A_112) | ~r1_tarski(A_112, '#skF_5'))), inference(resolution, [status(thm)], [c_58, c_881])).
% 2.93/1.43  tff(c_897, plain, (~r1_tarski(k1_tarski('#skF_7'), '#skF_5')), inference(resolution, [status(thm)], [c_73, c_893])).
% 2.93/1.43  tff(c_912, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_515, c_897])).
% 2.93/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.43  
% 2.93/1.43  Inference rules
% 2.93/1.43  ----------------------
% 2.93/1.43  #Ref     : 0
% 2.93/1.43  #Sup     : 200
% 2.93/1.43  #Fact    : 0
% 2.93/1.43  #Define  : 0
% 2.93/1.43  #Split   : 0
% 2.93/1.43  #Chain   : 0
% 2.93/1.43  #Close   : 0
% 2.93/1.43  
% 2.93/1.43  Ordering : KBO
% 2.93/1.43  
% 2.93/1.43  Simplification rules
% 2.93/1.43  ----------------------
% 2.93/1.43  #Subsume      : 4
% 2.93/1.43  #Demod        : 87
% 2.93/1.43  #Tautology    : 118
% 2.93/1.43  #SimpNegUnit  : 1
% 2.93/1.43  #BackRed      : 2
% 2.93/1.43  
% 2.93/1.43  #Partial instantiations: 0
% 2.93/1.43  #Strategies tried      : 1
% 2.93/1.43  
% 2.93/1.43  Timing (in seconds)
% 2.93/1.43  ----------------------
% 2.93/1.43  Preprocessing        : 0.33
% 2.93/1.43  Parsing              : 0.17
% 2.93/1.43  CNF conversion       : 0.02
% 2.93/1.43  Main loop            : 0.33
% 2.93/1.43  Inferencing          : 0.12
% 2.93/1.43  Reduction            : 0.12
% 2.93/1.43  Demodulation         : 0.09
% 2.93/1.43  BG Simplification    : 0.02
% 2.93/1.43  Subsumption          : 0.06
% 2.93/1.43  Abstraction          : 0.02
% 2.93/1.43  MUC search           : 0.00
% 2.93/1.43  Cooper               : 0.00
% 2.93/1.43  Total                : 0.69
% 2.93/1.44  Index Insertion      : 0.00
% 2.93/1.44  Index Deletion       : 0.00
% 2.93/1.44  Index Matching       : 0.00
% 2.93/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
