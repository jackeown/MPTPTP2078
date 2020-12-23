%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:07 EST 2020

% Result     : Theorem 4.54s
% Output     : CNFRefutation 4.54s
% Verified   : 
% Statistics : Number of formulae       :   68 (  99 expanded)
%              Number of leaves         :   29 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :   82 ( 147 expanded)
%              Number of equality atoms :   29 (  50 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_247,plain,(
    ! [A_57,B_58] :
      ( r2_hidden('#skF_1'(A_57,B_58),A_57)
      | r1_xboole_0(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_36,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_150,plain,(
    ! [A_47,B_48] :
      ( k3_xboole_0(A_47,B_48) = k1_xboole_0
      | ~ r1_xboole_0(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_162,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_150])).

tff(c_16,plain,(
    ! [A_10,B_11,C_14] :
      ( ~ r1_xboole_0(A_10,B_11)
      | ~ r2_hidden(C_14,k3_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_176,plain,(
    ! [C_14] :
      ( ~ r1_xboole_0('#skF_5','#skF_4')
      | ~ r2_hidden(C_14,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_16])).

tff(c_192,plain,(
    ! [C_14] : ~ r2_hidden(C_14,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_176])).

tff(c_258,plain,(
    ! [B_59] : r1_xboole_0(k1_xboole_0,B_59) ),
    inference(resolution,[status(thm)],[c_247,c_192])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_262,plain,(
    ! [B_59] : k3_xboole_0(k1_xboole_0,B_59) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_258,c_4])).

tff(c_1119,plain,(
    ! [A_105,B_106,C_107] : k3_xboole_0(k3_xboole_0(A_105,B_106),C_107) = k3_xboole_0(A_105,k3_xboole_0(B_106,C_107)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1214,plain,(
    ! [C_107] : k3_xboole_0('#skF_5',k3_xboole_0('#skF_4',C_107)) = k3_xboole_0(k1_xboole_0,C_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_1119])).

tff(c_1248,plain,(
    ! [C_107] : k3_xboole_0('#skF_5',k3_xboole_0('#skF_4',C_107)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_1214])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_179,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_2])).

tff(c_1641,plain,(
    ! [A_116,B_117,C_118] :
      ( k3_xboole_0(A_116,k2_xboole_0(B_117,C_118)) = k3_xboole_0(A_116,C_118)
      | ~ r1_xboole_0(A_116,B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_144,plain,(
    ! [A_45,B_46] :
      ( r1_xboole_0(A_45,B_46)
      | k3_xboole_0(A_45,B_46) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_147,plain,(
    k3_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_144,c_34])).

tff(c_149,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_3','#skF_5')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_147])).

tff(c_1712,plain,
    ( k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1641,c_149])).

tff(c_1757,plain,(
    ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_1712])).

tff(c_1770,plain,(
    k3_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_1757])).

tff(c_30,plain,(
    ! [A_29,B_30] :
      ( r1_xboole_0(k1_tarski(A_29),B_30)
      | r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_423,plain,(
    ! [A_71,B_72] :
      ( k3_xboole_0(k1_tarski(A_71),B_72) = k1_xboole_0
      | r2_hidden(A_71,B_72) ) ),
    inference(resolution,[status(thm)],[c_30,c_150])).

tff(c_532,plain,(
    ! [A_77,A_78] :
      ( k3_xboole_0(A_77,k1_tarski(A_78)) = k1_xboole_0
      | r2_hidden(A_78,A_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_423])).

tff(c_40,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_41,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_40])).

tff(c_85,plain,(
    ! [A_38,B_39] :
      ( k3_xboole_0(A_38,B_39) = A_38
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_89,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_41,c_85])).

tff(c_558,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | r2_hidden('#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_532,c_89])).

tff(c_3288,plain,(
    r2_hidden('#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_1770,c_558])).

tff(c_38,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_389,plain,(
    ! [A_67,B_68,C_69] :
      ( ~ r1_xboole_0(A_67,B_68)
      | ~ r2_hidden(C_69,B_68)
      | ~ r2_hidden(C_69,A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3609,plain,(
    ! [C_138,B_139,A_140] :
      ( ~ r2_hidden(C_138,B_139)
      | ~ r2_hidden(C_138,A_140)
      | k3_xboole_0(A_140,B_139) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_389])).

tff(c_3631,plain,(
    ! [A_141] :
      ( ~ r2_hidden('#skF_6',A_141)
      | k3_xboole_0(A_141,'#skF_5') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_3609])).

tff(c_3634,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_3'),'#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3288,c_3631])).

tff(c_3644,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1248,c_2,c_3634])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:52:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.54/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.54/1.79  
% 4.54/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.54/1.80  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.54/1.80  
% 4.54/1.80  %Foreground sorts:
% 4.54/1.80  
% 4.54/1.80  
% 4.54/1.80  %Background operators:
% 4.54/1.80  
% 4.54/1.80  
% 4.54/1.80  %Foreground operators:
% 4.54/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.54/1.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.54/1.80  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.54/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.54/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.54/1.80  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.54/1.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.54/1.80  tff('#skF_5', type, '#skF_5': $i).
% 4.54/1.80  tff('#skF_6', type, '#skF_6': $i).
% 4.54/1.80  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.54/1.80  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.54/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.54/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.54/1.80  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.54/1.80  tff('#skF_4', type, '#skF_4': $i).
% 4.54/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.54/1.80  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.54/1.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.54/1.80  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.54/1.80  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.54/1.80  
% 4.54/1.81  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.54/1.81  tff(f_95, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 4.54/1.81  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.54/1.81  tff(f_63, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.54/1.81  tff(f_65, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 4.54/1.81  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.54/1.81  tff(f_73, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_xboole_1)).
% 4.54/1.81  tff(f_84, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 4.54/1.81  tff(f_69, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.54/1.81  tff(c_247, plain, (![A_57, B_58]: (r2_hidden('#skF_1'(A_57, B_58), A_57) | r1_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.54/1.81  tff(c_36, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.54/1.81  tff(c_150, plain, (![A_47, B_48]: (k3_xboole_0(A_47, B_48)=k1_xboole_0 | ~r1_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.54/1.81  tff(c_162, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_150])).
% 4.54/1.81  tff(c_16, plain, (![A_10, B_11, C_14]: (~r1_xboole_0(A_10, B_11) | ~r2_hidden(C_14, k3_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.54/1.81  tff(c_176, plain, (![C_14]: (~r1_xboole_0('#skF_5', '#skF_4') | ~r2_hidden(C_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_162, c_16])).
% 4.54/1.81  tff(c_192, plain, (![C_14]: (~r2_hidden(C_14, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_176])).
% 4.54/1.81  tff(c_258, plain, (![B_59]: (r1_xboole_0(k1_xboole_0, B_59))), inference(resolution, [status(thm)], [c_247, c_192])).
% 4.54/1.81  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.54/1.81  tff(c_262, plain, (![B_59]: (k3_xboole_0(k1_xboole_0, B_59)=k1_xboole_0)), inference(resolution, [status(thm)], [c_258, c_4])).
% 4.54/1.81  tff(c_1119, plain, (![A_105, B_106, C_107]: (k3_xboole_0(k3_xboole_0(A_105, B_106), C_107)=k3_xboole_0(A_105, k3_xboole_0(B_106, C_107)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.54/1.81  tff(c_1214, plain, (![C_107]: (k3_xboole_0('#skF_5', k3_xboole_0('#skF_4', C_107))=k3_xboole_0(k1_xboole_0, C_107))), inference(superposition, [status(thm), theory('equality')], [c_162, c_1119])).
% 4.54/1.81  tff(c_1248, plain, (![C_107]: (k3_xboole_0('#skF_5', k3_xboole_0('#skF_4', C_107))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_262, c_1214])).
% 4.54/1.81  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.54/1.81  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.54/1.81  tff(c_179, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_162, c_2])).
% 4.54/1.81  tff(c_1641, plain, (![A_116, B_117, C_118]: (k3_xboole_0(A_116, k2_xboole_0(B_117, C_118))=k3_xboole_0(A_116, C_118) | ~r1_xboole_0(A_116, B_117))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.54/1.81  tff(c_144, plain, (![A_45, B_46]: (r1_xboole_0(A_45, B_46) | k3_xboole_0(A_45, B_46)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.54/1.81  tff(c_34, plain, (~r1_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.54/1.81  tff(c_147, plain, (k3_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_144, c_34])).
% 4.54/1.81  tff(c_149, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_3', '#skF_5'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_147])).
% 4.54/1.81  tff(c_1712, plain, (k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0 | ~r1_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1641, c_149])).
% 4.54/1.81  tff(c_1757, plain, (~r1_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_1712])).
% 4.54/1.81  tff(c_1770, plain, (k3_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_1757])).
% 4.54/1.81  tff(c_30, plain, (![A_29, B_30]: (r1_xboole_0(k1_tarski(A_29), B_30) | r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.54/1.81  tff(c_423, plain, (![A_71, B_72]: (k3_xboole_0(k1_tarski(A_71), B_72)=k1_xboole_0 | r2_hidden(A_71, B_72))), inference(resolution, [status(thm)], [c_30, c_150])).
% 4.54/1.81  tff(c_532, plain, (![A_77, A_78]: (k3_xboole_0(A_77, k1_tarski(A_78))=k1_xboole_0 | r2_hidden(A_78, A_77))), inference(superposition, [status(thm), theory('equality')], [c_2, c_423])).
% 4.54/1.81  tff(c_40, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.54/1.81  tff(c_41, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_40])).
% 4.54/1.81  tff(c_85, plain, (![A_38, B_39]: (k3_xboole_0(A_38, B_39)=A_38 | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.54/1.81  tff(c_89, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))=k3_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_41, c_85])).
% 4.54/1.81  tff(c_558, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0 | r2_hidden('#skF_6', k3_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_532, c_89])).
% 4.54/1.81  tff(c_3288, plain, (r2_hidden('#skF_6', k3_xboole_0('#skF_4', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1770, c_558])).
% 4.54/1.81  tff(c_38, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.54/1.81  tff(c_389, plain, (![A_67, B_68, C_69]: (~r1_xboole_0(A_67, B_68) | ~r2_hidden(C_69, B_68) | ~r2_hidden(C_69, A_67))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.54/1.81  tff(c_3609, plain, (![C_138, B_139, A_140]: (~r2_hidden(C_138, B_139) | ~r2_hidden(C_138, A_140) | k3_xboole_0(A_140, B_139)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_389])).
% 4.54/1.81  tff(c_3631, plain, (![A_141]: (~r2_hidden('#skF_6', A_141) | k3_xboole_0(A_141, '#skF_5')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_3609])).
% 4.54/1.81  tff(c_3634, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_3288, c_3631])).
% 4.54/1.81  tff(c_3644, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1248, c_2, c_3634])).
% 4.54/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.54/1.81  
% 4.54/1.81  Inference rules
% 4.54/1.81  ----------------------
% 4.54/1.81  #Ref     : 0
% 4.54/1.81  #Sup     : 904
% 4.54/1.81  #Fact    : 0
% 4.54/1.81  #Define  : 0
% 4.54/1.81  #Split   : 0
% 4.54/1.81  #Chain   : 0
% 4.54/1.81  #Close   : 0
% 4.54/1.81  
% 4.54/1.81  Ordering : KBO
% 4.54/1.81  
% 4.54/1.81  Simplification rules
% 4.54/1.81  ----------------------
% 4.54/1.81  #Subsume      : 98
% 4.54/1.81  #Demod        : 635
% 4.54/1.81  #Tautology    : 508
% 4.54/1.81  #SimpNegUnit  : 40
% 4.54/1.81  #BackRed      : 1
% 4.54/1.81  
% 4.54/1.81  #Partial instantiations: 0
% 4.54/1.81  #Strategies tried      : 1
% 4.54/1.81  
% 4.54/1.81  Timing (in seconds)
% 4.54/1.81  ----------------------
% 4.54/1.81  Preprocessing        : 0.31
% 4.54/1.81  Parsing              : 0.17
% 4.54/1.81  CNF conversion       : 0.02
% 4.54/1.81  Main loop            : 0.72
% 4.54/1.81  Inferencing          : 0.21
% 4.54/1.81  Reduction            : 0.33
% 4.54/1.81  Demodulation         : 0.27
% 4.54/1.81  BG Simplification    : 0.03
% 4.54/1.81  Subsumption          : 0.11
% 4.54/1.81  Abstraction          : 0.03
% 4.54/1.81  MUC search           : 0.00
% 4.54/1.81  Cooper               : 0.00
% 4.54/1.81  Total                : 1.06
% 4.54/1.81  Index Insertion      : 0.00
% 4.54/1.81  Index Deletion       : 0.00
% 4.54/1.81  Index Matching       : 0.00
% 4.54/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
