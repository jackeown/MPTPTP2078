%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:34 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 103 expanded)
%              Number of leaves         :   33 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :   80 ( 126 expanded)
%              Number of equality atoms :   33 (  62 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_69,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_71,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_82,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_56,plain,(
    ! [A_23] : k2_tarski(A_23,A_23) = k1_tarski(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_229,plain,(
    ! [A_68,B_69] : k1_enumset1(A_68,A_68,B_69) = k2_tarski(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_36,plain,(
    ! [E_22,A_16,C_18] : r2_hidden(E_22,k1_enumset1(A_16,E_22,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_247,plain,(
    ! [A_70,B_71] : r2_hidden(A_70,k2_tarski(A_70,B_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_36])).

tff(c_256,plain,(
    ! [A_23] : r2_hidden(A_23,k1_tarski(A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_247])).

tff(c_68,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_189,plain,(
    ! [A_61,B_62] :
      ( r1_xboole_0(k1_tarski(A_61),B_62)
      | r2_hidden(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = A_12
      | ~ r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_193,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(k1_tarski(A_61),B_62) = k1_tarski(A_61)
      | r2_hidden(A_61,B_62) ) ),
    inference(resolution,[status(thm)],[c_189,c_26])).

tff(c_24,plain,(
    ! [A_10,B_11] : r1_tarski(A_10,k2_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_30,plain,(
    ! [B_15,A_14] : k2_tarski(B_15,A_14) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_119,plain,(
    ! [A_52,B_53] : k3_tarski(k2_tarski(A_52,B_53)) = k2_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_314,plain,(
    ! [B_78,A_79] : k3_tarski(k2_tarski(B_78,A_79)) = k2_xboole_0(A_79,B_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_119])).

tff(c_66,plain,(
    ! [A_35,B_36] : k3_tarski(k2_tarski(A_35,B_36)) = k2_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_320,plain,(
    ! [B_78,A_79] : k2_xboole_0(B_78,A_79) = k2_xboole_0(A_79,B_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_66])).

tff(c_70,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_3'),'#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_342,plain,(
    r1_tarski(k2_xboole_0('#skF_4',k1_tarski('#skF_3')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_70])).

tff(c_14,plain,(
    ! [B_5,A_4] :
      ( B_5 = A_4
      | ~ r1_tarski(B_5,A_4)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_423,plain,
    ( k2_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_xboole_0('#skF_4',k1_tarski('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_342,c_14])).

tff(c_429,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_423])).

tff(c_18,plain,(
    ! [B_5] : r1_tarski(B_5,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_163,plain,(
    ! [A_58,B_59] :
      ( k3_xboole_0(A_58,B_59) = A_58
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_179,plain,(
    ! [B_5] : k3_xboole_0(B_5,B_5) = B_5 ),
    inference(resolution,[status(thm)],[c_18,c_163])).

tff(c_259,plain,(
    ! [A_73,B_74] : k5_xboole_0(A_73,k3_xboole_0(A_73,B_74)) = k4_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_277,plain,(
    ! [B_5] : k5_xboole_0(B_5,B_5) = k4_xboole_0(B_5,B_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_259])).

tff(c_178,plain,(
    ! [A_10,B_11] : k3_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = A_10 ),
    inference(resolution,[status(thm)],[c_24,c_163])).

tff(c_274,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = k5_xboole_0(A_10,A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_259])).

tff(c_517,plain,(
    ! [A_91,B_92] : k4_xboole_0(A_91,k2_xboole_0(A_91,B_92)) = k4_xboole_0(A_91,A_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_274])).

tff(c_553,plain,(
    ! [A_94,B_95] : k4_xboole_0(A_94,k2_xboole_0(B_95,A_94)) = k4_xboole_0(A_94,A_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_517])).

tff(c_570,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_553])).

tff(c_670,plain,(
    ! [A_108,C_109,B_110] :
      ( ~ r2_hidden(A_108,C_109)
      | ~ r2_hidden(A_108,B_110)
      | ~ r2_hidden(A_108,k5_xboole_0(B_110,C_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_793,plain,(
    ! [A_127,B_128] :
      ( ~ r2_hidden(A_127,B_128)
      | ~ r2_hidden(A_127,B_128)
      | ~ r2_hidden(A_127,k4_xboole_0(B_128,B_128)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_670])).

tff(c_1009,plain,(
    ! [A_157] :
      ( ~ r2_hidden(A_157,k1_tarski('#skF_3'))
      | ~ r2_hidden(A_157,k1_tarski('#skF_3'))
      | ~ r2_hidden(A_157,k4_xboole_0(k1_tarski('#skF_3'),'#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_793])).

tff(c_1020,plain,(
    ! [A_157] :
      ( ~ r2_hidden(A_157,k1_tarski('#skF_3'))
      | ~ r2_hidden(A_157,k1_tarski('#skF_3'))
      | ~ r2_hidden(A_157,k1_tarski('#skF_3'))
      | r2_hidden('#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_1009])).

tff(c_1026,plain,(
    ! [A_158] :
      ( ~ r2_hidden(A_158,k1_tarski('#skF_3'))
      | ~ r2_hidden(A_158,k1_tarski('#skF_3'))
      | ~ r2_hidden(A_158,k1_tarski('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1020])).

tff(c_1029,plain,(
    ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_256,c_1026])).

tff(c_1033,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_1029])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:11:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.99/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.46  
% 2.99/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.46  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.99/1.46  
% 2.99/1.46  %Foreground sorts:
% 2.99/1.46  
% 2.99/1.46  
% 2.99/1.46  %Background operators:
% 2.99/1.46  
% 2.99/1.46  
% 2.99/1.46  %Foreground operators:
% 2.99/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.99/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.99/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.99/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.99/1.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.99/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.99/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.99/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.99/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.99/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.99/1.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.99/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.99/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.46  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.99/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.99/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.99/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.99/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.99/1.46  
% 2.99/1.47  tff(f_69, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.99/1.47  tff(f_71, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.99/1.47  tff(f_67, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.99/1.47  tff(f_87, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.99/1.47  tff(f_80, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.99/1.47  tff(f_50, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.99/1.47  tff(f_46, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.99/1.47  tff(f_52, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.99/1.47  tff(f_82, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.99/1.47  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.99/1.47  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.99/1.47  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.99/1.47  tff(f_32, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.99/1.47  tff(c_56, plain, (![A_23]: (k2_tarski(A_23, A_23)=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.99/1.47  tff(c_229, plain, (![A_68, B_69]: (k1_enumset1(A_68, A_68, B_69)=k2_tarski(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.99/1.47  tff(c_36, plain, (![E_22, A_16, C_18]: (r2_hidden(E_22, k1_enumset1(A_16, E_22, C_18)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.99/1.47  tff(c_247, plain, (![A_70, B_71]: (r2_hidden(A_70, k2_tarski(A_70, B_71)))), inference(superposition, [status(thm), theory('equality')], [c_229, c_36])).
% 2.99/1.47  tff(c_256, plain, (![A_23]: (r2_hidden(A_23, k1_tarski(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_247])).
% 2.99/1.47  tff(c_68, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.99/1.47  tff(c_189, plain, (![A_61, B_62]: (r1_xboole_0(k1_tarski(A_61), B_62) | r2_hidden(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.99/1.47  tff(c_26, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=A_12 | ~r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.99/1.47  tff(c_193, plain, (![A_61, B_62]: (k4_xboole_0(k1_tarski(A_61), B_62)=k1_tarski(A_61) | r2_hidden(A_61, B_62))), inference(resolution, [status(thm)], [c_189, c_26])).
% 2.99/1.47  tff(c_24, plain, (![A_10, B_11]: (r1_tarski(A_10, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.99/1.47  tff(c_30, plain, (![B_15, A_14]: (k2_tarski(B_15, A_14)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.99/1.47  tff(c_119, plain, (![A_52, B_53]: (k3_tarski(k2_tarski(A_52, B_53))=k2_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.99/1.47  tff(c_314, plain, (![B_78, A_79]: (k3_tarski(k2_tarski(B_78, A_79))=k2_xboole_0(A_79, B_78))), inference(superposition, [status(thm), theory('equality')], [c_30, c_119])).
% 2.99/1.47  tff(c_66, plain, (![A_35, B_36]: (k3_tarski(k2_tarski(A_35, B_36))=k2_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.99/1.47  tff(c_320, plain, (![B_78, A_79]: (k2_xboole_0(B_78, A_79)=k2_xboole_0(A_79, B_78))), inference(superposition, [status(thm), theory('equality')], [c_314, c_66])).
% 2.99/1.47  tff(c_70, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_3'), '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.99/1.47  tff(c_342, plain, (r1_tarski(k2_xboole_0('#skF_4', k1_tarski('#skF_3')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_320, c_70])).
% 2.99/1.47  tff(c_14, plain, (![B_5, A_4]: (B_5=A_4 | ~r1_tarski(B_5, A_4) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.99/1.47  tff(c_423, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', k2_xboole_0('#skF_4', k1_tarski('#skF_3')))), inference(resolution, [status(thm)], [c_342, c_14])).
% 2.99/1.47  tff(c_429, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_423])).
% 2.99/1.47  tff(c_18, plain, (![B_5]: (r1_tarski(B_5, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.99/1.47  tff(c_163, plain, (![A_58, B_59]: (k3_xboole_0(A_58, B_59)=A_58 | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.99/1.47  tff(c_179, plain, (![B_5]: (k3_xboole_0(B_5, B_5)=B_5)), inference(resolution, [status(thm)], [c_18, c_163])).
% 2.99/1.47  tff(c_259, plain, (![A_73, B_74]: (k5_xboole_0(A_73, k3_xboole_0(A_73, B_74))=k4_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.99/1.47  tff(c_277, plain, (![B_5]: (k5_xboole_0(B_5, B_5)=k4_xboole_0(B_5, B_5))), inference(superposition, [status(thm), theory('equality')], [c_179, c_259])).
% 2.99/1.47  tff(c_178, plain, (![A_10, B_11]: (k3_xboole_0(A_10, k2_xboole_0(A_10, B_11))=A_10)), inference(resolution, [status(thm)], [c_24, c_163])).
% 2.99/1.47  tff(c_274, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k2_xboole_0(A_10, B_11))=k5_xboole_0(A_10, A_10))), inference(superposition, [status(thm), theory('equality')], [c_178, c_259])).
% 2.99/1.47  tff(c_517, plain, (![A_91, B_92]: (k4_xboole_0(A_91, k2_xboole_0(A_91, B_92))=k4_xboole_0(A_91, A_91))), inference(demodulation, [status(thm), theory('equality')], [c_277, c_274])).
% 2.99/1.47  tff(c_553, plain, (![A_94, B_95]: (k4_xboole_0(A_94, k2_xboole_0(B_95, A_94))=k4_xboole_0(A_94, A_94))), inference(superposition, [status(thm), theory('equality')], [c_320, c_517])).
% 2.99/1.47  tff(c_570, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_429, c_553])).
% 2.99/1.47  tff(c_670, plain, (![A_108, C_109, B_110]: (~r2_hidden(A_108, C_109) | ~r2_hidden(A_108, B_110) | ~r2_hidden(A_108, k5_xboole_0(B_110, C_109)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.99/1.47  tff(c_793, plain, (![A_127, B_128]: (~r2_hidden(A_127, B_128) | ~r2_hidden(A_127, B_128) | ~r2_hidden(A_127, k4_xboole_0(B_128, B_128)))), inference(superposition, [status(thm), theory('equality')], [c_277, c_670])).
% 2.99/1.47  tff(c_1009, plain, (![A_157]: (~r2_hidden(A_157, k1_tarski('#skF_3')) | ~r2_hidden(A_157, k1_tarski('#skF_3')) | ~r2_hidden(A_157, k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_570, c_793])).
% 2.99/1.47  tff(c_1020, plain, (![A_157]: (~r2_hidden(A_157, k1_tarski('#skF_3')) | ~r2_hidden(A_157, k1_tarski('#skF_3')) | ~r2_hidden(A_157, k1_tarski('#skF_3')) | r2_hidden('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_193, c_1009])).
% 2.99/1.47  tff(c_1026, plain, (![A_158]: (~r2_hidden(A_158, k1_tarski('#skF_3')) | ~r2_hidden(A_158, k1_tarski('#skF_3')) | ~r2_hidden(A_158, k1_tarski('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_68, c_1020])).
% 2.99/1.47  tff(c_1029, plain, (~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_256, c_1026])).
% 2.99/1.47  tff(c_1033, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_256, c_1029])).
% 2.99/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.47  
% 2.99/1.47  Inference rules
% 2.99/1.47  ----------------------
% 2.99/1.47  #Ref     : 0
% 2.99/1.47  #Sup     : 235
% 2.99/1.47  #Fact    : 0
% 2.99/1.47  #Define  : 0
% 2.99/1.47  #Split   : 1
% 2.99/1.47  #Chain   : 0
% 2.99/1.47  #Close   : 0
% 2.99/1.47  
% 2.99/1.47  Ordering : KBO
% 2.99/1.47  
% 2.99/1.47  Simplification rules
% 2.99/1.47  ----------------------
% 2.99/1.47  #Subsume      : 25
% 2.99/1.47  #Demod        : 104
% 2.99/1.47  #Tautology    : 155
% 2.99/1.47  #SimpNegUnit  : 1
% 2.99/1.47  #BackRed      : 4
% 2.99/1.47  
% 2.99/1.47  #Partial instantiations: 0
% 2.99/1.47  #Strategies tried      : 1
% 2.99/1.47  
% 2.99/1.47  Timing (in seconds)
% 2.99/1.47  ----------------------
% 2.99/1.48  Preprocessing        : 0.30
% 2.99/1.48  Parsing              : 0.15
% 2.99/1.48  CNF conversion       : 0.02
% 2.99/1.48  Main loop            : 0.37
% 2.99/1.48  Inferencing          : 0.13
% 2.99/1.48  Reduction            : 0.14
% 2.99/1.48  Demodulation         : 0.11
% 2.99/1.48  BG Simplification    : 0.02
% 2.99/1.48  Subsumption          : 0.07
% 2.99/1.48  Abstraction          : 0.02
% 2.99/1.48  MUC search           : 0.00
% 2.99/1.48  Cooper               : 0.00
% 2.99/1.48  Total                : 0.71
% 2.99/1.48  Index Insertion      : 0.00
% 2.99/1.48  Index Deletion       : 0.00
% 2.99/1.48  Index Matching       : 0.00
% 2.99/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
