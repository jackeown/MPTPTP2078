%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:58 EST 2020

% Result     : Theorem 6.29s
% Output     : CNFRefutation 6.29s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 112 expanded)
%              Number of leaves         :   32 (  51 expanded)
%              Depth                    :   14
%              Number of atoms          :   81 ( 134 expanded)
%              Number of equality atoms :   45 (  77 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_45,axiom,(
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

tff(f_61,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_48,plain,(
    r2_hidden('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [A_19] : r1_tarski(k1_xboole_0,A_19) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_383,plain,(
    ! [A_53,B_54] :
      ( k4_xboole_0(A_53,B_54) = k1_xboole_0
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_418,plain,(
    ! [A_19] : k4_xboole_0(k1_xboole_0,A_19) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_383])).

tff(c_734,plain,(
    ! [B_73,A_74] :
      ( ~ r2_hidden(B_73,A_74)
      | k4_xboole_0(A_74,k1_tarski(B_73)) != A_74 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_755,plain,(
    ! [B_75] : ~ r2_hidden(B_75,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_734])).

tff(c_761,plain,(
    ! [A_76] : r1_xboole_0(A_76,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_755])).

tff(c_24,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(A_20,B_21) = A_20
      | ~ r1_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_765,plain,(
    ! [A_76] : k4_xboole_0(A_76,k1_xboole_0) = A_76 ),
    inference(resolution,[status(thm)],[c_761,c_24])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_154,plain,(
    ! [A_47,B_48] :
      ( k3_xboole_0(A_47,B_48) = A_47
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_214,plain,(
    ! [A_49] : k3_xboole_0(k1_xboole_0,A_49) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_154])).

tff(c_238,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_214])).

tff(c_669,plain,(
    ! [A_71,B_72] : k5_xboole_0(A_71,k3_xboole_0(A_71,B_72)) = k4_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_696,plain,(
    ! [A_1] : k5_xboole_0(A_1,k1_xboole_0) = k4_xboole_0(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_669])).

tff(c_822,plain,(
    ! [A_1] : k5_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_765,c_696])).

tff(c_50,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_74,plain,(
    ! [B_41,A_42] : k3_xboole_0(B_41,A_42) = k3_xboole_0(A_42,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_15,B_16] : r1_tarski(k3_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_125,plain,(
    ! [B_43,A_44] : r1_tarski(k3_xboole_0(B_43,A_44),A_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_18])).

tff(c_134,plain,(
    r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_125])).

tff(c_180,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),'#skF_4') = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_134,c_154])).

tff(c_46,plain,(
    k3_xboole_0('#skF_2','#skF_4') != k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_54,plain,(
    k3_xboole_0('#skF_4','#skF_2') != k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_46])).

tff(c_116,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_74])).

tff(c_52,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_186,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_52,c_154])).

tff(c_193,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_2])).

tff(c_4632,plain,(
    ! [A_153,B_154,C_155] : k3_xboole_0(k3_xboole_0(A_153,B_154),C_155) = k3_xboole_0(A_153,k3_xboole_0(B_154,C_155)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5166,plain,(
    ! [A_169,B_170,C_171] : r1_tarski(k3_xboole_0(A_169,k3_xboole_0(B_170,C_171)),k3_xboole_0(A_169,B_170)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4632,c_18])).

tff(c_5881,plain,(
    ! [A_182] : r1_tarski(k3_xboole_0(A_182,'#skF_2'),k3_xboole_0(A_182,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_5166])).

tff(c_5942,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_2'),k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_5881])).

tff(c_36,plain,(
    ! [B_33,A_32] :
      ( k1_tarski(B_33) = A_32
      | k1_xboole_0 = A_32
      | ~ r1_tarski(A_32,k1_tarski(B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_5984,plain,
    ( k3_xboole_0('#skF_4','#skF_2') = k1_tarski('#skF_5')
    | k3_xboole_0('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5942,c_36])).

tff(c_5993,plain,(
    k3_xboole_0('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_5984])).

tff(c_4679,plain,(
    ! [C_155,A_153,B_154] : k3_xboole_0(C_155,k3_xboole_0(A_153,B_154)) = k3_xboole_0(A_153,k3_xboole_0(B_154,C_155)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4632,c_2])).

tff(c_6432,plain,(
    ! [A_153] : k3_xboole_0('#skF_2',k3_xboole_0(A_153,'#skF_4')) = k3_xboole_0(A_153,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5993,c_4679])).

tff(c_7070,plain,(
    ! [A_188] : k3_xboole_0('#skF_2',k3_xboole_0(A_188,'#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_6432])).

tff(c_7174,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_7070])).

tff(c_14,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_7492,plain,(
    k4_xboole_0('#skF_2',k1_tarski('#skF_5')) = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_7174,c_14])).

tff(c_7531,plain,(
    k4_xboole_0('#skF_2',k1_tarski('#skF_5')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_822,c_7492])).

tff(c_42,plain,(
    ! [B_35,A_34] :
      ( ~ r2_hidden(B_35,A_34)
      | k4_xboole_0(A_34,k1_tarski(B_35)) != A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_7545,plain,(
    ~ r2_hidden('#skF_5','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7531,c_42])).

tff(c_7558,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_7545])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:26:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.29/2.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.29/2.23  
% 6.29/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.29/2.23  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.29/2.23  
% 6.29/2.23  %Foreground sorts:
% 6.29/2.23  
% 6.29/2.23  
% 6.29/2.23  %Background operators:
% 6.29/2.23  
% 6.29/2.23  
% 6.29/2.23  %Foreground operators:
% 6.29/2.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.29/2.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.29/2.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.29/2.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.29/2.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.29/2.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.29/2.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.29/2.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.29/2.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.29/2.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.29/2.23  tff('#skF_5', type, '#skF_5': $i).
% 6.29/2.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.29/2.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.29/2.23  tff('#skF_2', type, '#skF_2': $i).
% 6.29/2.23  tff('#skF_3', type, '#skF_3': $i).
% 6.29/2.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.29/2.23  tff('#skF_4', type, '#skF_4': $i).
% 6.29/2.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.29/2.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.29/2.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.29/2.23  
% 6.29/2.25  tff(f_93, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 6.29/2.25  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.29/2.25  tff(f_61, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.29/2.25  tff(f_49, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.29/2.25  tff(f_84, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 6.29/2.25  tff(f_65, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 6.29/2.25  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.29/2.25  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.29/2.25  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.29/2.25  tff(f_55, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 6.29/2.25  tff(f_53, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 6.29/2.25  tff(f_79, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 6.29/2.25  tff(c_48, plain, (r2_hidden('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.29/2.25  tff(c_6, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.29/2.25  tff(c_22, plain, (![A_19]: (r1_tarski(k1_xboole_0, A_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.29/2.25  tff(c_383, plain, (![A_53, B_54]: (k4_xboole_0(A_53, B_54)=k1_xboole_0 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.29/2.25  tff(c_418, plain, (![A_19]: (k4_xboole_0(k1_xboole_0, A_19)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_383])).
% 6.29/2.25  tff(c_734, plain, (![B_73, A_74]: (~r2_hidden(B_73, A_74) | k4_xboole_0(A_74, k1_tarski(B_73))!=A_74)), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.29/2.25  tff(c_755, plain, (![B_75]: (~r2_hidden(B_75, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_418, c_734])).
% 6.29/2.25  tff(c_761, plain, (![A_76]: (r1_xboole_0(A_76, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_755])).
% 6.29/2.25  tff(c_24, plain, (![A_20, B_21]: (k4_xboole_0(A_20, B_21)=A_20 | ~r1_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.29/2.25  tff(c_765, plain, (![A_76]: (k4_xboole_0(A_76, k1_xboole_0)=A_76)), inference(resolution, [status(thm)], [c_761, c_24])).
% 6.29/2.25  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.29/2.25  tff(c_154, plain, (![A_47, B_48]: (k3_xboole_0(A_47, B_48)=A_47 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.29/2.25  tff(c_214, plain, (![A_49]: (k3_xboole_0(k1_xboole_0, A_49)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_154])).
% 6.29/2.25  tff(c_238, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_214])).
% 6.29/2.25  tff(c_669, plain, (![A_71, B_72]: (k5_xboole_0(A_71, k3_xboole_0(A_71, B_72))=k4_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.29/2.25  tff(c_696, plain, (![A_1]: (k5_xboole_0(A_1, k1_xboole_0)=k4_xboole_0(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_238, c_669])).
% 6.29/2.25  tff(c_822, plain, (![A_1]: (k5_xboole_0(A_1, k1_xboole_0)=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_765, c_696])).
% 6.29/2.25  tff(c_50, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.29/2.25  tff(c_74, plain, (![B_41, A_42]: (k3_xboole_0(B_41, A_42)=k3_xboole_0(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.29/2.25  tff(c_18, plain, (![A_15, B_16]: (r1_tarski(k3_xboole_0(A_15, B_16), A_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.29/2.25  tff(c_125, plain, (![B_43, A_44]: (r1_tarski(k3_xboole_0(B_43, A_44), A_44))), inference(superposition, [status(thm), theory('equality')], [c_74, c_18])).
% 6.29/2.25  tff(c_134, plain, (r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_50, c_125])).
% 6.29/2.25  tff(c_180, plain, (k3_xboole_0(k1_tarski('#skF_5'), '#skF_4')=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_134, c_154])).
% 6.29/2.25  tff(c_46, plain, (k3_xboole_0('#skF_2', '#skF_4')!=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.29/2.25  tff(c_54, plain, (k3_xboole_0('#skF_4', '#skF_2')!=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_46])).
% 6.29/2.25  tff(c_116, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_50, c_74])).
% 6.29/2.25  tff(c_52, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.29/2.25  tff(c_186, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_52, c_154])).
% 6.29/2.25  tff(c_193, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_186, c_2])).
% 6.29/2.25  tff(c_4632, plain, (![A_153, B_154, C_155]: (k3_xboole_0(k3_xboole_0(A_153, B_154), C_155)=k3_xboole_0(A_153, k3_xboole_0(B_154, C_155)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.29/2.25  tff(c_5166, plain, (![A_169, B_170, C_171]: (r1_tarski(k3_xboole_0(A_169, k3_xboole_0(B_170, C_171)), k3_xboole_0(A_169, B_170)))), inference(superposition, [status(thm), theory('equality')], [c_4632, c_18])).
% 6.29/2.25  tff(c_5881, plain, (![A_182]: (r1_tarski(k3_xboole_0(A_182, '#skF_2'), k3_xboole_0(A_182, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_193, c_5166])).
% 6.29/2.25  tff(c_5942, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_2'), k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_5881])).
% 6.29/2.25  tff(c_36, plain, (![B_33, A_32]: (k1_tarski(B_33)=A_32 | k1_xboole_0=A_32 | ~r1_tarski(A_32, k1_tarski(B_33)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.29/2.25  tff(c_5984, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_tarski('#skF_5') | k3_xboole_0('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_5942, c_36])).
% 6.29/2.25  tff(c_5993, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_54, c_5984])).
% 6.29/2.25  tff(c_4679, plain, (![C_155, A_153, B_154]: (k3_xboole_0(C_155, k3_xboole_0(A_153, B_154))=k3_xboole_0(A_153, k3_xboole_0(B_154, C_155)))), inference(superposition, [status(thm), theory('equality')], [c_4632, c_2])).
% 6.29/2.25  tff(c_6432, plain, (![A_153]: (k3_xboole_0('#skF_2', k3_xboole_0(A_153, '#skF_4'))=k3_xboole_0(A_153, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_5993, c_4679])).
% 6.29/2.25  tff(c_7070, plain, (![A_188]: (k3_xboole_0('#skF_2', k3_xboole_0(A_188, '#skF_4'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_238, c_6432])).
% 6.29/2.25  tff(c_7174, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_5'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_180, c_7070])).
% 6.29/2.25  tff(c_14, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.29/2.25  tff(c_7492, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_5'))=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7174, c_14])).
% 6.29/2.25  tff(c_7531, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_5'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_822, c_7492])).
% 6.29/2.25  tff(c_42, plain, (![B_35, A_34]: (~r2_hidden(B_35, A_34) | k4_xboole_0(A_34, k1_tarski(B_35))!=A_34)), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.29/2.25  tff(c_7545, plain, (~r2_hidden('#skF_5', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7531, c_42])).
% 6.29/2.25  tff(c_7558, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_7545])).
% 6.29/2.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.29/2.25  
% 6.29/2.25  Inference rules
% 6.29/2.25  ----------------------
% 6.29/2.25  #Ref     : 0
% 6.29/2.25  #Sup     : 1911
% 6.29/2.25  #Fact    : 0
% 6.29/2.25  #Define  : 0
% 6.29/2.25  #Split   : 4
% 6.29/2.25  #Chain   : 0
% 6.29/2.25  #Close   : 0
% 6.29/2.25  
% 6.29/2.25  Ordering : KBO
% 6.29/2.25  
% 6.29/2.25  Simplification rules
% 6.29/2.25  ----------------------
% 6.29/2.25  #Subsume      : 19
% 6.29/2.25  #Demod        : 1788
% 6.29/2.25  #Tautology    : 1081
% 6.29/2.25  #SimpNegUnit  : 10
% 6.29/2.25  #BackRed      : 11
% 6.29/2.25  
% 6.29/2.25  #Partial instantiations: 0
% 6.29/2.25  #Strategies tried      : 1
% 6.29/2.25  
% 6.29/2.25  Timing (in seconds)
% 6.29/2.25  ----------------------
% 6.29/2.25  Preprocessing        : 0.31
% 6.29/2.25  Parsing              : 0.17
% 6.29/2.25  CNF conversion       : 0.02
% 6.29/2.25  Main loop            : 1.18
% 6.29/2.25  Inferencing          : 0.30
% 6.29/2.25  Reduction            : 0.60
% 6.29/2.25  Demodulation         : 0.51
% 6.29/2.25  BG Simplification    : 0.04
% 6.29/2.25  Subsumption          : 0.17
% 6.29/2.25  Abstraction          : 0.04
% 6.29/2.25  MUC search           : 0.00
% 6.29/2.25  Cooper               : 0.00
% 6.29/2.25  Total                : 1.53
% 6.29/2.25  Index Insertion      : 0.00
% 6.29/2.25  Index Deletion       : 0.00
% 6.29/2.25  Index Matching       : 0.00
% 6.29/2.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
