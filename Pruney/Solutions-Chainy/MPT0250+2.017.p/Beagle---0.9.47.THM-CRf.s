%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:34 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   62 (  72 expanded)
%              Number of leaves         :   34 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :   69 (  84 expanded)
%              Number of equality atoms :   23 (  32 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_84,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_86,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_61,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_97,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_78,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_74,plain,(
    ! [A_37,B_38] :
      ( r1_xboole_0(k1_tarski(A_37),B_38)
      | r2_hidden(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_66,plain,(
    ! [A_27] : k2_tarski(A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_183,plain,(
    ! [A_66,B_67] : k1_enumset1(A_66,A_66,B_67) = k2_tarski(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_46,plain,(
    ! [E_26,A_20,C_22] : r2_hidden(E_26,k1_enumset1(A_20,E_26,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_201,plain,(
    ! [A_68,B_69] : r2_hidden(A_68,k2_tarski(A_68,B_69)) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_46])).

tff(c_210,plain,(
    ! [A_27] : r2_hidden(A_27,k1_tarski(A_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_201])).

tff(c_34,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_40,plain,(
    ! [B_19,A_18] : k2_tarski(B_19,A_18) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_140,plain,(
    ! [A_62,B_63] : k3_tarski(k2_tarski(A_62,B_63)) = k2_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_237,plain,(
    ! [B_75,A_76] : k3_tarski(k2_tarski(B_75,A_76)) = k2_xboole_0(A_76,B_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_140])).

tff(c_76,plain,(
    ! [A_39,B_40] : k3_tarski(k2_tarski(A_39,B_40)) = k2_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_243,plain,(
    ! [B_75,A_76] : k2_xboole_0(B_75,A_76) = k2_xboole_0(A_76,B_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_76])).

tff(c_80,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_263,plain,(
    r1_tarski(k2_xboole_0('#skF_6',k1_tarski('#skF_5')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_80])).

tff(c_20,plain,(
    ! [B_8,A_7] :
      ( B_8 = A_7
      | ~ r1_tarski(B_8,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_334,plain,
    ( k2_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_xboole_0('#skF_6',k1_tarski('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_263,c_20])).

tff(c_337,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_334])).

tff(c_380,plain,(
    ! [A_89,C_90,B_91] :
      ( r1_xboole_0(A_89,C_90)
      | ~ r1_xboole_0(A_89,k2_xboole_0(B_91,C_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_403,plain,(
    ! [A_92] :
      ( r1_xboole_0(A_92,k1_tarski('#skF_5'))
      | ~ r1_xboole_0(A_92,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_380])).

tff(c_36,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = A_16
      | ~ r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_407,plain,(
    ! [A_92] :
      ( k4_xboole_0(A_92,k1_tarski('#skF_5')) = A_92
      | ~ r1_xboole_0(A_92,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_403,c_36])).

tff(c_420,plain,(
    ! [D_94,B_95,A_96] :
      ( ~ r2_hidden(D_94,B_95)
      | ~ r2_hidden(D_94,k4_xboole_0(A_96,B_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_755,plain,(
    ! [D_145,A_146] :
      ( ~ r2_hidden(D_145,k1_tarski('#skF_5'))
      | ~ r2_hidden(D_145,A_146)
      | ~ r1_xboole_0(A_146,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_420])).

tff(c_760,plain,(
    ! [A_147] :
      ( ~ r2_hidden('#skF_5',A_147)
      | ~ r1_xboole_0(A_147,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_210,c_755])).

tff(c_806,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_210,c_760])).

tff(c_816,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_806])).

tff(c_821,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_816])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:26:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.38  
% 2.87/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.38  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.87/1.38  
% 2.87/1.38  %Foreground sorts:
% 2.87/1.38  
% 2.87/1.38  
% 2.87/1.38  %Background operators:
% 2.87/1.38  
% 2.87/1.38  
% 2.87/1.38  %Foreground operators:
% 2.87/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.87/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.87/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.87/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.87/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.87/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.87/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.87/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.87/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.87/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.87/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.87/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.87/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.87/1.38  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.87/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.87/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.87/1.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.87/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.87/1.38  
% 2.87/1.40  tff(f_102, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.87/1.40  tff(f_95, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.87/1.40  tff(f_84, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.87/1.40  tff(f_86, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.87/1.40  tff(f_82, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.87/1.40  tff(f_61, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.87/1.40  tff(f_67, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.87/1.40  tff(f_97, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.87/1.40  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.87/1.40  tff(f_59, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 2.87/1.40  tff(f_65, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.87/1.40  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.87/1.40  tff(c_78, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.87/1.40  tff(c_74, plain, (![A_37, B_38]: (r1_xboole_0(k1_tarski(A_37), B_38) | r2_hidden(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.87/1.40  tff(c_66, plain, (![A_27]: (k2_tarski(A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.87/1.40  tff(c_183, plain, (![A_66, B_67]: (k1_enumset1(A_66, A_66, B_67)=k2_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.87/1.40  tff(c_46, plain, (![E_26, A_20, C_22]: (r2_hidden(E_26, k1_enumset1(A_20, E_26, C_22)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.87/1.40  tff(c_201, plain, (![A_68, B_69]: (r2_hidden(A_68, k2_tarski(A_68, B_69)))), inference(superposition, [status(thm), theory('equality')], [c_183, c_46])).
% 2.87/1.40  tff(c_210, plain, (![A_27]: (r2_hidden(A_27, k1_tarski(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_201])).
% 2.87/1.40  tff(c_34, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.87/1.40  tff(c_40, plain, (![B_19, A_18]: (k2_tarski(B_19, A_18)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.87/1.40  tff(c_140, plain, (![A_62, B_63]: (k3_tarski(k2_tarski(A_62, B_63))=k2_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.87/1.40  tff(c_237, plain, (![B_75, A_76]: (k3_tarski(k2_tarski(B_75, A_76))=k2_xboole_0(A_76, B_75))), inference(superposition, [status(thm), theory('equality')], [c_40, c_140])).
% 2.87/1.40  tff(c_76, plain, (![A_39, B_40]: (k3_tarski(k2_tarski(A_39, B_40))=k2_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.87/1.40  tff(c_243, plain, (![B_75, A_76]: (k2_xboole_0(B_75, A_76)=k2_xboole_0(A_76, B_75))), inference(superposition, [status(thm), theory('equality')], [c_237, c_76])).
% 2.87/1.40  tff(c_80, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.87/1.40  tff(c_263, plain, (r1_tarski(k2_xboole_0('#skF_6', k1_tarski('#skF_5')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_243, c_80])).
% 2.87/1.40  tff(c_20, plain, (![B_8, A_7]: (B_8=A_7 | ~r1_tarski(B_8, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.87/1.40  tff(c_334, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6' | ~r1_tarski('#skF_6', k2_xboole_0('#skF_6', k1_tarski('#skF_5')))), inference(resolution, [status(thm)], [c_263, c_20])).
% 2.87/1.40  tff(c_337, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_334])).
% 2.87/1.40  tff(c_380, plain, (![A_89, C_90, B_91]: (r1_xboole_0(A_89, C_90) | ~r1_xboole_0(A_89, k2_xboole_0(B_91, C_90)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.87/1.40  tff(c_403, plain, (![A_92]: (r1_xboole_0(A_92, k1_tarski('#skF_5')) | ~r1_xboole_0(A_92, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_337, c_380])).
% 2.87/1.40  tff(c_36, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=A_16 | ~r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.87/1.40  tff(c_407, plain, (![A_92]: (k4_xboole_0(A_92, k1_tarski('#skF_5'))=A_92 | ~r1_xboole_0(A_92, '#skF_6'))), inference(resolution, [status(thm)], [c_403, c_36])).
% 2.87/1.40  tff(c_420, plain, (![D_94, B_95, A_96]: (~r2_hidden(D_94, B_95) | ~r2_hidden(D_94, k4_xboole_0(A_96, B_95)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.87/1.40  tff(c_755, plain, (![D_145, A_146]: (~r2_hidden(D_145, k1_tarski('#skF_5')) | ~r2_hidden(D_145, A_146) | ~r1_xboole_0(A_146, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_407, c_420])).
% 2.87/1.40  tff(c_760, plain, (![A_147]: (~r2_hidden('#skF_5', A_147) | ~r1_xboole_0(A_147, '#skF_6'))), inference(resolution, [status(thm)], [c_210, c_755])).
% 2.87/1.40  tff(c_806, plain, (~r1_xboole_0(k1_tarski('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_210, c_760])).
% 2.87/1.40  tff(c_816, plain, (r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_74, c_806])).
% 2.87/1.40  tff(c_821, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_816])).
% 2.87/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.40  
% 2.87/1.40  Inference rules
% 2.87/1.40  ----------------------
% 2.87/1.40  #Ref     : 0
% 2.87/1.40  #Sup     : 182
% 2.87/1.40  #Fact    : 0
% 2.87/1.40  #Define  : 0
% 2.87/1.40  #Split   : 1
% 2.87/1.40  #Chain   : 0
% 2.87/1.40  #Close   : 0
% 2.87/1.40  
% 2.87/1.40  Ordering : KBO
% 2.87/1.40  
% 2.87/1.40  Simplification rules
% 2.87/1.40  ----------------------
% 2.87/1.40  #Subsume      : 40
% 2.87/1.40  #Demod        : 29
% 2.87/1.40  #Tautology    : 91
% 2.87/1.40  #SimpNegUnit  : 1
% 2.87/1.40  #BackRed      : 2
% 2.87/1.40  
% 2.87/1.40  #Partial instantiations: 0
% 2.87/1.40  #Strategies tried      : 1
% 2.87/1.40  
% 2.87/1.40  Timing (in seconds)
% 2.87/1.40  ----------------------
% 2.87/1.40  Preprocessing        : 0.32
% 2.87/1.40  Parsing              : 0.16
% 2.87/1.40  CNF conversion       : 0.02
% 2.87/1.40  Main loop            : 0.32
% 2.87/1.40  Inferencing          : 0.11
% 2.87/1.40  Reduction            : 0.11
% 2.87/1.40  Demodulation         : 0.08
% 2.87/1.40  BG Simplification    : 0.02
% 2.87/1.40  Subsumption          : 0.06
% 2.87/1.40  Abstraction          : 0.02
% 2.87/1.40  MUC search           : 0.00
% 2.87/1.40  Cooper               : 0.00
% 2.87/1.40  Total                : 0.67
% 2.87/1.40  Index Insertion      : 0.00
% 2.87/1.40  Index Deletion       : 0.00
% 2.87/1.40  Index Matching       : 0.00
% 2.87/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
