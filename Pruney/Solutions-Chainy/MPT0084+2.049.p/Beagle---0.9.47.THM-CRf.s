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
% DateTime   : Thu Dec  3 09:44:10 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   57 (  69 expanded)
%              Number of leaves         :   25 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   58 (  82 expanded)
%              Number of equality atoms :   27 (  34 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_67,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_53,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_65,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(c_32,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_26,plain,(
    ! [A_24] : r1_xboole_0(A_24,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_12,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_271,plain,(
    ! [A_45,B_46,C_47] :
      ( ~ r1_xboole_0(A_45,B_46)
      | ~ r2_hidden(C_47,k3_xboole_0(A_45,B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_287,plain,(
    ! [A_10,C_47] :
      ( ~ r1_xboole_0(A_10,k1_xboole_0)
      | ~ r2_hidden(C_47,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_271])).

tff(c_290,plain,(
    ! [C_47] : ~ r2_hidden(C_47,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_287])).

tff(c_111,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k4_xboole_0(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_250,plain,(
    ! [A_43,B_44] : r1_tarski(k3_xboole_0(A_43,B_44),A_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_14])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = k1_xboole_0
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_266,plain,(
    ! [A_43,B_44] : k4_xboole_0(k3_xboole_0(A_43,B_44),A_43) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_250,c_10])).

tff(c_16,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_57,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_73,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_57])).

tff(c_132,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k3_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_111])).

tff(c_139,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_132])).

tff(c_1327,plain,(
    ! [A_82,B_83,C_84] : k4_xboole_0(k3_xboole_0(A_82,B_83),k3_xboole_0(A_82,C_84)) = k3_xboole_0(A_82,k4_xboole_0(B_83,C_84)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1437,plain,(
    ! [B_83] : k4_xboole_0(k3_xboole_0('#skF_3',B_83),'#skF_3') = k3_xboole_0('#skF_3',k4_xboole_0(B_83,'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_1327])).

tff(c_1473,plain,(
    ! [B_83] : k3_xboole_0('#skF_3',k4_xboole_0(B_83,'#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_1437])).

tff(c_18,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_28,plain,(
    r1_xboole_0('#skF_3',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_402,plain,(
    ! [A_55,B_56] :
      ( ~ r1_xboole_0(A_55,B_56)
      | k3_xboole_0(A_55,B_56) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_271])).

tff(c_409,plain,(
    k3_xboole_0('#skF_3',k3_xboole_0('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_402])).

tff(c_1419,plain,(
    ! [B_83] : k3_xboole_0('#skF_3',k4_xboole_0(B_83,k3_xboole_0('#skF_4','#skF_5'))) = k4_xboole_0(k3_xboole_0('#skF_3',B_83),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_1327])).

tff(c_1648,plain,(
    ! [B_88] : k3_xboole_0('#skF_3',k4_xboole_0(B_88,k3_xboole_0('#skF_4','#skF_5'))) = k3_xboole_0('#skF_3',B_88) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1419])).

tff(c_1699,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1648])).

tff(c_1727,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1473,c_1699])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),k3_xboole_0(A_1,B_2))
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1747,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4'),k1_xboole_0)
    | r1_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1727,c_2])).

tff(c_1770,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_290,c_1747])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:23:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.08/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.48  
% 3.08/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.48  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 3.08/1.48  
% 3.08/1.48  %Foreground sorts:
% 3.08/1.48  
% 3.08/1.48  
% 3.08/1.48  %Background operators:
% 3.08/1.48  
% 3.08/1.48  
% 3.08/1.48  %Foreground operators:
% 3.08/1.48  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.08/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.08/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.08/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.08/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.08/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.08/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.08/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.08/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.08/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.08/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.08/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.08/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.08/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.08/1.48  
% 3.08/1.50  tff(f_76, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 3.08/1.50  tff(f_67, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.08/1.50  tff(f_53, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.08/1.50  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.08/1.50  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.08/1.50  tff(f_55, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.08/1.50  tff(f_51, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.08/1.50  tff(f_57, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.08/1.50  tff(f_65, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_xboole_1)).
% 3.08/1.50  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 3.08/1.50  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.08/1.50  tff(c_32, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.08/1.50  tff(c_26, plain, (![A_24]: (r1_xboole_0(A_24, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.08/1.50  tff(c_12, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.08/1.50  tff(c_271, plain, (![A_45, B_46, C_47]: (~r1_xboole_0(A_45, B_46) | ~r2_hidden(C_47, k3_xboole_0(A_45, B_46)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.08/1.50  tff(c_287, plain, (![A_10, C_47]: (~r1_xboole_0(A_10, k1_xboole_0) | ~r2_hidden(C_47, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_271])).
% 3.08/1.50  tff(c_290, plain, (![C_47]: (~r2_hidden(C_47, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_287])).
% 3.08/1.50  tff(c_111, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k4_xboole_0(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.08/1.50  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.08/1.50  tff(c_250, plain, (![A_43, B_44]: (r1_tarski(k3_xboole_0(A_43, B_44), A_43))), inference(superposition, [status(thm), theory('equality')], [c_111, c_14])).
% 3.08/1.50  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=k1_xboole_0 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.08/1.50  tff(c_266, plain, (![A_43, B_44]: (k4_xboole_0(k3_xboole_0(A_43, B_44), A_43)=k1_xboole_0)), inference(resolution, [status(thm)], [c_250, c_10])).
% 3.08/1.50  tff(c_16, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.08/1.50  tff(c_30, plain, (r1_tarski('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.08/1.50  tff(c_57, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.08/1.50  tff(c_73, plain, (k4_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_57])).
% 3.08/1.50  tff(c_132, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_73, c_111])).
% 3.08/1.50  tff(c_139, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_132])).
% 3.08/1.50  tff(c_1327, plain, (![A_82, B_83, C_84]: (k4_xboole_0(k3_xboole_0(A_82, B_83), k3_xboole_0(A_82, C_84))=k3_xboole_0(A_82, k4_xboole_0(B_83, C_84)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.08/1.50  tff(c_1437, plain, (![B_83]: (k4_xboole_0(k3_xboole_0('#skF_3', B_83), '#skF_3')=k3_xboole_0('#skF_3', k4_xboole_0(B_83, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_139, c_1327])).
% 3.08/1.50  tff(c_1473, plain, (![B_83]: (k3_xboole_0('#skF_3', k4_xboole_0(B_83, '#skF_5'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_266, c_1437])).
% 3.08/1.50  tff(c_18, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.08/1.50  tff(c_28, plain, (r1_xboole_0('#skF_3', k3_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.08/1.50  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.08/1.50  tff(c_402, plain, (![A_55, B_56]: (~r1_xboole_0(A_55, B_56) | k3_xboole_0(A_55, B_56)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_271])).
% 3.08/1.50  tff(c_409, plain, (k3_xboole_0('#skF_3', k3_xboole_0('#skF_4', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_402])).
% 3.08/1.50  tff(c_1419, plain, (![B_83]: (k3_xboole_0('#skF_3', k4_xboole_0(B_83, k3_xboole_0('#skF_4', '#skF_5')))=k4_xboole_0(k3_xboole_0('#skF_3', B_83), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_409, c_1327])).
% 3.08/1.50  tff(c_1648, plain, (![B_88]: (k3_xboole_0('#skF_3', k4_xboole_0(B_88, k3_xboole_0('#skF_4', '#skF_5')))=k3_xboole_0('#skF_3', B_88))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1419])).
% 3.08/1.50  tff(c_1699, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18, c_1648])).
% 3.08/1.50  tff(c_1727, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1473, c_1699])).
% 3.08/1.50  tff(c_2, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), k3_xboole_0(A_1, B_2)) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.08/1.50  tff(c_1747, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), k1_xboole_0) | r1_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1727, c_2])).
% 3.08/1.50  tff(c_1770, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_290, c_1747])).
% 3.08/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.50  
% 3.08/1.50  Inference rules
% 3.08/1.50  ----------------------
% 3.08/1.50  #Ref     : 0
% 3.08/1.50  #Sup     : 439
% 3.08/1.50  #Fact    : 0
% 3.08/1.50  #Define  : 0
% 3.08/1.50  #Split   : 1
% 3.08/1.50  #Chain   : 0
% 3.08/1.50  #Close   : 0
% 3.08/1.50  
% 3.08/1.50  Ordering : KBO
% 3.08/1.50  
% 3.08/1.50  Simplification rules
% 3.08/1.50  ----------------------
% 3.08/1.50  #Subsume      : 9
% 3.08/1.50  #Demod        : 347
% 3.08/1.50  #Tautology    : 287
% 3.08/1.50  #SimpNegUnit  : 10
% 3.08/1.50  #BackRed      : 0
% 3.08/1.50  
% 3.08/1.50  #Partial instantiations: 0
% 3.08/1.50  #Strategies tried      : 1
% 3.08/1.50  
% 3.08/1.50  Timing (in seconds)
% 3.08/1.50  ----------------------
% 3.08/1.50  Preprocessing        : 0.29
% 3.08/1.50  Parsing              : 0.16
% 3.08/1.50  CNF conversion       : 0.02
% 3.08/1.50  Main loop            : 0.43
% 3.08/1.50  Inferencing          : 0.15
% 3.08/1.50  Reduction            : 0.17
% 3.08/1.50  Demodulation         : 0.14
% 3.08/1.50  BG Simplification    : 0.02
% 3.08/1.50  Subsumption          : 0.06
% 3.08/1.50  Abstraction          : 0.03
% 3.08/1.50  MUC search           : 0.00
% 3.08/1.50  Cooper               : 0.00
% 3.08/1.50  Total                : 0.75
% 3.08/1.50  Index Insertion      : 0.00
% 3.08/1.50  Index Deletion       : 0.00
% 3.08/1.50  Index Matching       : 0.00
% 3.08/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
