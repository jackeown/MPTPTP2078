%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:00 EST 2020

% Result     : Theorem 5.71s
% Output     : CNFRefutation 5.71s
% Verified   : 
% Statistics : Number of formulae       :   59 (  64 expanded)
%              Number of leaves         :   31 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   62 (  72 expanded)
%              Number of equality atoms :   30 (  34 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_86,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_84,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_88,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_94,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_90,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_56,axiom,(
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

tff(f_38,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_78,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_92,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_42,plain,(
    ! [A_25] : k2_xboole_0(A_25,k1_xboole_0) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_40,plain,(
    ! [A_23,B_24] : r1_tarski(k3_xboole_0(A_23,B_24),A_23) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_164,plain,(
    ! [A_41,B_42] :
      ( k4_xboole_0(A_41,B_42) = k1_xboole_0
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_168,plain,(
    ! [A_23,B_24] : k4_xboole_0(k3_xboole_0(A_23,B_24),A_23) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_164])).

tff(c_259,plain,(
    ! [A_53,B_54] : k2_xboole_0(A_53,k4_xboole_0(B_54,A_53)) = k2_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_284,plain,(
    ! [A_23,B_24] : k2_xboole_0(A_23,k3_xboole_0(A_23,B_24)) = k2_xboole_0(A_23,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_259])).

tff(c_297,plain,(
    ! [A_23,B_24] : k2_xboole_0(A_23,k3_xboole_0(A_23,B_24)) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_284])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_50,plain,(
    ! [A_31,B_32] : k4_xboole_0(A_31,k3_xboole_0(A_31,B_32)) = k4_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_46,plain,(
    ! [A_28] : k4_xboole_0(A_28,k1_xboole_0) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_28,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),A_9)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_26,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),B_10)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_485,plain,(
    ! [D_63,B_64,A_65] :
      ( ~ r2_hidden(D_63,B_64)
      | ~ r2_hidden(D_63,k4_xboole_0(A_65,B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6479,plain,(
    ! [A_248,A_249,B_250] :
      ( ~ r2_hidden('#skF_3'(A_248,k4_xboole_0(A_249,B_250)),B_250)
      | r1_xboole_0(A_248,k4_xboole_0(A_249,B_250)) ) ),
    inference(resolution,[status(thm)],[c_26,c_485])).

tff(c_6571,plain,(
    ! [A_251,A_252] : r1_xboole_0(A_251,k4_xboole_0(A_252,A_251)) ),
    inference(resolution,[status(thm)],[c_28,c_6479])).

tff(c_34,plain,(
    ! [A_19] :
      ( r2_hidden('#skF_5'(A_19),A_19)
      | k1_xboole_0 = A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_582,plain,(
    ! [A_75,B_76,C_77] :
      ( ~ r1_xboole_0(A_75,B_76)
      | ~ r2_hidden(C_77,k3_xboole_0(A_75,B_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_600,plain,(
    ! [A_75,B_76] :
      ( ~ r1_xboole_0(A_75,B_76)
      | k3_xboole_0(A_75,B_76) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_582])).

tff(c_6638,plain,(
    ! [A_253,A_254] : k3_xboole_0(A_253,k4_xboole_0(A_254,A_253)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6571,c_600])).

tff(c_6679,plain,(
    ! [A_253,A_254] : k4_xboole_0(A_253,k4_xboole_0(A_254,A_253)) = k4_xboole_0(A_253,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6638,c_50])).

tff(c_6759,plain,(
    ! [A_253,A_254] : k4_xboole_0(A_253,k4_xboole_0(A_254,A_253)) = A_253 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6679])).

tff(c_48,plain,(
    ! [A_29,B_30] : k4_xboole_0(k2_xboole_0(A_29,B_30),B_30) = k4_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_265,plain,(
    ! [A_53,B_54] : k4_xboole_0(k2_xboole_0(A_53,B_54),k4_xboole_0(B_54,A_53)) = k4_xboole_0(A_53,k4_xboole_0(B_54,A_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_48])).

tff(c_8086,plain,(
    ! [A_279,B_280] : k4_xboole_0(k2_xboole_0(A_279,B_280),k4_xboole_0(B_280,A_279)) = A_279 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6759,c_265])).

tff(c_8296,plain,(
    ! [A_31,B_32] : k4_xboole_0(k2_xboole_0(k3_xboole_0(A_31,B_32),A_31),k4_xboole_0(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_8086])).

tff(c_8371,plain,(
    ! [A_31,B_32] : k4_xboole_0(A_31,k4_xboole_0(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_2,c_8296])).

tff(c_52,plain,(
    k4_xboole_0('#skF_6',k4_xboole_0('#skF_6','#skF_7')) != k3_xboole_0('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_10074,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8371,c_52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n012.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 20:04:37 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.71/2.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.71/2.20  
% 5.71/2.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.71/2.20  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_4
% 5.71/2.20  
% 5.71/2.20  %Foreground sorts:
% 5.71/2.20  
% 5.71/2.20  
% 5.71/2.20  %Background operators:
% 5.71/2.20  
% 5.71/2.20  
% 5.71/2.20  %Foreground operators:
% 5.71/2.20  tff('#skF_5', type, '#skF_5': $i > $i).
% 5.71/2.20  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.71/2.20  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 5.71/2.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.71/2.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.71/2.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.71/2.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.71/2.20  tff('#skF_7', type, '#skF_7': $i).
% 5.71/2.20  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.71/2.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.71/2.20  tff('#skF_6', type, '#skF_6': $i).
% 5.71/2.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.71/2.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.71/2.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.71/2.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.71/2.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.71/2.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.71/2.20  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.71/2.20  
% 5.71/2.21  tff(f_86, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 5.71/2.21  tff(f_84, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.71/2.21  tff(f_82, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.71/2.21  tff(f_88, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.71/2.21  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.71/2.21  tff(f_94, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 5.71/2.21  tff(f_90, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.71/2.21  tff(f_56, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.71/2.21  tff(f_38, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.71/2.21  tff(f_78, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.71/2.21  tff(f_70, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.71/2.21  tff(f_92, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 5.71/2.21  tff(f_97, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.71/2.21  tff(c_42, plain, (![A_25]: (k2_xboole_0(A_25, k1_xboole_0)=A_25)), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.71/2.21  tff(c_40, plain, (![A_23, B_24]: (r1_tarski(k3_xboole_0(A_23, B_24), A_23))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.71/2.21  tff(c_164, plain, (![A_41, B_42]: (k4_xboole_0(A_41, B_42)=k1_xboole_0 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.71/2.21  tff(c_168, plain, (![A_23, B_24]: (k4_xboole_0(k3_xboole_0(A_23, B_24), A_23)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_164])).
% 5.71/2.21  tff(c_259, plain, (![A_53, B_54]: (k2_xboole_0(A_53, k4_xboole_0(B_54, A_53))=k2_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.71/2.21  tff(c_284, plain, (![A_23, B_24]: (k2_xboole_0(A_23, k3_xboole_0(A_23, B_24))=k2_xboole_0(A_23, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_168, c_259])).
% 5.71/2.21  tff(c_297, plain, (![A_23, B_24]: (k2_xboole_0(A_23, k3_xboole_0(A_23, B_24))=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_284])).
% 5.71/2.21  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.71/2.21  tff(c_50, plain, (![A_31, B_32]: (k4_xboole_0(A_31, k3_xboole_0(A_31, B_32))=k4_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.71/2.21  tff(c_46, plain, (![A_28]: (k4_xboole_0(A_28, k1_xboole_0)=A_28)), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.71/2.21  tff(c_28, plain, (![A_9, B_10]: (r2_hidden('#skF_3'(A_9, B_10), A_9) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.71/2.21  tff(c_26, plain, (![A_9, B_10]: (r2_hidden('#skF_3'(A_9, B_10), B_10) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.71/2.21  tff(c_485, plain, (![D_63, B_64, A_65]: (~r2_hidden(D_63, B_64) | ~r2_hidden(D_63, k4_xboole_0(A_65, B_64)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.71/2.21  tff(c_6479, plain, (![A_248, A_249, B_250]: (~r2_hidden('#skF_3'(A_248, k4_xboole_0(A_249, B_250)), B_250) | r1_xboole_0(A_248, k4_xboole_0(A_249, B_250)))), inference(resolution, [status(thm)], [c_26, c_485])).
% 5.71/2.21  tff(c_6571, plain, (![A_251, A_252]: (r1_xboole_0(A_251, k4_xboole_0(A_252, A_251)))), inference(resolution, [status(thm)], [c_28, c_6479])).
% 5.71/2.21  tff(c_34, plain, (![A_19]: (r2_hidden('#skF_5'(A_19), A_19) | k1_xboole_0=A_19)), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.71/2.21  tff(c_582, plain, (![A_75, B_76, C_77]: (~r1_xboole_0(A_75, B_76) | ~r2_hidden(C_77, k3_xboole_0(A_75, B_76)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.71/2.21  tff(c_600, plain, (![A_75, B_76]: (~r1_xboole_0(A_75, B_76) | k3_xboole_0(A_75, B_76)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_582])).
% 5.71/2.21  tff(c_6638, plain, (![A_253, A_254]: (k3_xboole_0(A_253, k4_xboole_0(A_254, A_253))=k1_xboole_0)), inference(resolution, [status(thm)], [c_6571, c_600])).
% 5.71/2.21  tff(c_6679, plain, (![A_253, A_254]: (k4_xboole_0(A_253, k4_xboole_0(A_254, A_253))=k4_xboole_0(A_253, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6638, c_50])).
% 5.71/2.21  tff(c_6759, plain, (![A_253, A_254]: (k4_xboole_0(A_253, k4_xboole_0(A_254, A_253))=A_253)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_6679])).
% 5.71/2.21  tff(c_48, plain, (![A_29, B_30]: (k4_xboole_0(k2_xboole_0(A_29, B_30), B_30)=k4_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.71/2.21  tff(c_265, plain, (![A_53, B_54]: (k4_xboole_0(k2_xboole_0(A_53, B_54), k4_xboole_0(B_54, A_53))=k4_xboole_0(A_53, k4_xboole_0(B_54, A_53)))), inference(superposition, [status(thm), theory('equality')], [c_259, c_48])).
% 5.71/2.21  tff(c_8086, plain, (![A_279, B_280]: (k4_xboole_0(k2_xboole_0(A_279, B_280), k4_xboole_0(B_280, A_279))=A_279)), inference(demodulation, [status(thm), theory('equality')], [c_6759, c_265])).
% 5.71/2.21  tff(c_8296, plain, (![A_31, B_32]: (k4_xboole_0(k2_xboole_0(k3_xboole_0(A_31, B_32), A_31), k4_xboole_0(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(superposition, [status(thm), theory('equality')], [c_50, c_8086])).
% 5.71/2.21  tff(c_8371, plain, (![A_31, B_32]: (k4_xboole_0(A_31, k4_xboole_0(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(demodulation, [status(thm), theory('equality')], [c_297, c_2, c_8296])).
% 5.71/2.21  tff(c_52, plain, (k4_xboole_0('#skF_6', k4_xboole_0('#skF_6', '#skF_7'))!=k3_xboole_0('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.71/2.21  tff(c_10074, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8371, c_52])).
% 5.71/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.71/2.21  
% 5.71/2.21  Inference rules
% 5.71/2.21  ----------------------
% 5.71/2.21  #Ref     : 0
% 5.71/2.21  #Sup     : 2528
% 5.71/2.21  #Fact    : 0
% 5.71/2.21  #Define  : 0
% 5.71/2.21  #Split   : 1
% 5.71/2.21  #Chain   : 0
% 5.71/2.21  #Close   : 0
% 5.71/2.21  
% 5.71/2.21  Ordering : KBO
% 5.71/2.21  
% 5.71/2.21  Simplification rules
% 5.71/2.21  ----------------------
% 5.71/2.21  #Subsume      : 300
% 5.71/2.21  #Demod        : 2389
% 5.71/2.21  #Tautology    : 1639
% 5.71/2.21  #SimpNegUnit  : 44
% 5.71/2.21  #BackRed      : 6
% 5.71/2.21  
% 5.71/2.21  #Partial instantiations: 0
% 5.71/2.21  #Strategies tried      : 1
% 5.71/2.21  
% 5.71/2.21  Timing (in seconds)
% 5.71/2.21  ----------------------
% 5.71/2.21  Preprocessing        : 0.30
% 5.71/2.21  Parsing              : 0.16
% 5.71/2.21  CNF conversion       : 0.02
% 5.71/2.21  Main loop            : 1.16
% 5.71/2.21  Inferencing          : 0.35
% 5.71/2.21  Reduction            : 0.51
% 5.71/2.21  Demodulation         : 0.42
% 5.71/2.21  BG Simplification    : 0.04
% 5.71/2.22  Subsumption          : 0.19
% 5.71/2.22  Abstraction          : 0.06
% 5.71/2.22  MUC search           : 0.00
% 5.71/2.22  Cooper               : 0.00
% 5.71/2.22  Total                : 1.49
% 5.71/2.22  Index Insertion      : 0.00
% 5.71/2.22  Index Deletion       : 0.00
% 5.71/2.22  Index Matching       : 0.00
% 5.71/2.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
