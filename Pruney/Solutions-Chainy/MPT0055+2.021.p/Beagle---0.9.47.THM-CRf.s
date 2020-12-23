%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:00 EST 2020

% Result     : Theorem 4.81s
% Output     : CNFRefutation 5.00s
% Verified   : 
% Statistics : Number of formulae       :   54 (  59 expanded)
%              Number of leaves         :   28 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :   54 (  64 expanded)
%              Number of equality atoms :   29 (  33 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_68,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_66,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_76,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_72,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_60,axiom,(
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

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_40,plain,(
    ! [A_20] : k2_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_38,plain,(
    ! [A_18,B_19] : r1_tarski(k3_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_121,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_125,plain,(
    ! [A_18,B_19] : k4_xboole_0(k3_xboole_0(A_18,B_19),A_18) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_121])).

tff(c_330,plain,(
    ! [A_57,B_58] : k2_xboole_0(A_57,k4_xboole_0(B_58,A_57)) = k2_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_358,plain,(
    ! [A_18,B_19] : k2_xboole_0(A_18,k3_xboole_0(A_18,B_19)) = k2_xboole_0(A_18,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_330])).

tff(c_373,plain,(
    ! [A_18,B_19] : k2_xboole_0(A_18,k3_xboole_0(A_18,B_19)) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_358])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_48,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k3_xboole_0(A_26,B_27)) = k4_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_44,plain,(
    ! [A_23] : k4_xboole_0(A_23,k1_xboole_0) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_32,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_3'(A_11,B_12),A_11)
      | r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_30,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_3'(A_11,B_12),B_12)
      | r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_456,plain,(
    ! [D_66,B_67,A_68] :
      ( ~ r2_hidden(D_66,B_67)
      | ~ r2_hidden(D_66,k4_xboole_0(A_68,B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4081,plain,(
    ! [A_167,A_168,B_169] :
      ( ~ r2_hidden('#skF_3'(A_167,k4_xboole_0(A_168,B_169)),B_169)
      | r1_xboole_0(A_167,k4_xboole_0(A_168,B_169)) ) ),
    inference(resolution,[status(thm)],[c_30,c_456])).

tff(c_4148,plain,(
    ! [A_170,A_171] : r1_xboole_0(A_170,k4_xboole_0(A_171,A_170)) ),
    inference(resolution,[status(thm)],[c_32,c_4081])).

tff(c_24,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = k1_xboole_0
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4211,plain,(
    ! [A_172,A_173] : k3_xboole_0(A_172,k4_xboole_0(A_173,A_172)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4148,c_24])).

tff(c_4228,plain,(
    ! [A_172,A_173] : k4_xboole_0(A_172,k4_xboole_0(A_173,A_172)) = k4_xboole_0(A_172,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4211,c_48])).

tff(c_4288,plain,(
    ! [A_172,A_173] : k4_xboole_0(A_172,k4_xboole_0(A_173,A_172)) = A_172 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_4228])).

tff(c_46,plain,(
    ! [A_24,B_25] : k4_xboole_0(k2_xboole_0(A_24,B_25),B_25) = k4_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_336,plain,(
    ! [A_57,B_58] : k4_xboole_0(k2_xboole_0(A_57,B_58),k4_xboole_0(B_58,A_57)) = k4_xboole_0(A_57,k4_xboole_0(B_58,A_57)) ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_46])).

tff(c_4763,plain,(
    ! [A_182,B_183] : k4_xboole_0(k2_xboole_0(A_182,B_183),k4_xboole_0(B_183,A_182)) = A_182 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4288,c_336])).

tff(c_4928,plain,(
    ! [A_26,B_27] : k4_xboole_0(k2_xboole_0(k3_xboole_0(A_26,B_27),A_26),k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_4763])).

tff(c_4987,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_2,c_4928])).

tff(c_50,plain,(
    k4_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_5')) != k3_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_5902,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4987,c_50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:23:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.81/1.98  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.81/1.98  
% 4.81/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.81/1.98  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 4.81/1.98  
% 4.81/1.98  %Foreground sorts:
% 4.81/1.98  
% 4.81/1.98  
% 4.81/1.98  %Background operators:
% 4.81/1.98  
% 4.81/1.98  
% 4.81/1.98  %Foreground operators:
% 4.81/1.98  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.81/1.98  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 4.81/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.81/1.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.81/1.98  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.81/1.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.81/1.98  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.81/1.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.81/1.98  tff('#skF_5', type, '#skF_5': $i).
% 4.81/1.98  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.81/1.98  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.81/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.81/1.98  tff('#skF_4', type, '#skF_4': $i).
% 4.81/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.81/1.98  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.81/1.98  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.81/1.98  
% 5.00/2.00  tff(f_68, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 5.00/2.00  tff(f_66, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.00/2.00  tff(f_64, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.00/2.00  tff(f_70, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.00/2.00  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.00/2.00  tff(f_76, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 5.00/2.00  tff(f_72, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.00/2.00  tff(f_60, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.00/2.00  tff(f_38, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.00/2.00  tff(f_42, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.00/2.00  tff(f_74, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 5.00/2.00  tff(f_79, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.00/2.00  tff(c_40, plain, (![A_20]: (k2_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.00/2.00  tff(c_38, plain, (![A_18, B_19]: (r1_tarski(k3_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.00/2.00  tff(c_121, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.00/2.00  tff(c_125, plain, (![A_18, B_19]: (k4_xboole_0(k3_xboole_0(A_18, B_19), A_18)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_121])).
% 5.00/2.00  tff(c_330, plain, (![A_57, B_58]: (k2_xboole_0(A_57, k4_xboole_0(B_58, A_57))=k2_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.00/2.00  tff(c_358, plain, (![A_18, B_19]: (k2_xboole_0(A_18, k3_xboole_0(A_18, B_19))=k2_xboole_0(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_125, c_330])).
% 5.00/2.00  tff(c_373, plain, (![A_18, B_19]: (k2_xboole_0(A_18, k3_xboole_0(A_18, B_19))=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_358])).
% 5.00/2.00  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.00/2.00  tff(c_48, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k3_xboole_0(A_26, B_27))=k4_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.00/2.00  tff(c_44, plain, (![A_23]: (k4_xboole_0(A_23, k1_xboole_0)=A_23)), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.00/2.00  tff(c_32, plain, (![A_11, B_12]: (r2_hidden('#skF_3'(A_11, B_12), A_11) | r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.00/2.00  tff(c_30, plain, (![A_11, B_12]: (r2_hidden('#skF_3'(A_11, B_12), B_12) | r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.00/2.00  tff(c_456, plain, (![D_66, B_67, A_68]: (~r2_hidden(D_66, B_67) | ~r2_hidden(D_66, k4_xboole_0(A_68, B_67)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.00/2.00  tff(c_4081, plain, (![A_167, A_168, B_169]: (~r2_hidden('#skF_3'(A_167, k4_xboole_0(A_168, B_169)), B_169) | r1_xboole_0(A_167, k4_xboole_0(A_168, B_169)))), inference(resolution, [status(thm)], [c_30, c_456])).
% 5.00/2.00  tff(c_4148, plain, (![A_170, A_171]: (r1_xboole_0(A_170, k4_xboole_0(A_171, A_170)))), inference(resolution, [status(thm)], [c_32, c_4081])).
% 5.00/2.00  tff(c_24, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=k1_xboole_0 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.00/2.00  tff(c_4211, plain, (![A_172, A_173]: (k3_xboole_0(A_172, k4_xboole_0(A_173, A_172))=k1_xboole_0)), inference(resolution, [status(thm)], [c_4148, c_24])).
% 5.00/2.00  tff(c_4228, plain, (![A_172, A_173]: (k4_xboole_0(A_172, k4_xboole_0(A_173, A_172))=k4_xboole_0(A_172, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4211, c_48])).
% 5.00/2.00  tff(c_4288, plain, (![A_172, A_173]: (k4_xboole_0(A_172, k4_xboole_0(A_173, A_172))=A_172)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_4228])).
% 5.00/2.00  tff(c_46, plain, (![A_24, B_25]: (k4_xboole_0(k2_xboole_0(A_24, B_25), B_25)=k4_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.00/2.00  tff(c_336, plain, (![A_57, B_58]: (k4_xboole_0(k2_xboole_0(A_57, B_58), k4_xboole_0(B_58, A_57))=k4_xboole_0(A_57, k4_xboole_0(B_58, A_57)))), inference(superposition, [status(thm), theory('equality')], [c_330, c_46])).
% 5.00/2.00  tff(c_4763, plain, (![A_182, B_183]: (k4_xboole_0(k2_xboole_0(A_182, B_183), k4_xboole_0(B_183, A_182))=A_182)), inference(demodulation, [status(thm), theory('equality')], [c_4288, c_336])).
% 5.00/2.00  tff(c_4928, plain, (![A_26, B_27]: (k4_xboole_0(k2_xboole_0(k3_xboole_0(A_26, B_27), A_26), k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(superposition, [status(thm), theory('equality')], [c_48, c_4763])).
% 5.00/2.00  tff(c_4987, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(demodulation, [status(thm), theory('equality')], [c_373, c_2, c_4928])).
% 5.00/2.00  tff(c_50, plain, (k4_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_5'))!=k3_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.00/2.00  tff(c_5902, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4987, c_50])).
% 5.00/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.00/2.00  
% 5.00/2.00  Inference rules
% 5.00/2.00  ----------------------
% 5.00/2.00  #Ref     : 0
% 5.00/2.00  #Sup     : 1457
% 5.00/2.00  #Fact    : 0
% 5.00/2.00  #Define  : 0
% 5.00/2.00  #Split   : 0
% 5.00/2.00  #Chain   : 0
% 5.00/2.00  #Close   : 0
% 5.00/2.00  
% 5.00/2.00  Ordering : KBO
% 5.00/2.00  
% 5.00/2.00  Simplification rules
% 5.00/2.00  ----------------------
% 5.00/2.00  #Subsume      : 114
% 5.00/2.00  #Demod        : 1525
% 5.00/2.00  #Tautology    : 1011
% 5.00/2.00  #SimpNegUnit  : 0
% 5.00/2.00  #BackRed      : 3
% 5.00/2.00  
% 5.00/2.00  #Partial instantiations: 0
% 5.00/2.00  #Strategies tried      : 1
% 5.00/2.00  
% 5.00/2.00  Timing (in seconds)
% 5.00/2.00  ----------------------
% 5.00/2.00  Preprocessing        : 0.32
% 5.00/2.00  Parsing              : 0.17
% 5.00/2.00  CNF conversion       : 0.02
% 5.00/2.00  Main loop            : 0.85
% 5.00/2.00  Inferencing          : 0.27
% 5.00/2.00  Reduction            : 0.39
% 5.00/2.00  Demodulation         : 0.33
% 5.00/2.00  BG Simplification    : 0.03
% 5.00/2.00  Subsumption          : 0.12
% 5.00/2.00  Abstraction          : 0.04
% 5.00/2.00  MUC search           : 0.00
% 5.00/2.00  Cooper               : 0.00
% 5.00/2.00  Total                : 1.20
% 5.00/2.00  Index Insertion      : 0.00
% 5.00/2.00  Index Deletion       : 0.00
% 5.00/2.00  Index Matching       : 0.00
% 5.00/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
