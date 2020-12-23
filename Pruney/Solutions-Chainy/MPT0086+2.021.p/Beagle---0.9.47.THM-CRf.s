%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:16 EST 2020

% Result     : Theorem 4.18s
% Output     : CNFRefutation 4.34s
% Verified   : 
% Statistics : Number of formulae       :   56 (  89 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :   59 (  99 expanded)
%              Number of equality atoms :   27 (  57 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_71,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_47,axiom,(
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

tff(f_69,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_73,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_22,plain,(
    ! [A_18,B_19,C_20] : k4_xboole_0(k4_xboole_0(A_18,B_19),C_20) = k4_xboole_0(A_18,k2_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [A_17] : k4_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_83,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k4_xboole_0(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_112,plain,(
    ! [A_42] : k4_xboole_0(A_42,A_42) = k3_xboole_0(A_42,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_83])).

tff(c_128,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_20])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_147,plain,(
    ! [A_43,B_44,C_45] :
      ( ~ r1_xboole_0(A_43,B_44)
      | ~ r2_hidden(C_45,k3_xboole_0(A_43,B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_150,plain,(
    ! [C_45] :
      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
      | ~ r2_hidden(C_45,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_147])).

tff(c_178,plain,(
    ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_181,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_178])).

tff(c_185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_181])).

tff(c_188,plain,(
    ! [C_50] : ~ r2_hidden(C_50,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_212,plain,(
    ! [A_54] : r1_xboole_0(A_54,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_188])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_219,plain,(
    ! [A_54] : k3_xboole_0(A_54,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_212,c_2])).

tff(c_104,plain,(
    ! [A_17] : k4_xboole_0(A_17,A_17) = k3_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_83])).

tff(c_331,plain,(
    ! [A_62] : k4_xboole_0(A_62,A_62) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_104])).

tff(c_359,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k2_xboole_0(B_19,k4_xboole_0(A_18,B_19))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_331])).

tff(c_36,plain,(
    ! [A_24,B_25] : r1_tarski(k4_xboole_0(A_24,B_25),A_24) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_39,plain,(
    ! [A_17] : r1_tarski(A_17,A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_36])).

tff(c_42,plain,(
    ! [A_29,B_30] :
      ( k2_xboole_0(A_29,B_30) = B_30
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_49,plain,(
    ! [A_17] : k2_xboole_0(A_17,A_17) = A_17 ),
    inference(resolution,[status(thm)],[c_39,c_42])).

tff(c_248,plain,(
    ! [A_57,B_58,C_59] : k4_xboole_0(k4_xboole_0(A_57,B_58),C_59) = k4_xboole_0(A_57,k2_xboole_0(B_58,C_59)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_24,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_261,plain,(
    ! [A_57,B_58,B_22] : k4_xboole_0(A_57,k2_xboole_0(B_58,k4_xboole_0(k4_xboole_0(A_57,B_58),B_22))) = k3_xboole_0(k4_xboole_0(A_57,B_58),B_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_24])).

tff(c_4976,plain,(
    ! [A_189,B_190,B_191] : k4_xboole_0(A_189,k2_xboole_0(B_190,k4_xboole_0(A_189,k2_xboole_0(B_190,B_191)))) = k3_xboole_0(k4_xboole_0(A_189,B_190),B_191) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_261])).

tff(c_5193,plain,(
    ! [A_189,A_17] : k4_xboole_0(A_189,k2_xboole_0(A_17,k4_xboole_0(A_189,A_17))) = k3_xboole_0(k4_xboole_0(A_189,A_17),A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_4976])).

tff(c_5232,plain,(
    ! [A_189,A_17] : k3_xboole_0(k4_xboole_0(A_189,A_17),A_17) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_5193])).

tff(c_73,plain,(
    ! [A_34,B_35] :
      ( r1_xboole_0(A_34,B_35)
      | k3_xboole_0(A_34,B_35) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_26,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_81,plain,(
    k3_xboole_0(k4_xboole_0('#skF_3','#skF_4'),'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_73,c_26])).

tff(c_5235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5232,c_81])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n016.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 10:41:19 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.18/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.18/1.82  
% 4.18/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.18/1.82  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.18/1.82  
% 4.18/1.82  %Foreground sorts:
% 4.18/1.82  
% 4.18/1.82  
% 4.18/1.82  %Background operators:
% 4.18/1.82  
% 4.18/1.82  
% 4.18/1.82  %Foreground operators:
% 4.18/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.18/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.18/1.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.18/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.18/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.18/1.82  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.18/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.18/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.18/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.18/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.18/1.82  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.18/1.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.18/1.82  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.18/1.82  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.18/1.82  
% 4.34/1.83  tff(f_71, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.34/1.83  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.34/1.83  tff(f_69, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.34/1.83  tff(f_73, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.34/1.83  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.34/1.83  tff(f_61, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.34/1.83  tff(f_67, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.34/1.83  tff(f_65, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.34/1.83  tff(f_76, negated_conjecture, ~(![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.34/1.83  tff(c_22, plain, (![A_18, B_19, C_20]: (k4_xboole_0(k4_xboole_0(A_18, B_19), C_20)=k4_xboole_0(A_18, k2_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.34/1.83  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.34/1.83  tff(c_20, plain, (![A_17]: (k4_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.34/1.83  tff(c_83, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k4_xboole_0(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.34/1.83  tff(c_112, plain, (![A_42]: (k4_xboole_0(A_42, A_42)=k3_xboole_0(A_42, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_83])).
% 4.34/1.83  tff(c_128, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_112, c_20])).
% 4.34/1.83  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.34/1.83  tff(c_147, plain, (![A_43, B_44, C_45]: (~r1_xboole_0(A_43, B_44) | ~r2_hidden(C_45, k3_xboole_0(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.34/1.83  tff(c_150, plain, (![C_45]: (~r1_xboole_0(k1_xboole_0, k1_xboole_0) | ~r2_hidden(C_45, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_128, c_147])).
% 4.34/1.83  tff(c_178, plain, (~r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(splitLeft, [status(thm)], [c_150])).
% 4.34/1.83  tff(c_181, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_178])).
% 4.34/1.83  tff(c_185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_128, c_181])).
% 4.34/1.83  tff(c_188, plain, (![C_50]: (~r2_hidden(C_50, k1_xboole_0))), inference(splitRight, [status(thm)], [c_150])).
% 4.34/1.83  tff(c_212, plain, (![A_54]: (r1_xboole_0(A_54, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_188])).
% 4.34/1.83  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.34/1.83  tff(c_219, plain, (![A_54]: (k3_xboole_0(A_54, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_212, c_2])).
% 4.34/1.83  tff(c_104, plain, (![A_17]: (k4_xboole_0(A_17, A_17)=k3_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_83])).
% 4.34/1.83  tff(c_331, plain, (![A_62]: (k4_xboole_0(A_62, A_62)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_219, c_104])).
% 4.34/1.83  tff(c_359, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k2_xboole_0(B_19, k4_xboole_0(A_18, B_19)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_331])).
% 4.34/1.83  tff(c_36, plain, (![A_24, B_25]: (r1_tarski(k4_xboole_0(A_24, B_25), A_24))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.34/1.83  tff(c_39, plain, (![A_17]: (r1_tarski(A_17, A_17))), inference(superposition, [status(thm), theory('equality')], [c_20, c_36])).
% 4.34/1.83  tff(c_42, plain, (![A_29, B_30]: (k2_xboole_0(A_29, B_30)=B_30 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.34/1.83  tff(c_49, plain, (![A_17]: (k2_xboole_0(A_17, A_17)=A_17)), inference(resolution, [status(thm)], [c_39, c_42])).
% 4.34/1.83  tff(c_248, plain, (![A_57, B_58, C_59]: (k4_xboole_0(k4_xboole_0(A_57, B_58), C_59)=k4_xboole_0(A_57, k2_xboole_0(B_58, C_59)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.34/1.83  tff(c_24, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.34/1.83  tff(c_261, plain, (![A_57, B_58, B_22]: (k4_xboole_0(A_57, k2_xboole_0(B_58, k4_xboole_0(k4_xboole_0(A_57, B_58), B_22)))=k3_xboole_0(k4_xboole_0(A_57, B_58), B_22))), inference(superposition, [status(thm), theory('equality')], [c_248, c_24])).
% 4.34/1.83  tff(c_4976, plain, (![A_189, B_190, B_191]: (k4_xboole_0(A_189, k2_xboole_0(B_190, k4_xboole_0(A_189, k2_xboole_0(B_190, B_191))))=k3_xboole_0(k4_xboole_0(A_189, B_190), B_191))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_261])).
% 4.34/1.83  tff(c_5193, plain, (![A_189, A_17]: (k4_xboole_0(A_189, k2_xboole_0(A_17, k4_xboole_0(A_189, A_17)))=k3_xboole_0(k4_xboole_0(A_189, A_17), A_17))), inference(superposition, [status(thm), theory('equality')], [c_49, c_4976])).
% 4.34/1.83  tff(c_5232, plain, (![A_189, A_17]: (k3_xboole_0(k4_xboole_0(A_189, A_17), A_17)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_359, c_5193])).
% 4.34/1.83  tff(c_73, plain, (![A_34, B_35]: (r1_xboole_0(A_34, B_35) | k3_xboole_0(A_34, B_35)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.34/1.83  tff(c_26, plain, (~r1_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.34/1.83  tff(c_81, plain, (k3_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_73, c_26])).
% 4.34/1.83  tff(c_5235, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5232, c_81])).
% 4.34/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.34/1.83  
% 4.34/1.83  Inference rules
% 4.34/1.83  ----------------------
% 4.34/1.83  #Ref     : 0
% 4.34/1.83  #Sup     : 1283
% 4.34/1.83  #Fact    : 0
% 4.34/1.83  #Define  : 0
% 4.34/1.83  #Split   : 1
% 4.34/1.83  #Chain   : 0
% 4.34/1.83  #Close   : 0
% 4.34/1.83  
% 4.34/1.83  Ordering : KBO
% 4.34/1.83  
% 4.34/1.83  Simplification rules
% 4.34/1.83  ----------------------
% 4.34/1.83  #Subsume      : 117
% 4.34/1.83  #Demod        : 867
% 4.34/1.83  #Tautology    : 758
% 4.34/1.83  #SimpNegUnit  : 4
% 4.34/1.83  #BackRed      : 5
% 4.34/1.83  
% 4.34/1.83  #Partial instantiations: 0
% 4.34/1.83  #Strategies tried      : 1
% 4.34/1.83  
% 4.34/1.83  Timing (in seconds)
% 4.34/1.83  ----------------------
% 4.34/1.83  Preprocessing        : 0.27
% 4.34/1.83  Parsing              : 0.16
% 4.34/1.83  CNF conversion       : 0.02
% 4.34/1.83  Main loop            : 0.77
% 4.34/1.83  Inferencing          : 0.27
% 4.34/1.83  Reduction            : 0.31
% 4.34/1.83  Demodulation         : 0.24
% 4.34/1.83  BG Simplification    : 0.03
% 4.34/1.83  Subsumption          : 0.11
% 4.34/1.83  Abstraction          : 0.04
% 4.34/1.83  MUC search           : 0.00
% 4.34/1.83  Cooper               : 0.00
% 4.34/1.83  Total                : 1.07
% 4.34/1.83  Index Insertion      : 0.00
% 4.34/1.83  Index Deletion       : 0.00
% 4.34/1.83  Index Matching       : 0.00
% 4.34/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
