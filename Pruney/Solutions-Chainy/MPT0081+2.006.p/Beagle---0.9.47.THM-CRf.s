%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:57 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :   60 (  99 expanded)
%              Number of leaves         :   23 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :   69 ( 141 expanded)
%              Number of equality atoms :   18 (  37 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
          & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_66,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

tff(c_30,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_53,plain,(
    ! [B_35,A_36] :
      ( r1_xboole_0(B_35,A_36)
      | ~ r1_xboole_0(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_56,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_53])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_121,plain,(
    ! [A_47,B_48,C_49] :
      ( ~ r1_xboole_0(A_47,B_48)
      | ~ r2_hidden(C_49,k3_xboole_0(A_47,B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1284,plain,(
    ! [A_116,B_117,B_118] :
      ( ~ r1_xboole_0(A_116,B_117)
      | r1_tarski(k3_xboole_0(A_116,B_117),B_118) ) ),
    inference(resolution,[status(thm)],[c_6,c_121])).

tff(c_26,plain,(
    ! [A_26] : k4_xboole_0(k1_xboole_0,A_26) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_61,plain,(
    ! [A_37,B_38] :
      ( k1_xboole_0 = A_37
      | ~ r1_tarski(A_37,k4_xboole_0(B_38,A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_64,plain,(
    ! [A_26] :
      ( k1_xboole_0 = A_26
      | ~ r1_tarski(A_26,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_61])).

tff(c_1308,plain,(
    ! [A_121,B_122] :
      ( k3_xboole_0(A_121,B_122) = k1_xboole_0
      | ~ r1_xboole_0(A_121,B_122) ) ),
    inference(resolution,[status(thm)],[c_1284,c_64])).

tff(c_1315,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_1308])).

tff(c_12,plain,(
    ! [A_8,B_9,C_12] :
      ( ~ r1_xboole_0(A_8,B_9)
      | ~ r2_hidden(C_12,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1335,plain,(
    ! [C_12] :
      ( ~ r1_xboole_0('#skF_4','#skF_3')
      | ~ r2_hidden(C_12,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1315,c_12])).

tff(c_1346,plain,(
    ! [C_12] : ~ r2_hidden(C_12,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1335])).

tff(c_24,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k4_xboole_0(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_130,plain,(
    ! [A_50,B_51] : k4_xboole_0(A_50,k4_xboole_0(A_50,B_51)) = k3_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_169,plain,(
    ! [B_52] : k3_xboole_0(k1_xboole_0,B_52) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_26])).

tff(c_174,plain,(
    ! [B_52,C_12] :
      ( ~ r1_xboole_0(k1_xboole_0,B_52)
      | ~ r2_hidden(C_12,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_12])).

tff(c_214,plain,(
    ! [C_12] : ~ r2_hidden(C_12,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_174])).

tff(c_579,plain,(
    ! [A_82,B_83,B_84] :
      ( ~ r1_xboole_0(A_82,B_83)
      | r1_tarski(k3_xboole_0(A_82,B_83),B_84) ) ),
    inference(resolution,[status(thm)],[c_6,c_121])).

tff(c_618,plain,(
    ! [A_87,B_88] :
      ( k3_xboole_0(A_87,B_88) = k1_xboole_0
      | ~ r1_xboole_0(A_87,B_88) ) ),
    inference(resolution,[status(thm)],[c_579,c_64])).

tff(c_635,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_618])).

tff(c_28,plain,(
    ! [A_27,B_28,C_29] : k4_xboole_0(k3_xboole_0(A_27,B_28),k3_xboole_0(A_27,C_29)) = k3_xboole_0(A_27,k4_xboole_0(B_28,C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_642,plain,(
    ! [C_29] : k4_xboole_0(k1_xboole_0,k3_xboole_0('#skF_3',C_29)) = k3_xboole_0('#skF_3',k4_xboole_0('#skF_4',C_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_635,c_28])).

tff(c_847,plain,(
    ! [C_90] : k3_xboole_0('#skF_3',k4_xboole_0('#skF_4',C_90)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_642])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_2'(A_8,B_9),k3_xboole_0(A_8,B_9))
      | r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_861,plain,(
    ! [C_90] :
      ( r2_hidden('#skF_2'('#skF_3',k4_xboole_0('#skF_4',C_90)),k1_xboole_0)
      | r1_xboole_0('#skF_3',k4_xboole_0('#skF_4',C_90)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_847,c_10])).

tff(c_970,plain,(
    ! [C_94] : r1_xboole_0('#skF_3',k4_xboole_0('#skF_4',C_94)) ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_861])).

tff(c_983,plain,(
    ! [B_25] : r1_xboole_0('#skF_3',k3_xboole_0('#skF_4',B_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_970])).

tff(c_32,plain,(
    ~ r1_xboole_0('#skF_3',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1018,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_983,c_32])).

tff(c_1019,plain,(
    ! [B_52] : ~ r1_xboole_0(k1_xboole_0,B_52) ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_146,plain,(
    ! [B_51] : k3_xboole_0(k1_xboole_0,B_51) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_26])).

tff(c_1174,plain,(
    ! [A_107,B_108] :
      ( r2_hidden('#skF_2'(A_107,B_108),k3_xboole_0(A_107,B_108))
      | r1_xboole_0(A_107,B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1185,plain,(
    ! [B_51] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_51),k1_xboole_0)
      | r1_xboole_0(k1_xboole_0,B_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_1174])).

tff(c_1191,plain,(
    ! [B_51] : r2_hidden('#skF_2'(k1_xboole_0,B_51),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_1019,c_1185])).

tff(c_1435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1346,c_1191])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:23:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/1.45  
% 3.01/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/1.45  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.01/1.45  
% 3.01/1.45  %Foreground sorts:
% 3.01/1.45  
% 3.01/1.45  
% 3.01/1.45  %Background operators:
% 3.01/1.45  
% 3.01/1.45  
% 3.01/1.45  %Foreground operators:
% 3.01/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.01/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.01/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.01/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.01/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.01/1.45  tff('#skF_5', type, '#skF_5': $i).
% 3.01/1.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.01/1.45  tff('#skF_3', type, '#skF_3': $i).
% 3.01/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.01/1.45  tff('#skF_4', type, '#skF_4': $i).
% 3.01/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.01/1.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.01/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.01/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.01/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.01/1.45  
% 3.01/1.47  tff(f_75, negated_conjecture, ~(![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_xboole_1)).
% 3.01/1.47  tff(f_36, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.01/1.47  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.01/1.47  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.01/1.47  tff(f_66, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 3.01/1.47  tff(f_58, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 3.01/1.47  tff(f_64, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.01/1.47  tff(f_68, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_xboole_1)).
% 3.01/1.47  tff(c_30, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.01/1.47  tff(c_53, plain, (![B_35, A_36]: (r1_xboole_0(B_35, A_36) | ~r1_xboole_0(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.01/1.47  tff(c_56, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_53])).
% 3.01/1.47  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.01/1.47  tff(c_121, plain, (![A_47, B_48, C_49]: (~r1_xboole_0(A_47, B_48) | ~r2_hidden(C_49, k3_xboole_0(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.01/1.47  tff(c_1284, plain, (![A_116, B_117, B_118]: (~r1_xboole_0(A_116, B_117) | r1_tarski(k3_xboole_0(A_116, B_117), B_118))), inference(resolution, [status(thm)], [c_6, c_121])).
% 3.01/1.47  tff(c_26, plain, (![A_26]: (k4_xboole_0(k1_xboole_0, A_26)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.01/1.47  tff(c_61, plain, (![A_37, B_38]: (k1_xboole_0=A_37 | ~r1_tarski(A_37, k4_xboole_0(B_38, A_37)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.01/1.47  tff(c_64, plain, (![A_26]: (k1_xboole_0=A_26 | ~r1_tarski(A_26, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_61])).
% 3.01/1.47  tff(c_1308, plain, (![A_121, B_122]: (k3_xboole_0(A_121, B_122)=k1_xboole_0 | ~r1_xboole_0(A_121, B_122))), inference(resolution, [status(thm)], [c_1284, c_64])).
% 3.01/1.47  tff(c_1315, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_1308])).
% 3.01/1.47  tff(c_12, plain, (![A_8, B_9, C_12]: (~r1_xboole_0(A_8, B_9) | ~r2_hidden(C_12, k3_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.01/1.47  tff(c_1335, plain, (![C_12]: (~r1_xboole_0('#skF_4', '#skF_3') | ~r2_hidden(C_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1315, c_12])).
% 3.01/1.47  tff(c_1346, plain, (![C_12]: (~r2_hidden(C_12, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1335])).
% 3.01/1.47  tff(c_24, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k4_xboole_0(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.01/1.47  tff(c_130, plain, (![A_50, B_51]: (k4_xboole_0(A_50, k4_xboole_0(A_50, B_51))=k3_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.01/1.47  tff(c_169, plain, (![B_52]: (k3_xboole_0(k1_xboole_0, B_52)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_130, c_26])).
% 3.01/1.47  tff(c_174, plain, (![B_52, C_12]: (~r1_xboole_0(k1_xboole_0, B_52) | ~r2_hidden(C_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_169, c_12])).
% 3.01/1.47  tff(c_214, plain, (![C_12]: (~r2_hidden(C_12, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_174])).
% 3.01/1.47  tff(c_579, plain, (![A_82, B_83, B_84]: (~r1_xboole_0(A_82, B_83) | r1_tarski(k3_xboole_0(A_82, B_83), B_84))), inference(resolution, [status(thm)], [c_6, c_121])).
% 3.01/1.47  tff(c_618, plain, (![A_87, B_88]: (k3_xboole_0(A_87, B_88)=k1_xboole_0 | ~r1_xboole_0(A_87, B_88))), inference(resolution, [status(thm)], [c_579, c_64])).
% 3.01/1.47  tff(c_635, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_618])).
% 3.01/1.47  tff(c_28, plain, (![A_27, B_28, C_29]: (k4_xboole_0(k3_xboole_0(A_27, B_28), k3_xboole_0(A_27, C_29))=k3_xboole_0(A_27, k4_xboole_0(B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.01/1.47  tff(c_642, plain, (![C_29]: (k4_xboole_0(k1_xboole_0, k3_xboole_0('#skF_3', C_29))=k3_xboole_0('#skF_3', k4_xboole_0('#skF_4', C_29)))), inference(superposition, [status(thm), theory('equality')], [c_635, c_28])).
% 3.01/1.47  tff(c_847, plain, (![C_90]: (k3_xboole_0('#skF_3', k4_xboole_0('#skF_4', C_90))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_642])).
% 3.01/1.47  tff(c_10, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), k3_xboole_0(A_8, B_9)) | r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.01/1.47  tff(c_861, plain, (![C_90]: (r2_hidden('#skF_2'('#skF_3', k4_xboole_0('#skF_4', C_90)), k1_xboole_0) | r1_xboole_0('#skF_3', k4_xboole_0('#skF_4', C_90)))), inference(superposition, [status(thm), theory('equality')], [c_847, c_10])).
% 3.01/1.47  tff(c_970, plain, (![C_94]: (r1_xboole_0('#skF_3', k4_xboole_0('#skF_4', C_94)))), inference(negUnitSimplification, [status(thm)], [c_214, c_861])).
% 3.01/1.47  tff(c_983, plain, (![B_25]: (r1_xboole_0('#skF_3', k3_xboole_0('#skF_4', B_25)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_970])).
% 3.01/1.47  tff(c_32, plain, (~r1_xboole_0('#skF_3', k3_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.01/1.47  tff(c_1018, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_983, c_32])).
% 3.01/1.47  tff(c_1019, plain, (![B_52]: (~r1_xboole_0(k1_xboole_0, B_52))), inference(splitRight, [status(thm)], [c_174])).
% 3.01/1.47  tff(c_146, plain, (![B_51]: (k3_xboole_0(k1_xboole_0, B_51)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_130, c_26])).
% 3.01/1.47  tff(c_1174, plain, (![A_107, B_108]: (r2_hidden('#skF_2'(A_107, B_108), k3_xboole_0(A_107, B_108)) | r1_xboole_0(A_107, B_108))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.01/1.47  tff(c_1185, plain, (![B_51]: (r2_hidden('#skF_2'(k1_xboole_0, B_51), k1_xboole_0) | r1_xboole_0(k1_xboole_0, B_51))), inference(superposition, [status(thm), theory('equality')], [c_146, c_1174])).
% 3.01/1.47  tff(c_1191, plain, (![B_51]: (r2_hidden('#skF_2'(k1_xboole_0, B_51), k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_1019, c_1185])).
% 3.01/1.47  tff(c_1435, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1346, c_1191])).
% 3.01/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/1.47  
% 3.01/1.47  Inference rules
% 3.01/1.47  ----------------------
% 3.01/1.47  #Ref     : 0
% 3.01/1.47  #Sup     : 340
% 3.01/1.47  #Fact    : 0
% 3.01/1.47  #Define  : 0
% 3.01/1.47  #Split   : 1
% 3.01/1.47  #Chain   : 0
% 3.01/1.47  #Close   : 0
% 3.01/1.47  
% 3.01/1.47  Ordering : KBO
% 3.01/1.47  
% 3.01/1.47  Simplification rules
% 3.01/1.47  ----------------------
% 3.01/1.47  #Subsume      : 10
% 3.01/1.47  #Demod        : 245
% 3.01/1.47  #Tautology    : 190
% 3.01/1.47  #SimpNegUnit  : 9
% 3.01/1.47  #BackRed      : 2
% 3.01/1.47  
% 3.01/1.47  #Partial instantiations: 0
% 3.01/1.47  #Strategies tried      : 1
% 3.01/1.47  
% 3.01/1.47  Timing (in seconds)
% 3.01/1.47  ----------------------
% 3.01/1.47  Preprocessing        : 0.28
% 3.01/1.47  Parsing              : 0.16
% 3.01/1.47  CNF conversion       : 0.02
% 3.01/1.47  Main loop            : 0.41
% 3.01/1.47  Inferencing          : 0.16
% 3.01/1.47  Reduction            : 0.15
% 3.01/1.47  Demodulation         : 0.11
% 3.01/1.47  BG Simplification    : 0.02
% 3.01/1.47  Subsumption          : 0.06
% 3.01/1.47  Abstraction          : 0.02
% 3.01/1.47  MUC search           : 0.00
% 3.01/1.47  Cooper               : 0.00
% 3.01/1.47  Total                : 0.72
% 3.01/1.47  Index Insertion      : 0.00
% 3.01/1.47  Index Deletion       : 0.00
% 3.01/1.47  Index Matching       : 0.00
% 3.01/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
