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
% DateTime   : Thu Dec  3 09:44:02 EST 2020

% Result     : Theorem 4.22s
% Output     : CNFRefutation 4.38s
% Verified   : 
% Statistics : Number of formulae       :   59 (  93 expanded)
%              Number of leaves         :   23 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :   66 ( 116 expanded)
%              Number of equality atoms :   26 (  50 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(k3_xboole_0(C,A),k3_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_190,plain,(
    ! [A_34,B_35] :
      ( k3_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_xboole_0(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_194,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_190])).

tff(c_244,plain,(
    ! [A_38,B_39,C_40] :
      ( ~ r1_xboole_0(A_38,B_39)
      | ~ r2_hidden(C_40,k3_xboole_0(A_38,B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_250,plain,(
    ! [C_40] :
      ( ~ r1_xboole_0('#skF_2','#skF_3')
      | ~ r2_hidden(C_40,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_244])).

tff(c_264,plain,(
    ! [C_40] : ~ r2_hidden(C_40,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_250])).

tff(c_18,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_40,plain,(
    ! [B_26,A_27] : k3_xboole_0(B_26,A_27) = k3_xboole_0(A_27,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_56,plain,(
    ! [A_27] : k3_xboole_0(k1_xboole_0,A_27) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_14])).

tff(c_350,plain,(
    ! [A_48,B_49] : k4_xboole_0(A_48,k3_xboole_0(A_48,B_49)) = k4_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_406,plain,(
    ! [A_50] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_350])).

tff(c_433,plain,(
    ! [B_16] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,B_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_18])).

tff(c_454,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_433])).

tff(c_375,plain,(
    ! [A_27] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_350])).

tff(c_487,plain,(
    ! [A_27] : k4_xboole_0(k1_xboole_0,A_27) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_375])).

tff(c_204,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_2])).

tff(c_685,plain,(
    ! [A_67,B_68,C_69] : k4_xboole_0(k3_xboole_0(A_67,B_68),C_69) = k3_xboole_0(A_67,k4_xboole_0(B_68,C_69)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_720,plain,(
    ! [C_69] : k3_xboole_0('#skF_3',k4_xboole_0('#skF_2',C_69)) = k4_xboole_0(k1_xboole_0,C_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_685])).

tff(c_746,plain,(
    ! [C_70] : k3_xboole_0('#skF_3',k4_xboole_0('#skF_2',C_70)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_720])).

tff(c_781,plain,(
    ! [B_16] : k3_xboole_0('#skF_3',k3_xboole_0('#skF_2',B_16)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_746])).

tff(c_1164,plain,(
    ! [A_78,B_79] :
      ( r2_hidden('#skF_1'(A_78,B_79),k3_xboole_0(A_78,B_79))
      | r1_xboole_0(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1182,plain,(
    ! [B_16] :
      ( r2_hidden('#skF_1'('#skF_3',k3_xboole_0('#skF_2',B_16)),k1_xboole_0)
      | r1_xboole_0('#skF_3',k3_xboole_0('#skF_2',B_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_781,c_1164])).

tff(c_1212,plain,(
    ! [B_16] : r1_xboole_0('#skF_3',k3_xboole_0('#skF_2',B_16)) ),
    inference(negUnitSimplification,[status(thm)],[c_264,c_1182])).

tff(c_256,plain,(
    ! [A_1,B_2,C_40] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_40,k3_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_244])).

tff(c_1480,plain,(
    ! [B_91,A_92] :
      ( ~ r1_xboole_0(B_91,A_92)
      | r1_xboole_0(A_92,B_91) ) ),
    inference(resolution,[status(thm)],[c_1164,c_256])).

tff(c_1576,plain,(
    ! [B_95] : r1_xboole_0(k3_xboole_0('#skF_2',B_95),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1212,c_1480])).

tff(c_1593,plain,(
    ! [B_2] : r1_xboole_0(k3_xboole_0(B_2,'#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1576])).

tff(c_12,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_457,plain,(
    ! [A_51,C_52,B_53] :
      ( r1_xboole_0(A_51,C_52)
      | ~ r1_xboole_0(A_51,k2_xboole_0(B_53,C_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1716,plain,(
    ! [A_100,A_101,B_102] :
      ( r1_xboole_0(A_100,k3_xboole_0(A_101,B_102))
      | ~ r1_xboole_0(A_100,A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_457])).

tff(c_3011,plain,(
    ! [A_121,B_122,A_123] :
      ( r1_xboole_0(A_121,k3_xboole_0(B_122,A_123))
      | ~ r1_xboole_0(A_121,A_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1716])).

tff(c_30,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_4','#skF_2'),k3_xboole_0('#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3019,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_4','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_3011,c_30])).

tff(c_3085,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1593,c_3019])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:50:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.22/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.22/1.81  
% 4.22/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.22/1.82  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.22/1.82  
% 4.22/1.82  %Foreground sorts:
% 4.22/1.82  
% 4.22/1.82  
% 4.22/1.82  %Background operators:
% 4.22/1.82  
% 4.22/1.82  
% 4.22/1.82  %Foreground operators:
% 4.22/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.22/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.22/1.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.22/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.22/1.82  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.22/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.22/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.22/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.22/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.22/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.22/1.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.22/1.82  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.22/1.82  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.22/1.82  
% 4.38/1.83  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.38/1.83  tff(f_78, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(k3_xboole_0(C, A), k3_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_xboole_1)).
% 4.38/1.83  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.38/1.83  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.38/1.83  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.38/1.83  tff(f_49, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 4.38/1.83  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.38/1.83  tff(f_55, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 4.38/1.83  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 4.38/1.83  tff(f_73, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 4.38/1.83  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.38/1.83  tff(c_32, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.38/1.83  tff(c_190, plain, (![A_34, B_35]: (k3_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.38/1.83  tff(c_194, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_190])).
% 4.38/1.83  tff(c_244, plain, (![A_38, B_39, C_40]: (~r1_xboole_0(A_38, B_39) | ~r2_hidden(C_40, k3_xboole_0(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.38/1.83  tff(c_250, plain, (![C_40]: (~r1_xboole_0('#skF_2', '#skF_3') | ~r2_hidden(C_40, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_194, c_244])).
% 4.38/1.83  tff(c_264, plain, (![C_40]: (~r2_hidden(C_40, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_250])).
% 4.38/1.83  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.38/1.83  tff(c_40, plain, (![B_26, A_27]: (k3_xboole_0(B_26, A_27)=k3_xboole_0(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.38/1.83  tff(c_14, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.38/1.83  tff(c_56, plain, (![A_27]: (k3_xboole_0(k1_xboole_0, A_27)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40, c_14])).
% 4.38/1.83  tff(c_350, plain, (![A_48, B_49]: (k4_xboole_0(A_48, k3_xboole_0(A_48, B_49))=k4_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.38/1.83  tff(c_406, plain, (![A_50]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_50))), inference(superposition, [status(thm), theory('equality')], [c_56, c_350])).
% 4.38/1.83  tff(c_433, plain, (![B_16]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k3_xboole_0(k1_xboole_0, B_16))), inference(superposition, [status(thm), theory('equality')], [c_406, c_18])).
% 4.38/1.83  tff(c_454, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_433])).
% 4.38/1.83  tff(c_375, plain, (![A_27]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_27))), inference(superposition, [status(thm), theory('equality')], [c_56, c_350])).
% 4.38/1.83  tff(c_487, plain, (![A_27]: (k4_xboole_0(k1_xboole_0, A_27)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_454, c_375])).
% 4.38/1.83  tff(c_204, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_194, c_2])).
% 4.38/1.83  tff(c_685, plain, (![A_67, B_68, C_69]: (k4_xboole_0(k3_xboole_0(A_67, B_68), C_69)=k3_xboole_0(A_67, k4_xboole_0(B_68, C_69)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.38/1.83  tff(c_720, plain, (![C_69]: (k3_xboole_0('#skF_3', k4_xboole_0('#skF_2', C_69))=k4_xboole_0(k1_xboole_0, C_69))), inference(superposition, [status(thm), theory('equality')], [c_204, c_685])).
% 4.38/1.83  tff(c_746, plain, (![C_70]: (k3_xboole_0('#skF_3', k4_xboole_0('#skF_2', C_70))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_487, c_720])).
% 4.38/1.83  tff(c_781, plain, (![B_16]: (k3_xboole_0('#skF_3', k3_xboole_0('#skF_2', B_16))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_746])).
% 4.38/1.83  tff(c_1164, plain, (![A_78, B_79]: (r2_hidden('#skF_1'(A_78, B_79), k3_xboole_0(A_78, B_79)) | r1_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.38/1.83  tff(c_1182, plain, (![B_16]: (r2_hidden('#skF_1'('#skF_3', k3_xboole_0('#skF_2', B_16)), k1_xboole_0) | r1_xboole_0('#skF_3', k3_xboole_0('#skF_2', B_16)))), inference(superposition, [status(thm), theory('equality')], [c_781, c_1164])).
% 4.38/1.83  tff(c_1212, plain, (![B_16]: (r1_xboole_0('#skF_3', k3_xboole_0('#skF_2', B_16)))), inference(negUnitSimplification, [status(thm)], [c_264, c_1182])).
% 4.38/1.83  tff(c_256, plain, (![A_1, B_2, C_40]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_40, k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_244])).
% 4.38/1.83  tff(c_1480, plain, (![B_91, A_92]: (~r1_xboole_0(B_91, A_92) | r1_xboole_0(A_92, B_91))), inference(resolution, [status(thm)], [c_1164, c_256])).
% 4.38/1.83  tff(c_1576, plain, (![B_95]: (r1_xboole_0(k3_xboole_0('#skF_2', B_95), '#skF_3'))), inference(resolution, [status(thm)], [c_1212, c_1480])).
% 4.38/1.83  tff(c_1593, plain, (![B_2]: (r1_xboole_0(k3_xboole_0(B_2, '#skF_2'), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1576])).
% 4.38/1.83  tff(c_12, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k3_xboole_0(A_10, B_11))=A_10)), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.38/1.83  tff(c_457, plain, (![A_51, C_52, B_53]: (r1_xboole_0(A_51, C_52) | ~r1_xboole_0(A_51, k2_xboole_0(B_53, C_52)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.38/1.83  tff(c_1716, plain, (![A_100, A_101, B_102]: (r1_xboole_0(A_100, k3_xboole_0(A_101, B_102)) | ~r1_xboole_0(A_100, A_101))), inference(superposition, [status(thm), theory('equality')], [c_12, c_457])).
% 4.38/1.83  tff(c_3011, plain, (![A_121, B_122, A_123]: (r1_xboole_0(A_121, k3_xboole_0(B_122, A_123)) | ~r1_xboole_0(A_121, A_123))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1716])).
% 4.38/1.83  tff(c_30, plain, (~r1_xboole_0(k3_xboole_0('#skF_4', '#skF_2'), k3_xboole_0('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.38/1.83  tff(c_3019, plain, (~r1_xboole_0(k3_xboole_0('#skF_4', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_3011, c_30])).
% 4.38/1.83  tff(c_3085, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1593, c_3019])).
% 4.38/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.38/1.83  
% 4.38/1.83  Inference rules
% 4.38/1.83  ----------------------
% 4.38/1.83  #Ref     : 0
% 4.38/1.83  #Sup     : 774
% 4.38/1.83  #Fact    : 0
% 4.38/1.83  #Define  : 0
% 4.38/1.83  #Split   : 0
% 4.38/1.83  #Chain   : 0
% 4.38/1.83  #Close   : 0
% 4.38/1.83  
% 4.38/1.83  Ordering : KBO
% 4.38/1.83  
% 4.38/1.83  Simplification rules
% 4.38/1.83  ----------------------
% 4.38/1.83  #Subsume      : 57
% 4.38/1.83  #Demod        : 594
% 4.38/1.83  #Tautology    : 515
% 4.38/1.83  #SimpNegUnit  : 16
% 4.38/1.83  #BackRed      : 3
% 4.38/1.83  
% 4.38/1.83  #Partial instantiations: 0
% 4.38/1.83  #Strategies tried      : 1
% 4.38/1.83  
% 4.38/1.83  Timing (in seconds)
% 4.38/1.83  ----------------------
% 4.38/1.83  Preprocessing        : 0.31
% 4.38/1.83  Parsing              : 0.17
% 4.38/1.83  CNF conversion       : 0.02
% 4.38/1.83  Main loop            : 0.76
% 4.38/1.83  Inferencing          : 0.24
% 4.38/1.83  Reduction            : 0.33
% 4.38/1.83  Demodulation         : 0.27
% 4.38/1.83  BG Simplification    : 0.03
% 4.38/1.83  Subsumption          : 0.11
% 4.38/1.83  Abstraction          : 0.04
% 4.38/1.83  MUC search           : 0.00
% 4.38/1.83  Cooper               : 0.00
% 4.38/1.83  Total                : 1.10
% 4.38/1.83  Index Insertion      : 0.00
% 4.38/1.83  Index Deletion       : 0.00
% 4.38/1.83  Index Matching       : 0.00
% 4.38/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
