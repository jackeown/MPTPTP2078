%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:12 EST 2020

% Result     : Theorem 21.05s
% Output     : CNFRefutation 21.19s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 143 expanded)
%              Number of leaves         :   23 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :   61 ( 206 expanded)
%              Number of equality atoms :   32 (  74 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_56,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_50,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_55,plain,(
    ! [A_30,B_31] :
      ( ~ r2_hidden('#skF_1'(A_30,B_31),B_31)
      | r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_61,plain,(
    ! [A_32] : r1_tarski(A_32,A_32) ),
    inference(resolution,[status(thm)],[c_6,c_55])).

tff(c_16,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_65,plain,(
    ! [A_32] : k3_xboole_0(A_32,A_32) = A_32 ),
    inference(resolution,[status(thm)],[c_61,c_16])).

tff(c_60,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_55])).

tff(c_239,plain,(
    ! [A_56,B_57,C_58] :
      ( r1_tarski(A_56,k2_xboole_0(B_57,C_58))
      | ~ r1_tarski(k4_xboole_0(A_56,B_57),C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_340,plain,(
    ! [A_64,B_65] : r1_tarski(A_64,k2_xboole_0(B_65,k4_xboole_0(A_64,B_65))) ),
    inference(resolution,[status(thm)],[c_60,c_239])).

tff(c_349,plain,(
    ! [A_64,B_65] : k3_xboole_0(A_64,k2_xboole_0(B_65,k4_xboole_0(A_64,B_65))) = A_64 ),
    inference(resolution,[status(thm)],[c_340,c_16])).

tff(c_18,plain,(
    ! [A_18] : k3_xboole_0(A_18,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_245,plain,(
    ! [A_59,B_60,C_61] : k2_xboole_0(k3_xboole_0(A_59,B_60),k3_xboole_0(A_59,C_61)) = k3_xboole_0(A_59,k2_xboole_0(B_60,C_61)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_505,plain,(
    ! [A_77,C_78] : k3_xboole_0(A_77,k2_xboole_0(k1_xboole_0,C_78)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(A_77,C_78)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_245])).

tff(c_14,plain,(
    ! [A_13,B_14,C_15] : k2_xboole_0(k3_xboole_0(A_13,B_14),k3_xboole_0(A_13,C_15)) = k3_xboole_0(A_13,k2_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6917,plain,(
    ! [A_228,C_229,C_230] : k2_xboole_0(k2_xboole_0(k1_xboole_0,k3_xboole_0(A_228,C_229)),k3_xboole_0(A_228,C_230)) = k3_xboole_0(A_228,k2_xboole_0(k2_xboole_0(k1_xboole_0,C_229),C_230)) ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_14])).

tff(c_12000,plain,(
    ! [A_284,C_285] : k3_xboole_0(A_284,k2_xboole_0(k2_xboole_0(k1_xboole_0,A_284),C_285)) = k2_xboole_0(k2_xboole_0(k1_xboole_0,A_284),k3_xboole_0(A_284,C_285)) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_6917])).

tff(c_70776,plain,(
    ! [A_746] : k2_xboole_0(k2_xboole_0(k1_xboole_0,A_746),k3_xboole_0(A_746,k4_xboole_0(A_746,k2_xboole_0(k1_xboole_0,A_746)))) = A_746 ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_12000])).

tff(c_12,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_350,plain,(
    ! [A_66,B_67] : k3_xboole_0(A_66,k2_xboole_0(B_67,k4_xboole_0(A_66,B_67))) = A_66 ),
    inference(resolution,[status(thm)],[c_340,c_16])).

tff(c_360,plain,(
    ! [A_66,B_67,C_15] : k3_xboole_0(A_66,k2_xboole_0(k2_xboole_0(B_67,k4_xboole_0(A_66,B_67)),C_15)) = k2_xboole_0(A_66,k3_xboole_0(A_66,C_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_14])).

tff(c_393,plain,(
    ! [A_66,B_67,C_15] : k3_xboole_0(A_66,k2_xboole_0(k2_xboole_0(B_67,k4_xboole_0(A_66,B_67)),C_15)) = A_66 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_360])).

tff(c_70908,plain,(
    ! [A_66] : k3_xboole_0(A_66,k4_xboole_0(A_66,k1_xboole_0)) = A_66 ),
    inference(superposition,[status(thm),theory(equality)],[c_70776,c_393])).

tff(c_549,plain,(
    ! [A_64] : k2_xboole_0(k1_xboole_0,k3_xboole_0(A_64,k4_xboole_0(A_64,k1_xboole_0))) = A_64 ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_505])).

tff(c_1261,plain,(
    ! [C_110] : k2_xboole_0(k1_xboole_0,k3_xboole_0(k2_xboole_0(k1_xboole_0,C_110),C_110)) = k2_xboole_0(k1_xboole_0,C_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_65])).

tff(c_1308,plain,(
    ! [A_64] : k2_xboole_0(k1_xboole_0,k3_xboole_0(A_64,k3_xboole_0(A_64,k4_xboole_0(A_64,k1_xboole_0)))) = k2_xboole_0(k1_xboole_0,k3_xboole_0(A_64,k4_xboole_0(A_64,k1_xboole_0))) ),
    inference(superposition,[status(thm),theory(equality)],[c_549,c_1261])).

tff(c_1355,plain,(
    ! [A_64] : k2_xboole_0(k1_xboole_0,k3_xboole_0(A_64,k3_xboole_0(A_64,k4_xboole_0(A_64,k1_xboole_0)))) = A_64 ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_1308])).

tff(c_71342,plain,(
    ! [A_64] : k2_xboole_0(k1_xboole_0,k3_xboole_0(A_64,A_64)) = A_64 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70908,c_1355])).

tff(c_71349,plain,(
    ! [A_64] : k2_xboole_0(k1_xboole_0,A_64) = A_64 ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_71342])).

tff(c_24,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_107,plain,(
    ! [A_35,B_36,C_37] :
      ( ~ r1_xboole_0(A_35,B_36)
      | ~ r2_hidden(C_37,k3_xboole_0(A_35,B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_168,plain,(
    ! [A_46,B_47,B_48] :
      ( ~ r1_xboole_0(A_46,B_47)
      | r1_tarski(k3_xboole_0(A_46,B_47),B_48) ) ),
    inference(resolution,[status(thm)],[c_6,c_107])).

tff(c_1362,plain,(
    ! [A_111,B_112,B_113] :
      ( k3_xboole_0(k3_xboole_0(A_111,B_112),B_113) = k3_xboole_0(A_111,B_112)
      | ~ r1_xboole_0(A_111,B_112) ) ),
    inference(resolution,[status(thm)],[c_168,c_16])).

tff(c_1530,plain,(
    ! [A_114,B_115] :
      ( k3_xboole_0(A_114,B_115) = k1_xboole_0
      | ~ r1_xboole_0(A_114,B_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1362,c_18])).

tff(c_1559,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_1530])).

tff(c_1581,plain,(
    ! [C_15] : k3_xboole_0('#skF_3',k2_xboole_0('#skF_4',C_15)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_3',C_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1559,c_14])).

tff(c_22,plain,(
    k3_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) != k3_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1636,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_3','#skF_5')) != k3_xboole_0('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1581,c_22])).

tff(c_72269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71349,c_1636])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:05:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.05/12.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.05/12.61  
% 21.05/12.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.05/12.61  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 21.05/12.61  
% 21.05/12.61  %Foreground sorts:
% 21.05/12.61  
% 21.05/12.61  
% 21.05/12.61  %Background operators:
% 21.05/12.61  
% 21.05/12.61  
% 21.05/12.61  %Foreground operators:
% 21.05/12.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.05/12.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 21.05/12.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 21.05/12.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 21.05/12.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 21.05/12.61  tff('#skF_5', type, '#skF_5': $i).
% 21.05/12.61  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 21.05/12.61  tff('#skF_3', type, '#skF_3': $i).
% 21.05/12.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.05/12.61  tff('#skF_4', type, '#skF_4': $i).
% 21.05/12.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.05/12.61  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 21.05/12.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 21.05/12.61  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 21.05/12.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 21.05/12.61  
% 21.19/12.62  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 21.19/12.62  tff(f_54, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 21.19/12.62  tff(f_60, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 21.19/12.62  tff(f_56, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 21.19/12.62  tff(f_50, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 21.19/12.62  tff(f_48, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 21.19/12.62  tff(f_65, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 21.19/12.62  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 21.19/12.62  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 21.19/12.62  tff(c_55, plain, (![A_30, B_31]: (~r2_hidden('#skF_1'(A_30, B_31), B_31) | r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_32])).
% 21.19/12.62  tff(c_61, plain, (![A_32]: (r1_tarski(A_32, A_32))), inference(resolution, [status(thm)], [c_6, c_55])).
% 21.19/12.62  tff(c_16, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 21.19/12.62  tff(c_65, plain, (![A_32]: (k3_xboole_0(A_32, A_32)=A_32)), inference(resolution, [status(thm)], [c_61, c_16])).
% 21.19/12.62  tff(c_60, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_55])).
% 21.19/12.62  tff(c_239, plain, (![A_56, B_57, C_58]: (r1_tarski(A_56, k2_xboole_0(B_57, C_58)) | ~r1_tarski(k4_xboole_0(A_56, B_57), C_58))), inference(cnfTransformation, [status(thm)], [f_60])).
% 21.19/12.62  tff(c_340, plain, (![A_64, B_65]: (r1_tarski(A_64, k2_xboole_0(B_65, k4_xboole_0(A_64, B_65))))), inference(resolution, [status(thm)], [c_60, c_239])).
% 21.19/12.62  tff(c_349, plain, (![A_64, B_65]: (k3_xboole_0(A_64, k2_xboole_0(B_65, k4_xboole_0(A_64, B_65)))=A_64)), inference(resolution, [status(thm)], [c_340, c_16])).
% 21.19/12.62  tff(c_18, plain, (![A_18]: (k3_xboole_0(A_18, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 21.19/12.62  tff(c_245, plain, (![A_59, B_60, C_61]: (k2_xboole_0(k3_xboole_0(A_59, B_60), k3_xboole_0(A_59, C_61))=k3_xboole_0(A_59, k2_xboole_0(B_60, C_61)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 21.19/12.62  tff(c_505, plain, (![A_77, C_78]: (k3_xboole_0(A_77, k2_xboole_0(k1_xboole_0, C_78))=k2_xboole_0(k1_xboole_0, k3_xboole_0(A_77, C_78)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_245])).
% 21.19/12.62  tff(c_14, plain, (![A_13, B_14, C_15]: (k2_xboole_0(k3_xboole_0(A_13, B_14), k3_xboole_0(A_13, C_15))=k3_xboole_0(A_13, k2_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 21.19/12.62  tff(c_6917, plain, (![A_228, C_229, C_230]: (k2_xboole_0(k2_xboole_0(k1_xboole_0, k3_xboole_0(A_228, C_229)), k3_xboole_0(A_228, C_230))=k3_xboole_0(A_228, k2_xboole_0(k2_xboole_0(k1_xboole_0, C_229), C_230)))), inference(superposition, [status(thm), theory('equality')], [c_505, c_14])).
% 21.19/12.62  tff(c_12000, plain, (![A_284, C_285]: (k3_xboole_0(A_284, k2_xboole_0(k2_xboole_0(k1_xboole_0, A_284), C_285))=k2_xboole_0(k2_xboole_0(k1_xboole_0, A_284), k3_xboole_0(A_284, C_285)))), inference(superposition, [status(thm), theory('equality')], [c_65, c_6917])).
% 21.19/12.62  tff(c_70776, plain, (![A_746]: (k2_xboole_0(k2_xboole_0(k1_xboole_0, A_746), k3_xboole_0(A_746, k4_xboole_0(A_746, k2_xboole_0(k1_xboole_0, A_746))))=A_746)), inference(superposition, [status(thm), theory('equality')], [c_349, c_12000])).
% 21.19/12.62  tff(c_12, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k3_xboole_0(A_11, B_12))=A_11)), inference(cnfTransformation, [status(thm)], [f_48])).
% 21.19/12.62  tff(c_350, plain, (![A_66, B_67]: (k3_xboole_0(A_66, k2_xboole_0(B_67, k4_xboole_0(A_66, B_67)))=A_66)), inference(resolution, [status(thm)], [c_340, c_16])).
% 21.19/12.62  tff(c_360, plain, (![A_66, B_67, C_15]: (k3_xboole_0(A_66, k2_xboole_0(k2_xboole_0(B_67, k4_xboole_0(A_66, B_67)), C_15))=k2_xboole_0(A_66, k3_xboole_0(A_66, C_15)))), inference(superposition, [status(thm), theory('equality')], [c_350, c_14])).
% 21.19/12.62  tff(c_393, plain, (![A_66, B_67, C_15]: (k3_xboole_0(A_66, k2_xboole_0(k2_xboole_0(B_67, k4_xboole_0(A_66, B_67)), C_15))=A_66)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_360])).
% 21.19/12.62  tff(c_70908, plain, (![A_66]: (k3_xboole_0(A_66, k4_xboole_0(A_66, k1_xboole_0))=A_66)), inference(superposition, [status(thm), theory('equality')], [c_70776, c_393])).
% 21.19/12.62  tff(c_549, plain, (![A_64]: (k2_xboole_0(k1_xboole_0, k3_xboole_0(A_64, k4_xboole_0(A_64, k1_xboole_0)))=A_64)), inference(superposition, [status(thm), theory('equality')], [c_349, c_505])).
% 21.19/12.62  tff(c_1261, plain, (![C_110]: (k2_xboole_0(k1_xboole_0, k3_xboole_0(k2_xboole_0(k1_xboole_0, C_110), C_110))=k2_xboole_0(k1_xboole_0, C_110))), inference(superposition, [status(thm), theory('equality')], [c_505, c_65])).
% 21.19/12.62  tff(c_1308, plain, (![A_64]: (k2_xboole_0(k1_xboole_0, k3_xboole_0(A_64, k3_xboole_0(A_64, k4_xboole_0(A_64, k1_xboole_0))))=k2_xboole_0(k1_xboole_0, k3_xboole_0(A_64, k4_xboole_0(A_64, k1_xboole_0))))), inference(superposition, [status(thm), theory('equality')], [c_549, c_1261])).
% 21.19/12.62  tff(c_1355, plain, (![A_64]: (k2_xboole_0(k1_xboole_0, k3_xboole_0(A_64, k3_xboole_0(A_64, k4_xboole_0(A_64, k1_xboole_0))))=A_64)), inference(demodulation, [status(thm), theory('equality')], [c_549, c_1308])).
% 21.19/12.62  tff(c_71342, plain, (![A_64]: (k2_xboole_0(k1_xboole_0, k3_xboole_0(A_64, A_64))=A_64)), inference(demodulation, [status(thm), theory('equality')], [c_70908, c_1355])).
% 21.19/12.62  tff(c_71349, plain, (![A_64]: (k2_xboole_0(k1_xboole_0, A_64)=A_64)), inference(demodulation, [status(thm), theory('equality')], [c_65, c_71342])).
% 21.19/12.62  tff(c_24, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_65])).
% 21.19/12.62  tff(c_107, plain, (![A_35, B_36, C_37]: (~r1_xboole_0(A_35, B_36) | ~r2_hidden(C_37, k3_xboole_0(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 21.19/12.62  tff(c_168, plain, (![A_46, B_47, B_48]: (~r1_xboole_0(A_46, B_47) | r1_tarski(k3_xboole_0(A_46, B_47), B_48))), inference(resolution, [status(thm)], [c_6, c_107])).
% 21.19/12.62  tff(c_1362, plain, (![A_111, B_112, B_113]: (k3_xboole_0(k3_xboole_0(A_111, B_112), B_113)=k3_xboole_0(A_111, B_112) | ~r1_xboole_0(A_111, B_112))), inference(resolution, [status(thm)], [c_168, c_16])).
% 21.19/12.62  tff(c_1530, plain, (![A_114, B_115]: (k3_xboole_0(A_114, B_115)=k1_xboole_0 | ~r1_xboole_0(A_114, B_115))), inference(superposition, [status(thm), theory('equality')], [c_1362, c_18])).
% 21.19/12.62  tff(c_1559, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_1530])).
% 21.19/12.62  tff(c_1581, plain, (![C_15]: (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', C_15))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_3', C_15)))), inference(superposition, [status(thm), theory('equality')], [c_1559, c_14])).
% 21.19/12.62  tff(c_22, plain, (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))!=k3_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_65])).
% 21.19/12.62  tff(c_1636, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_3', '#skF_5'))!=k3_xboole_0('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1581, c_22])).
% 21.19/12.62  tff(c_72269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71349, c_1636])).
% 21.19/12.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.19/12.62  
% 21.19/12.62  Inference rules
% 21.19/12.62  ----------------------
% 21.19/12.62  #Ref     : 0
% 21.19/12.62  #Sup     : 18690
% 21.19/12.62  #Fact    : 0
% 21.19/12.62  #Define  : 0
% 21.19/12.62  #Split   : 11
% 21.19/12.62  #Chain   : 0
% 21.19/12.62  #Close   : 0
% 21.19/12.62  
% 21.19/12.62  Ordering : KBO
% 21.19/12.62  
% 21.19/12.62  Simplification rules
% 21.19/12.62  ----------------------
% 21.19/12.62  #Subsume      : 5489
% 21.19/12.62  #Demod        : 22522
% 21.19/12.62  #Tautology    : 5980
% 21.19/12.62  #SimpNegUnit  : 330
% 21.19/12.62  #BackRed      : 224
% 21.19/12.62  
% 21.19/12.62  #Partial instantiations: 0
% 21.19/12.62  #Strategies tried      : 1
% 21.19/12.62  
% 21.19/12.62  Timing (in seconds)
% 21.19/12.62  ----------------------
% 21.19/12.63  Preprocessing        : 0.27
% 21.19/12.63  Parsing              : 0.15
% 21.19/12.63  CNF conversion       : 0.02
% 21.19/12.63  Main loop            : 11.58
% 21.19/12.63  Inferencing          : 1.59
% 21.19/12.63  Reduction            : 6.05
% 21.19/12.63  Demodulation         : 5.23
% 21.19/12.63  BG Simplification    : 0.19
% 21.19/12.63  Subsumption          : 3.16
% 21.19/12.63  Abstraction          : 0.31
% 21.19/12.63  MUC search           : 0.00
% 21.19/12.63  Cooper               : 0.00
% 21.19/12.63  Total                : 11.89
% 21.19/12.63  Index Insertion      : 0.00
% 21.19/12.63  Index Deletion       : 0.00
% 21.19/12.63  Index Matching       : 0.00
% 21.19/12.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
