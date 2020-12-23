%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:51 EST 2020

% Result     : Theorem 4.28s
% Output     : CNFRefutation 4.28s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 161 expanded)
%              Number of leaves         :   29 (  64 expanded)
%              Depth                    :   18
%              Number of atoms          :   82 ( 198 expanded)
%              Number of equality atoms :   47 ( 117 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_62,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_72,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_66,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_38,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_24,plain,(
    ! [A_20] : k4_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_34,plain,(
    ! [A_30] : r1_xboole_0(A_30,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_254,plain,(
    ! [A_50,B_51] :
      ( k3_xboole_0(A_50,B_51) = k1_xboole_0
      | ~ r1_xboole_0(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_265,plain,(
    ! [A_30] : k3_xboole_0(A_30,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_254])).

tff(c_279,plain,(
    ! [A_55,B_56] : k4_xboole_0(A_55,k4_xboole_0(A_55,B_56)) = k3_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_294,plain,(
    ! [A_20] : k4_xboole_0(A_20,A_20) = k3_xboole_0(A_20,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_279])).

tff(c_340,plain,(
    ! [A_59] : k4_xboole_0(A_59,A_59) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_294])).

tff(c_30,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_345,plain,(
    ! [A_59] : k4_xboole_0(A_59,k1_xboole_0) = k3_xboole_0(A_59,A_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_340,c_30])).

tff(c_357,plain,(
    ! [A_59] : k3_xboole_0(A_59,A_59) = A_59 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_345])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_xboole_0(A_8,B_9)
      | k3_xboole_0(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_458,plain,(
    ! [A_63,B_64,C_65] :
      ( ~ r1_xboole_0(A_63,B_64)
      | ~ r2_hidden(C_65,k3_xboole_0(A_63,B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_497,plain,(
    ! [A_69,C_70] :
      ( ~ r1_xboole_0(A_69,A_69)
      | ~ r2_hidden(C_70,A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_458])).

tff(c_500,plain,(
    ! [C_70,B_9] :
      ( ~ r2_hidden(C_70,B_9)
      | k3_xboole_0(B_9,B_9) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_497])).

tff(c_509,plain,(
    ! [C_71,B_72] :
      ( ~ r2_hidden(C_71,B_72)
      | k1_xboole_0 != B_72 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_500])).

tff(c_521,plain,(
    ! [A_73,B_74] :
      ( k1_xboole_0 != A_73
      | r1_tarski(A_73,B_74) ) ),
    inference(resolution,[status(thm)],[c_8,c_509])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( k2_xboole_0(A_15,B_16) = B_16
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_585,plain,(
    ! [A_77,B_78] :
      ( k2_xboole_0(A_77,B_78) = B_78
      | k1_xboole_0 != A_77 ) ),
    inference(resolution,[status(thm)],[c_521,c_18])).

tff(c_665,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_585])).

tff(c_40,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_266,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_254])).

tff(c_744,plain,(
    ! [A_81,B_82] : k2_xboole_0(k3_xboole_0(A_81,B_82),k4_xboole_0(A_81,B_82)) = A_81 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_798,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_5')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_744])).

tff(c_528,plain,(
    ! [A_73,B_74] :
      ( k2_xboole_0(A_73,B_74) = B_74
      | k1_xboole_0 != A_73 ) ),
    inference(resolution,[status(thm)],[c_521,c_18])).

tff(c_894,plain,(
    k4_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_798,c_528])).

tff(c_1280,plain,(
    ! [A_100,B_101,C_102] : k4_xboole_0(k4_xboole_0(A_100,B_101),C_102) = k4_xboole_0(A_100,k2_xboole_0(B_101,C_102)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2705,plain,(
    ! [C_132] : k4_xboole_0('#skF_3',k2_xboole_0('#skF_5',C_132)) = k4_xboole_0('#skF_3',C_132) ),
    inference(superposition,[status(thm),theory(equality)],[c_894,c_1280])).

tff(c_3934,plain,(
    ! [B_155] : k4_xboole_0('#skF_3',k2_xboole_0(B_155,'#skF_5')) = k4_xboole_0('#skF_3',B_155) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2705])).

tff(c_297,plain,(
    ! [A_20] : k4_xboole_0(A_20,A_20) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_294])).

tff(c_42,plain,(
    r1_tarski('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_120,plain,(
    ! [A_41,B_42] :
      ( k2_xboole_0(A_41,B_42) = B_42
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_130,plain,(
    k2_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) = k2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_120])).

tff(c_298,plain,(
    ! [A_57,B_58] : k4_xboole_0(k2_xboole_0(A_57,B_58),B_58) = k4_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_314,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_5'),k2_xboole_0('#skF_4','#skF_5')) = k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_298])).

tff(c_418,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_314])).

tff(c_3982,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3934,c_418])).

tff(c_22,plain,(
    ! [A_18,B_19] : k2_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4092,plain,(
    k2_xboole_0('#skF_4',k1_xboole_0) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3982,c_22])).

tff(c_4114,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_665,c_4092])).

tff(c_67,plain,(
    ! [B_39,A_40] : k2_xboole_0(B_39,A_40) = k2_xboole_0(A_40,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    ! [A_31,B_32] : r1_tarski(A_31,k2_xboole_0(A_31,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_85,plain,(
    ! [B_39,A_40] : r1_tarski(B_39,k2_xboole_0(A_40,B_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_36])).

tff(c_4155,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4114,c_85])).

tff(c_4175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_4155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:31:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.28/1.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.28/1.70  
% 4.28/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.28/1.71  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.28/1.71  
% 4.28/1.71  %Foreground sorts:
% 4.28/1.71  
% 4.28/1.71  
% 4.28/1.71  %Background operators:
% 4.28/1.71  
% 4.28/1.71  
% 4.28/1.71  %Foreground operators:
% 4.28/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.28/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.28/1.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.28/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.28/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.28/1.71  tff('#skF_5', type, '#skF_5': $i).
% 4.28/1.71  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.28/1.71  tff('#skF_3', type, '#skF_3': $i).
% 4.28/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.28/1.71  tff('#skF_4', type, '#skF_4': $i).
% 4.28/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.28/1.71  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.28/1.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.28/1.71  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.28/1.71  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.28/1.71  
% 4.28/1.72  tff(f_81, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 4.28/1.72  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.28/1.72  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.28/1.72  tff(f_62, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.28/1.72  tff(f_72, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.28/1.72  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.28/1.72  tff(f_68, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.28/1.72  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.28/1.72  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.28/1.72  tff(f_70, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 4.28/1.72  tff(f_66, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.28/1.72  tff(f_64, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 4.28/1.72  tff(f_60, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.28/1.72  tff(f_74, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.28/1.72  tff(c_38, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.28/1.72  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.28/1.72  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.28/1.72  tff(c_24, plain, (![A_20]: (k4_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.28/1.72  tff(c_34, plain, (![A_30]: (r1_xboole_0(A_30, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.28/1.72  tff(c_254, plain, (![A_50, B_51]: (k3_xboole_0(A_50, B_51)=k1_xboole_0 | ~r1_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.28/1.72  tff(c_265, plain, (![A_30]: (k3_xboole_0(A_30, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_254])).
% 4.28/1.72  tff(c_279, plain, (![A_55, B_56]: (k4_xboole_0(A_55, k4_xboole_0(A_55, B_56))=k3_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.28/1.72  tff(c_294, plain, (![A_20]: (k4_xboole_0(A_20, A_20)=k3_xboole_0(A_20, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_279])).
% 4.28/1.72  tff(c_340, plain, (![A_59]: (k4_xboole_0(A_59, A_59)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_265, c_294])).
% 4.28/1.72  tff(c_30, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.28/1.72  tff(c_345, plain, (![A_59]: (k4_xboole_0(A_59, k1_xboole_0)=k3_xboole_0(A_59, A_59))), inference(superposition, [status(thm), theory('equality')], [c_340, c_30])).
% 4.28/1.72  tff(c_357, plain, (![A_59]: (k3_xboole_0(A_59, A_59)=A_59)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_345])).
% 4.28/1.72  tff(c_12, plain, (![A_8, B_9]: (r1_xboole_0(A_8, B_9) | k3_xboole_0(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.28/1.72  tff(c_458, plain, (![A_63, B_64, C_65]: (~r1_xboole_0(A_63, B_64) | ~r2_hidden(C_65, k3_xboole_0(A_63, B_64)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.28/1.72  tff(c_497, plain, (![A_69, C_70]: (~r1_xboole_0(A_69, A_69) | ~r2_hidden(C_70, A_69))), inference(superposition, [status(thm), theory('equality')], [c_357, c_458])).
% 4.28/1.72  tff(c_500, plain, (![C_70, B_9]: (~r2_hidden(C_70, B_9) | k3_xboole_0(B_9, B_9)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_497])).
% 4.28/1.72  tff(c_509, plain, (![C_71, B_72]: (~r2_hidden(C_71, B_72) | k1_xboole_0!=B_72)), inference(demodulation, [status(thm), theory('equality')], [c_357, c_500])).
% 4.28/1.72  tff(c_521, plain, (![A_73, B_74]: (k1_xboole_0!=A_73 | r1_tarski(A_73, B_74))), inference(resolution, [status(thm)], [c_8, c_509])).
% 4.28/1.72  tff(c_18, plain, (![A_15, B_16]: (k2_xboole_0(A_15, B_16)=B_16 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.28/1.72  tff(c_585, plain, (![A_77, B_78]: (k2_xboole_0(A_77, B_78)=B_78 | k1_xboole_0!=A_77)), inference(resolution, [status(thm)], [c_521, c_18])).
% 4.28/1.72  tff(c_665, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_585])).
% 4.28/1.72  tff(c_40, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.28/1.72  tff(c_266, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_254])).
% 4.28/1.72  tff(c_744, plain, (![A_81, B_82]: (k2_xboole_0(k3_xboole_0(A_81, B_82), k4_xboole_0(A_81, B_82))=A_81)), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.28/1.72  tff(c_798, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_5'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_266, c_744])).
% 4.28/1.72  tff(c_528, plain, (![A_73, B_74]: (k2_xboole_0(A_73, B_74)=B_74 | k1_xboole_0!=A_73)), inference(resolution, [status(thm)], [c_521, c_18])).
% 4.28/1.72  tff(c_894, plain, (k4_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_798, c_528])).
% 4.28/1.72  tff(c_1280, plain, (![A_100, B_101, C_102]: (k4_xboole_0(k4_xboole_0(A_100, B_101), C_102)=k4_xboole_0(A_100, k2_xboole_0(B_101, C_102)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.28/1.72  tff(c_2705, plain, (![C_132]: (k4_xboole_0('#skF_3', k2_xboole_0('#skF_5', C_132))=k4_xboole_0('#skF_3', C_132))), inference(superposition, [status(thm), theory('equality')], [c_894, c_1280])).
% 4.28/1.72  tff(c_3934, plain, (![B_155]: (k4_xboole_0('#skF_3', k2_xboole_0(B_155, '#skF_5'))=k4_xboole_0('#skF_3', B_155))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2705])).
% 4.28/1.72  tff(c_297, plain, (![A_20]: (k4_xboole_0(A_20, A_20)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_265, c_294])).
% 4.28/1.72  tff(c_42, plain, (r1_tarski('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.28/1.72  tff(c_120, plain, (![A_41, B_42]: (k2_xboole_0(A_41, B_42)=B_42 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.28/1.72  tff(c_130, plain, (k2_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))=k2_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_120])).
% 4.28/1.72  tff(c_298, plain, (![A_57, B_58]: (k4_xboole_0(k2_xboole_0(A_57, B_58), B_58)=k4_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.28/1.72  tff(c_314, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_5'), k2_xboole_0('#skF_4', '#skF_5'))=k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_130, c_298])).
% 4.28/1.72  tff(c_418, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_297, c_314])).
% 4.28/1.72  tff(c_3982, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3934, c_418])).
% 4.28/1.72  tff(c_22, plain, (![A_18, B_19]: (k2_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.28/1.72  tff(c_4092, plain, (k2_xboole_0('#skF_4', k1_xboole_0)=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3982, c_22])).
% 4.28/1.72  tff(c_4114, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_665, c_4092])).
% 4.28/1.72  tff(c_67, plain, (![B_39, A_40]: (k2_xboole_0(B_39, A_40)=k2_xboole_0(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.28/1.72  tff(c_36, plain, (![A_31, B_32]: (r1_tarski(A_31, k2_xboole_0(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.28/1.72  tff(c_85, plain, (![B_39, A_40]: (r1_tarski(B_39, k2_xboole_0(A_40, B_39)))), inference(superposition, [status(thm), theory('equality')], [c_67, c_36])).
% 4.28/1.72  tff(c_4155, plain, (r1_tarski('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4114, c_85])).
% 4.28/1.72  tff(c_4175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_4155])).
% 4.28/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.28/1.72  
% 4.28/1.72  Inference rules
% 4.28/1.72  ----------------------
% 4.28/1.72  #Ref     : 1
% 4.28/1.72  #Sup     : 1030
% 4.28/1.72  #Fact    : 0
% 4.28/1.72  #Define  : 0
% 4.28/1.72  #Split   : 2
% 4.28/1.72  #Chain   : 0
% 4.28/1.72  #Close   : 0
% 4.28/1.72  
% 4.28/1.72  Ordering : KBO
% 4.28/1.72  
% 4.28/1.72  Simplification rules
% 4.28/1.72  ----------------------
% 4.28/1.72  #Subsume      : 204
% 4.28/1.72  #Demod        : 601
% 4.28/1.72  #Tautology    : 613
% 4.28/1.72  #SimpNegUnit  : 58
% 4.28/1.72  #BackRed      : 1
% 4.28/1.72  
% 4.28/1.72  #Partial instantiations: 0
% 4.28/1.72  #Strategies tried      : 1
% 4.28/1.72  
% 4.28/1.72  Timing (in seconds)
% 4.28/1.72  ----------------------
% 4.28/1.72  Preprocessing        : 0.28
% 4.28/1.72  Parsing              : 0.15
% 4.28/1.72  CNF conversion       : 0.02
% 4.28/1.72  Main loop            : 0.70
% 4.28/1.72  Inferencing          : 0.22
% 4.28/1.72  Reduction            : 0.30
% 4.28/1.72  Demodulation         : 0.24
% 4.28/1.72  BG Simplification    : 0.02
% 4.28/1.72  Subsumption          : 0.11
% 4.28/1.72  Abstraction          : 0.03
% 4.28/1.72  MUC search           : 0.00
% 4.28/1.72  Cooper               : 0.00
% 4.28/1.72  Total                : 1.01
% 4.28/1.72  Index Insertion      : 0.00
% 4.28/1.72  Index Deletion       : 0.00
% 4.28/1.72  Index Matching       : 0.00
% 4.28/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
