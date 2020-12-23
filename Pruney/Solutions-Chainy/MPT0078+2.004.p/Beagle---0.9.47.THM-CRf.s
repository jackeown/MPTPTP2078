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
% DateTime   : Thu Dec  3 09:43:39 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 108 expanded)
%              Number of leaves         :   28 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :   63 ( 130 expanded)
%              Number of equality atoms :   38 (  79 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,B)
          & r1_xboole_0(A,B)
          & r1_xboole_0(C,B) )
       => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_36,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_80,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_72,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_60,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_62,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_66,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_70,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C] : k4_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,C),k4_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

tff(c_38,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_42,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_8,plain,(
    ! [A_5] :
      ( v1_xboole_0(A_5)
      | r2_hidden('#skF_1'(A_5),A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_341,plain,(
    ! [A_57,B_58,C_59] :
      ( ~ r1_xboole_0(A_57,B_58)
      | ~ r2_hidden(C_59,k3_xboole_0(A_57,B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_581,plain,(
    ! [A_74,B_75] :
      ( ~ r1_xboole_0(A_74,B_75)
      | v1_xboole_0(k3_xboole_0(A_74,B_75)) ) ),
    inference(resolution,[status(thm)],[c_8,c_341])).

tff(c_10,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_250,plain,(
    ! [B_44,A_45] :
      ( ~ v1_xboole_0(B_44)
      | B_44 = A_45
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_253,plain,(
    ! [A_45] :
      ( k1_xboole_0 = A_45
      | ~ v1_xboole_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_10,c_250])).

tff(c_799,plain,(
    ! [A_89,B_90] :
      ( k3_xboole_0(A_89,B_90) = k1_xboole_0
      | ~ r1_xboole_0(A_89,B_90) ) ),
    inference(resolution,[status(thm)],[c_581,c_253])).

tff(c_830,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_799])).

tff(c_34,plain,(
    ! [A_28,B_29] : k2_xboole_0(k3_xboole_0(A_28,B_29),k4_xboole_0(A_28,B_29)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_898,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_830,c_34])).

tff(c_72,plain,(
    ! [B_37,A_38] : k2_xboole_0(B_37,A_38) = k2_xboole_0(A_38,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_18] : k2_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_88,plain,(
    ! [A_38] : k2_xboole_0(k1_xboole_0,A_38) = A_38 ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_22])).

tff(c_1063,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_898,c_88])).

tff(c_24,plain,(
    ! [A_19] : k3_xboole_0(A_19,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_28,plain,(
    ! [A_22] : k4_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_272,plain,(
    ! [A_53,B_54] : k4_xboole_0(A_53,k4_xboole_0(A_53,B_54)) = k3_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_287,plain,(
    ! [A_22] : k4_xboole_0(A_22,A_22) = k3_xboole_0(A_22,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_272])).

tff(c_290,plain,(
    ! [A_22] : k4_xboole_0(A_22,A_22) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_287])).

tff(c_645,plain,(
    ! [A_79,C_80,B_81] : k2_xboole_0(k4_xboole_0(A_79,C_80),k4_xboole_0(B_81,C_80)) = k4_xboole_0(k2_xboole_0(A_79,B_81),C_80) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_674,plain,(
    ! [A_22,B_81] : k4_xboole_0(k2_xboole_0(A_22,B_81),A_22) = k2_xboole_0(k1_xboole_0,k4_xboole_0(B_81,A_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_645])).

tff(c_702,plain,(
    ! [A_22,B_81] : k4_xboole_0(k2_xboole_0(A_22,B_81),A_22) = k4_xboole_0(B_81,A_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_674])).

tff(c_40,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_829,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_799])).

tff(c_849,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_5','#skF_4')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_829,c_34])).

tff(c_1098,plain,(
    k4_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_849,c_88])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_44,plain,(
    k2_xboole_0('#skF_5','#skF_4') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_45,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_44])).

tff(c_1618,plain,(
    ! [A_105,B_106] : k4_xboole_0(k2_xboole_0(A_105,B_106),A_105) = k4_xboole_0(B_106,A_105) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_674])).

tff(c_1678,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_4') = k4_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_1618])).

tff(c_1707,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1063,c_702,c_1098,c_1678])).

tff(c_1709,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1707])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:22:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.60  
% 3.11/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.60  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.11/1.60  
% 3.11/1.60  %Foreground sorts:
% 3.11/1.60  
% 3.11/1.60  
% 3.11/1.60  %Background operators:
% 3.11/1.60  
% 3.11/1.60  
% 3.11/1.60  %Foreground operators:
% 3.11/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.11/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.11/1.60  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.11/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.11/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.11/1.60  tff('#skF_5', type, '#skF_5': $i).
% 3.11/1.60  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.11/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.11/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.11/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.60  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.11/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.11/1.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.11/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.11/1.60  
% 3.11/1.61  tff(f_89, negated_conjecture, ~(![A, B, C]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, B)) & r1_xboole_0(A, B)) & r1_xboole_0(C, B)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_xboole_1)).
% 3.11/1.61  tff(f_35, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.11/1.61  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.11/1.61  tff(f_36, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.11/1.61  tff(f_80, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 3.11/1.61  tff(f_72, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.11/1.61  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.11/1.61  tff(f_60, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.11/1.61  tff(f_62, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.11/1.61  tff(f_66, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.11/1.61  tff(f_70, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.11/1.61  tff(f_68, axiom, (![A, B, C]: (k4_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 3.11/1.61  tff(c_38, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.11/1.61  tff(c_42, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.11/1.61  tff(c_8, plain, (![A_5]: (v1_xboole_0(A_5) | r2_hidden('#skF_1'(A_5), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.11/1.61  tff(c_341, plain, (![A_57, B_58, C_59]: (~r1_xboole_0(A_57, B_58) | ~r2_hidden(C_59, k3_xboole_0(A_57, B_58)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.11/1.61  tff(c_581, plain, (![A_74, B_75]: (~r1_xboole_0(A_74, B_75) | v1_xboole_0(k3_xboole_0(A_74, B_75)))), inference(resolution, [status(thm)], [c_8, c_341])).
% 3.11/1.61  tff(c_10, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.11/1.61  tff(c_250, plain, (![B_44, A_45]: (~v1_xboole_0(B_44) | B_44=A_45 | ~v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.11/1.61  tff(c_253, plain, (![A_45]: (k1_xboole_0=A_45 | ~v1_xboole_0(A_45))), inference(resolution, [status(thm)], [c_10, c_250])).
% 3.11/1.61  tff(c_799, plain, (![A_89, B_90]: (k3_xboole_0(A_89, B_90)=k1_xboole_0 | ~r1_xboole_0(A_89, B_90))), inference(resolution, [status(thm)], [c_581, c_253])).
% 3.11/1.61  tff(c_830, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_799])).
% 3.11/1.61  tff(c_34, plain, (![A_28, B_29]: (k2_xboole_0(k3_xboole_0(A_28, B_29), k4_xboole_0(A_28, B_29))=A_28)), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.11/1.61  tff(c_898, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_830, c_34])).
% 3.11/1.61  tff(c_72, plain, (![B_37, A_38]: (k2_xboole_0(B_37, A_38)=k2_xboole_0(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.11/1.61  tff(c_22, plain, (![A_18]: (k2_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.11/1.61  tff(c_88, plain, (![A_38]: (k2_xboole_0(k1_xboole_0, A_38)=A_38)), inference(superposition, [status(thm), theory('equality')], [c_72, c_22])).
% 3.11/1.61  tff(c_1063, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_898, c_88])).
% 3.11/1.61  tff(c_24, plain, (![A_19]: (k3_xboole_0(A_19, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.11/1.61  tff(c_28, plain, (![A_22]: (k4_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.11/1.61  tff(c_272, plain, (![A_53, B_54]: (k4_xboole_0(A_53, k4_xboole_0(A_53, B_54))=k3_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.11/1.61  tff(c_287, plain, (![A_22]: (k4_xboole_0(A_22, A_22)=k3_xboole_0(A_22, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_272])).
% 3.11/1.61  tff(c_290, plain, (![A_22]: (k4_xboole_0(A_22, A_22)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_287])).
% 3.11/1.61  tff(c_645, plain, (![A_79, C_80, B_81]: (k2_xboole_0(k4_xboole_0(A_79, C_80), k4_xboole_0(B_81, C_80))=k4_xboole_0(k2_xboole_0(A_79, B_81), C_80))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.11/1.61  tff(c_674, plain, (![A_22, B_81]: (k4_xboole_0(k2_xboole_0(A_22, B_81), A_22)=k2_xboole_0(k1_xboole_0, k4_xboole_0(B_81, A_22)))), inference(superposition, [status(thm), theory('equality')], [c_290, c_645])).
% 3.11/1.61  tff(c_702, plain, (![A_22, B_81]: (k4_xboole_0(k2_xboole_0(A_22, B_81), A_22)=k4_xboole_0(B_81, A_22))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_674])).
% 3.11/1.61  tff(c_40, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.11/1.61  tff(c_829, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_799])).
% 3.11/1.61  tff(c_849, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_5', '#skF_4'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_829, c_34])).
% 3.11/1.61  tff(c_1098, plain, (k4_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_849, c_88])).
% 3.11/1.61  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.11/1.61  tff(c_44, plain, (k2_xboole_0('#skF_5', '#skF_4')=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.11/1.61  tff(c_45, plain, (k2_xboole_0('#skF_4', '#skF_5')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_44])).
% 3.11/1.61  tff(c_1618, plain, (![A_105, B_106]: (k4_xboole_0(k2_xboole_0(A_105, B_106), A_105)=k4_xboole_0(B_106, A_105))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_674])).
% 3.11/1.61  tff(c_1678, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_4')=k4_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_45, c_1618])).
% 3.11/1.61  tff(c_1707, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1063, c_702, c_1098, c_1678])).
% 3.11/1.61  tff(c_1709, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_1707])).
% 3.11/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.61  
% 3.11/1.61  Inference rules
% 3.11/1.61  ----------------------
% 3.11/1.61  #Ref     : 0
% 3.11/1.61  #Sup     : 412
% 3.11/1.61  #Fact    : 0
% 3.11/1.61  #Define  : 0
% 3.11/1.61  #Split   : 4
% 3.11/1.61  #Chain   : 0
% 3.11/1.61  #Close   : 0
% 3.11/1.61  
% 3.11/1.61  Ordering : KBO
% 3.11/1.61  
% 3.11/1.61  Simplification rules
% 3.11/1.61  ----------------------
% 3.11/1.61  #Subsume      : 34
% 3.11/1.61  #Demod        : 334
% 3.11/1.61  #Tautology    : 260
% 3.11/1.61  #SimpNegUnit  : 7
% 3.11/1.61  #BackRed      : 5
% 3.11/1.61  
% 3.11/1.61  #Partial instantiations: 0
% 3.11/1.61  #Strategies tried      : 1
% 3.11/1.61  
% 3.11/1.61  Timing (in seconds)
% 3.11/1.61  ----------------------
% 3.11/1.61  Preprocessing        : 0.33
% 3.11/1.61  Parsing              : 0.18
% 3.11/1.61  CNF conversion       : 0.02
% 3.11/1.61  Main loop            : 0.47
% 3.11/1.61  Inferencing          : 0.16
% 3.11/1.61  Reduction            : 0.19
% 3.11/1.62  Demodulation         : 0.15
% 3.11/1.62  BG Simplification    : 0.02
% 3.11/1.62  Subsumption          : 0.06
% 3.11/1.62  Abstraction          : 0.02
% 3.11/1.62  MUC search           : 0.00
% 3.11/1.62  Cooper               : 0.00
% 3.11/1.62  Total                : 0.83
% 3.11/1.62  Index Insertion      : 0.00
% 3.11/1.62  Index Deletion       : 0.00
% 3.11/1.62  Index Matching       : 0.00
% 3.11/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
