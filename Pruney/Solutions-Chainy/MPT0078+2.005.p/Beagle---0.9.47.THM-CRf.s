%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:39 EST 2020

% Result     : Theorem 4.43s
% Output     : CNFRefutation 4.43s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 143 expanded)
%              Number of leaves         :   30 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :   82 ( 169 expanded)
%              Number of equality atoms :   57 ( 116 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,B)
          & r1_xboole_0(A,B)
          & r1_xboole_0(C,B) )
       => A = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_36,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_66,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_52,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_54,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_58,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_64,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] : k4_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,C),k4_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_34,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_38,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_8,plain,(
    ! [A_5] :
      ( v1_xboole_0(A_5)
      | r2_hidden('#skF_1'(A_5),A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_426,plain,(
    ! [A_54,B_55,C_56] :
      ( ~ r1_xboole_0(A_54,B_55)
      | ~ r2_hidden(C_56,k3_xboole_0(A_54,B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_521,plain,(
    ! [A_63,B_64] :
      ( ~ r1_xboole_0(A_63,B_64)
      | v1_xboole_0(k3_xboole_0(A_63,B_64)) ) ),
    inference(resolution,[status(thm)],[c_8,c_426])).

tff(c_10,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_159,plain,(
    ! [B_39,A_40] :
      ( ~ v1_xboole_0(B_39)
      | B_39 = A_40
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_162,plain,(
    ! [A_40] :
      ( k1_xboole_0 = A_40
      | ~ v1_xboole_0(A_40) ) ),
    inference(resolution,[status(thm)],[c_10,c_159])).

tff(c_1819,plain,(
    ! [A_108,B_109] :
      ( k3_xboole_0(A_108,B_109) = k1_xboole_0
      | ~ r1_xboole_0(A_108,B_109) ) ),
    inference(resolution,[status(thm)],[c_521,c_162])).

tff(c_1850,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_1819])).

tff(c_30,plain,(
    ! [A_27,B_28] : k2_xboole_0(k3_xboole_0(A_27,B_28),k4_xboole_0(A_27,B_28)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1955,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1850,c_30])).

tff(c_72,plain,(
    ! [B_36,A_37] : k2_xboole_0(B_36,A_37) = k2_xboole_0(A_37,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_88,plain,(
    ! [A_37] : k2_xboole_0(k1_xboole_0,A_37) = A_37 ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_16])).

tff(c_2123,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1955,c_88])).

tff(c_18,plain,(
    ! [A_15] : k3_xboole_0(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_22,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_324,plain,(
    ! [A_50,B_51] : k4_xboole_0(A_50,k4_xboole_0(A_50,B_51)) = k3_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_353,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k3_xboole_0(A_18,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_324])).

tff(c_359,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_353])).

tff(c_1040,plain,(
    ! [A_88,C_89,B_90] : k2_xboole_0(k4_xboole_0(A_88,C_89),k4_xboole_0(B_90,C_89)) = k4_xboole_0(k2_xboole_0(A_88,B_90),C_89) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1096,plain,(
    ! [A_18,B_90] : k4_xboole_0(k2_xboole_0(A_18,B_90),A_18) = k2_xboole_0(k1_xboole_0,k4_xboole_0(B_90,A_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_1040])).

tff(c_3458,plain,(
    ! [A_138,B_139] : k4_xboole_0(k2_xboole_0(A_138,B_139),A_138) = k4_xboole_0(B_139,A_138) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1096])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    k2_xboole_0('#skF_5','#skF_4') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_41,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_40])).

tff(c_20,plain,(
    ! [A_16,B_17] : k2_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_658,plain,(
    ! [A_75,B_76,C_77] : k4_xboole_0(k4_xboole_0(A_75,B_76),C_77) = k4_xboole_0(A_75,k2_xboole_0(B_76,C_77)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_671,plain,(
    ! [A_75,B_76] : k4_xboole_0(A_75,k2_xboole_0(B_76,k4_xboole_0(A_75,B_76))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_658,c_359])).

tff(c_729,plain,(
    ! [A_78,B_79] : k4_xboole_0(A_78,k2_xboole_0(B_79,A_78)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_671])).

tff(c_780,plain,(
    k4_xboole_0('#skF_5',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_729])).

tff(c_28,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1158,plain,(
    k3_xboole_0('#skF_5',k2_xboole_0('#skF_4','#skF_3')) = k4_xboole_0('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_780,c_28])).

tff(c_1169,plain,(
    k3_xboole_0('#skF_5',k2_xboole_0('#skF_4','#skF_3')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1158])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_36,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1849,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_1819])).

tff(c_257,plain,(
    ! [A_46,B_47] : k2_xboole_0(k3_xboole_0(A_46,B_47),k4_xboole_0(A_46,B_47)) = A_46 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_269,plain,(
    ! [B_4,A_3] : k2_xboole_0(k3_xboole_0(B_4,A_3),k4_xboole_0(A_3,B_4)) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_257])).

tff(c_1866,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_4','#skF_5')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1849,c_269])).

tff(c_2255,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1866,c_88])).

tff(c_1099,plain,(
    ! [A_88,A_18] : k4_xboole_0(k2_xboole_0(A_88,A_18),A_18) = k2_xboole_0(k4_xboole_0(A_88,A_18),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_1040])).

tff(c_3265,plain,(
    ! [A_136,A_137] : k4_xboole_0(k2_xboole_0(A_136,A_137),A_137) = k4_xboole_0(A_136,A_137) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1099])).

tff(c_3344,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_5') = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_3265])).

tff(c_3372,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2255,c_3344])).

tff(c_3402,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_4') = k3_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3372,c_28])).

tff(c_3413,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1169,c_4,c_3402])).

tff(c_3464,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_3458,c_3413])).

tff(c_3560,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2123,c_3464])).

tff(c_3562,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_3560])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:06:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.43/1.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.43/1.90  
% 4.43/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.43/1.91  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 4.43/1.91  
% 4.43/1.91  %Foreground sorts:
% 4.43/1.91  
% 4.43/1.91  
% 4.43/1.91  %Background operators:
% 4.43/1.91  
% 4.43/1.91  
% 4.43/1.91  %Foreground operators:
% 4.43/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.43/1.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.43/1.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.43/1.91  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.43/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.43/1.91  tff('#skF_5', type, '#skF_5': $i).
% 4.43/1.91  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.43/1.91  tff('#skF_3', type, '#skF_3': $i).
% 4.43/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.43/1.91  tff('#skF_4', type, '#skF_4': $i).
% 4.43/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.43/1.91  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.43/1.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.43/1.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.43/1.91  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.43/1.91  
% 4.43/1.92  tff(f_83, negated_conjecture, ~(![A, B, C]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, B)) & r1_xboole_0(A, B)) & r1_xboole_0(C, B)) => (A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_xboole_1)).
% 4.43/1.92  tff(f_35, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.43/1.92  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.43/1.92  tff(f_36, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.43/1.92  tff(f_74, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 4.43/1.92  tff(f_66, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 4.43/1.92  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.43/1.92  tff(f_52, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.43/1.92  tff(f_54, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.43/1.92  tff(f_58, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.43/1.92  tff(f_64, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.43/1.92  tff(f_62, axiom, (![A, B, C]: (k4_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_xboole_1)).
% 4.43/1.92  tff(f_56, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.43/1.92  tff(f_60, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.43/1.92  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.43/1.92  tff(c_34, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.43/1.92  tff(c_38, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.43/1.92  tff(c_8, plain, (![A_5]: (v1_xboole_0(A_5) | r2_hidden('#skF_1'(A_5), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.43/1.92  tff(c_426, plain, (![A_54, B_55, C_56]: (~r1_xboole_0(A_54, B_55) | ~r2_hidden(C_56, k3_xboole_0(A_54, B_55)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.43/1.92  tff(c_521, plain, (![A_63, B_64]: (~r1_xboole_0(A_63, B_64) | v1_xboole_0(k3_xboole_0(A_63, B_64)))), inference(resolution, [status(thm)], [c_8, c_426])).
% 4.43/1.92  tff(c_10, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.43/1.92  tff(c_159, plain, (![B_39, A_40]: (~v1_xboole_0(B_39) | B_39=A_40 | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.43/1.92  tff(c_162, plain, (![A_40]: (k1_xboole_0=A_40 | ~v1_xboole_0(A_40))), inference(resolution, [status(thm)], [c_10, c_159])).
% 4.43/1.92  tff(c_1819, plain, (![A_108, B_109]: (k3_xboole_0(A_108, B_109)=k1_xboole_0 | ~r1_xboole_0(A_108, B_109))), inference(resolution, [status(thm)], [c_521, c_162])).
% 4.43/1.92  tff(c_1850, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_1819])).
% 4.43/1.92  tff(c_30, plain, (![A_27, B_28]: (k2_xboole_0(k3_xboole_0(A_27, B_28), k4_xboole_0(A_27, B_28))=A_27)), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.43/1.92  tff(c_1955, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1850, c_30])).
% 4.43/1.92  tff(c_72, plain, (![B_36, A_37]: (k2_xboole_0(B_36, A_37)=k2_xboole_0(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.43/1.92  tff(c_16, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.43/1.92  tff(c_88, plain, (![A_37]: (k2_xboole_0(k1_xboole_0, A_37)=A_37)), inference(superposition, [status(thm), theory('equality')], [c_72, c_16])).
% 4.43/1.92  tff(c_2123, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1955, c_88])).
% 4.43/1.92  tff(c_18, plain, (![A_15]: (k3_xboole_0(A_15, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.43/1.92  tff(c_22, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.43/1.92  tff(c_324, plain, (![A_50, B_51]: (k4_xboole_0(A_50, k4_xboole_0(A_50, B_51))=k3_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.43/1.92  tff(c_353, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k3_xboole_0(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_324])).
% 4.43/1.92  tff(c_359, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_353])).
% 4.43/1.92  tff(c_1040, plain, (![A_88, C_89, B_90]: (k2_xboole_0(k4_xboole_0(A_88, C_89), k4_xboole_0(B_90, C_89))=k4_xboole_0(k2_xboole_0(A_88, B_90), C_89))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.43/1.92  tff(c_1096, plain, (![A_18, B_90]: (k4_xboole_0(k2_xboole_0(A_18, B_90), A_18)=k2_xboole_0(k1_xboole_0, k4_xboole_0(B_90, A_18)))), inference(superposition, [status(thm), theory('equality')], [c_359, c_1040])).
% 4.43/1.92  tff(c_3458, plain, (![A_138, B_139]: (k4_xboole_0(k2_xboole_0(A_138, B_139), A_138)=k4_xboole_0(B_139, A_138))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1096])).
% 4.43/1.92  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.43/1.92  tff(c_40, plain, (k2_xboole_0('#skF_5', '#skF_4')=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.43/1.92  tff(c_41, plain, (k2_xboole_0('#skF_4', '#skF_5')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_40])).
% 4.43/1.92  tff(c_20, plain, (![A_16, B_17]: (k2_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.43/1.92  tff(c_658, plain, (![A_75, B_76, C_77]: (k4_xboole_0(k4_xboole_0(A_75, B_76), C_77)=k4_xboole_0(A_75, k2_xboole_0(B_76, C_77)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.43/1.92  tff(c_671, plain, (![A_75, B_76]: (k4_xboole_0(A_75, k2_xboole_0(B_76, k4_xboole_0(A_75, B_76)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_658, c_359])).
% 4.43/1.92  tff(c_729, plain, (![A_78, B_79]: (k4_xboole_0(A_78, k2_xboole_0(B_79, A_78))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_671])).
% 4.43/1.92  tff(c_780, plain, (k4_xboole_0('#skF_5', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_41, c_729])).
% 4.43/1.92  tff(c_28, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.43/1.92  tff(c_1158, plain, (k3_xboole_0('#skF_5', k2_xboole_0('#skF_4', '#skF_3'))=k4_xboole_0('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_780, c_28])).
% 4.43/1.92  tff(c_1169, plain, (k3_xboole_0('#skF_5', k2_xboole_0('#skF_4', '#skF_3'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1158])).
% 4.43/1.92  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.43/1.92  tff(c_36, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.43/1.92  tff(c_1849, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_1819])).
% 4.43/1.92  tff(c_257, plain, (![A_46, B_47]: (k2_xboole_0(k3_xboole_0(A_46, B_47), k4_xboole_0(A_46, B_47))=A_46)), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.43/1.92  tff(c_269, plain, (![B_4, A_3]: (k2_xboole_0(k3_xboole_0(B_4, A_3), k4_xboole_0(A_3, B_4))=A_3)), inference(superposition, [status(thm), theory('equality')], [c_4, c_257])).
% 4.43/1.92  tff(c_1866, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_4', '#skF_5'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1849, c_269])).
% 4.43/1.92  tff(c_2255, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1866, c_88])).
% 4.43/1.92  tff(c_1099, plain, (![A_88, A_18]: (k4_xboole_0(k2_xboole_0(A_88, A_18), A_18)=k2_xboole_0(k4_xboole_0(A_88, A_18), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_359, c_1040])).
% 4.43/1.92  tff(c_3265, plain, (![A_136, A_137]: (k4_xboole_0(k2_xboole_0(A_136, A_137), A_137)=k4_xboole_0(A_136, A_137))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1099])).
% 4.43/1.92  tff(c_3344, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_5')=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_41, c_3265])).
% 4.43/1.92  tff(c_3372, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2255, c_3344])).
% 4.43/1.92  tff(c_3402, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_4')=k3_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3372, c_28])).
% 4.43/1.92  tff(c_3413, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1169, c_4, c_3402])).
% 4.43/1.92  tff(c_3464, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_3458, c_3413])).
% 4.43/1.92  tff(c_3560, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2123, c_3464])).
% 4.43/1.92  tff(c_3562, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_3560])).
% 4.43/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.43/1.92  
% 4.43/1.92  Inference rules
% 4.43/1.92  ----------------------
% 4.43/1.92  #Ref     : 0
% 4.43/1.92  #Sup     : 914
% 4.43/1.92  #Fact    : 0
% 4.43/1.92  #Define  : 0
% 4.43/1.92  #Split   : 2
% 4.43/1.92  #Chain   : 0
% 4.43/1.92  #Close   : 0
% 4.43/1.92  
% 4.43/1.92  Ordering : KBO
% 4.43/1.92  
% 4.43/1.92  Simplification rules
% 4.43/1.92  ----------------------
% 4.43/1.92  #Subsume      : 108
% 4.43/1.92  #Demod        : 677
% 4.43/1.92  #Tautology    : 510
% 4.43/1.92  #SimpNegUnit  : 19
% 4.43/1.92  #BackRed      : 5
% 4.43/1.92  
% 4.43/1.92  #Partial instantiations: 0
% 4.43/1.92  #Strategies tried      : 1
% 4.43/1.92  
% 4.43/1.93  Timing (in seconds)
% 4.43/1.93  ----------------------
% 4.43/1.93  Preprocessing        : 0.32
% 4.43/1.93  Parsing              : 0.17
% 4.43/1.93  CNF conversion       : 0.02
% 4.43/1.93  Main loop            : 0.76
% 4.43/1.93  Inferencing          : 0.25
% 4.43/1.93  Reduction            : 0.32
% 4.43/1.93  Demodulation         : 0.26
% 4.43/1.93  BG Simplification    : 0.03
% 4.43/1.93  Subsumption          : 0.11
% 4.43/1.93  Abstraction          : 0.04
% 4.43/1.93  MUC search           : 0.00
% 4.43/1.93  Cooper               : 0.00
% 4.43/1.93  Total                : 1.12
% 4.43/1.93  Index Insertion      : 0.00
% 4.43/1.93  Index Deletion       : 0.00
% 4.43/1.93  Index Matching       : 0.00
% 4.43/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
