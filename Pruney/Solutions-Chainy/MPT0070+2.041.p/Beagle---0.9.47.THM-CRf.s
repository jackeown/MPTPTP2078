%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:23 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 126 expanded)
%              Number of leaves         :   27 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :   82 ( 181 expanded)
%              Number of equality atoms :   35 (  56 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_59,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_63,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_30,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_59,plain,(
    ! [B_28,A_29] :
      ( r1_xboole_0(B_28,A_29)
      | ~ r1_xboole_0(A_29,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_62,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_59])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_225,plain,(
    ! [A_43,B_44,C_45] :
      ( ~ r1_xboole_0(A_43,B_44)
      | ~ r2_hidden(C_45,k3_xboole_0(A_43,B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1693,plain,(
    ! [A_94,B_95] :
      ( ~ r1_xboole_0(A_94,B_95)
      | k3_xboole_0(A_94,B_95) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_225])).

tff(c_1700,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_62,c_1693])).

tff(c_6,plain,(
    ! [A_3,B_4,C_7] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r2_hidden(C_7,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1708,plain,(
    ! [C_7] :
      ( ~ r1_xboole_0('#skF_5','#skF_4')
      | ~ r2_hidden(C_7,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1700,c_6])).

tff(c_1716,plain,(
    ! [C_7] : ~ r2_hidden(C_7,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1708])).

tff(c_28,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_16,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_238,plain,(
    ! [A_13,C_45] :
      ( ~ r1_xboole_0(A_13,k1_xboole_0)
      | ~ r2_hidden(C_45,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_225])).

tff(c_240,plain,(
    ! [C_45] : ~ r2_hidden(C_45,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_238])).

tff(c_20,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_94,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k4_xboole_0(A_36,B_37)) = k3_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_115,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k3_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_94])).

tff(c_122,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_115])).

tff(c_640,plain,(
    ! [A_64,B_65] :
      ( ~ r1_xboole_0(A_64,B_65)
      | k3_xboole_0(A_64,B_65) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_225])).

tff(c_657,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_62,c_640])).

tff(c_24,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k3_xboole_0(A_20,B_21)) = k4_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_668,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) = k4_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_657,c_24])).

tff(c_675,plain,(
    k4_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_668])).

tff(c_14,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_68,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = k1_xboole_0
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_76,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_68])).

tff(c_144,plain,(
    ! [A_39,B_40] : k2_xboole_0(A_39,k4_xboole_0(B_40,A_39)) = k2_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_162,plain,(
    k2_xboole_0('#skF_4',k1_xboole_0) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_144])).

tff(c_169,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_162])).

tff(c_22,plain,(
    ! [A_17,B_18,C_19] : k4_xboole_0(k4_xboole_0(A_17,B_18),C_19) = k4_xboole_0(A_17,k2_xboole_0(B_18,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1205,plain,(
    ! [C_75] : k4_xboole_0('#skF_5',k2_xboole_0('#skF_4',C_75)) = k4_xboole_0('#skF_5',C_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_675,c_22])).

tff(c_1238,plain,(
    k4_xboole_0('#skF_5','#skF_3') = k4_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_1205])).

tff(c_1259,plain,(
    k4_xboole_0('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_675,c_1238])).

tff(c_26,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k4_xboole_0(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1275,plain,(
    k4_xboole_0('#skF_5','#skF_5') = k3_xboole_0('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1259,c_26])).

tff(c_1280,plain,(
    k3_xboole_0('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_1275])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),k3_xboole_0(A_3,B_4))
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1288,plain,
    ( r2_hidden('#skF_1'('#skF_5','#skF_3'),k1_xboole_0)
    | r1_xboole_0('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1280,c_4])).

tff(c_1298,plain,(
    r1_xboole_0('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_1288])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1305,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_1298,c_2])).

tff(c_1311,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_1305])).

tff(c_1312,plain,(
    ! [A_13] : ~ r1_xboole_0(A_13,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_238])).

tff(c_1620,plain,(
    ! [A_89,B_90] :
      ( r2_hidden('#skF_1'(A_89,B_90),k3_xboole_0(A_89,B_90))
      | r1_xboole_0(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1638,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_1'(A_13,k1_xboole_0),k1_xboole_0)
      | r1_xboole_0(A_13,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1620])).

tff(c_1640,plain,(
    ! [A_13] : r2_hidden('#skF_1'(A_13,k1_xboole_0),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_1312,c_1638])).

tff(c_1793,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1716,c_1640])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.10  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.09/0.29  % Computer   : n001.cluster.edu
% 0.09/0.29  % Model      : x86_64 x86_64
% 0.09/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.29  % Memory     : 8042.1875MB
% 0.09/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.29  % CPULimit   : 60
% 0.09/0.29  % DateTime   : Tue Dec  1 15:10:15 EST 2020
% 0.09/0.29  % CPUTime    : 
% 0.09/0.30  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.41  
% 2.91/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.41  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.91/1.41  
% 2.91/1.41  %Foreground sorts:
% 2.91/1.41  
% 2.91/1.41  
% 2.91/1.41  %Background operators:
% 2.91/1.41  
% 2.91/1.41  
% 2.91/1.41  %Foreground operators:
% 2.91/1.41  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.91/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.91/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.91/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.91/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.91/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.91/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.91/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.91/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.91/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.91/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.91/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.91/1.41  
% 2.91/1.42  tff(f_76, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.91/1.42  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.91/1.42  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.91/1.42  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.91/1.42  tff(f_59, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.91/1.42  tff(f_63, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.91/1.42  tff(f_69, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.91/1.42  tff(f_67, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.91/1.42  tff(f_57, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.91/1.42  tff(f_55, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.91/1.42  tff(f_61, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.91/1.42  tff(f_65, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.91/1.42  tff(c_30, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.91/1.42  tff(c_59, plain, (![B_28, A_29]: (r1_xboole_0(B_28, A_29) | ~r1_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.91/1.42  tff(c_62, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_59])).
% 2.91/1.42  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.91/1.42  tff(c_225, plain, (![A_43, B_44, C_45]: (~r1_xboole_0(A_43, B_44) | ~r2_hidden(C_45, k3_xboole_0(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.91/1.42  tff(c_1693, plain, (![A_94, B_95]: (~r1_xboole_0(A_94, B_95) | k3_xboole_0(A_94, B_95)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_225])).
% 2.91/1.42  tff(c_1700, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_62, c_1693])).
% 2.91/1.42  tff(c_6, plain, (![A_3, B_4, C_7]: (~r1_xboole_0(A_3, B_4) | ~r2_hidden(C_7, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.91/1.42  tff(c_1708, plain, (![C_7]: (~r1_xboole_0('#skF_5', '#skF_4') | ~r2_hidden(C_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1700, c_6])).
% 2.91/1.42  tff(c_1716, plain, (![C_7]: (~r2_hidden(C_7, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1708])).
% 2.91/1.42  tff(c_28, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.91/1.42  tff(c_16, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.91/1.42  tff(c_238, plain, (![A_13, C_45]: (~r1_xboole_0(A_13, k1_xboole_0) | ~r2_hidden(C_45, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_225])).
% 2.91/1.42  tff(c_240, plain, (![C_45]: (~r2_hidden(C_45, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_238])).
% 2.91/1.42  tff(c_20, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.91/1.42  tff(c_94, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k4_xboole_0(A_36, B_37))=k3_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.91/1.42  tff(c_115, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k3_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_94])).
% 2.91/1.42  tff(c_122, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_115])).
% 2.91/1.42  tff(c_640, plain, (![A_64, B_65]: (~r1_xboole_0(A_64, B_65) | k3_xboole_0(A_64, B_65)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_225])).
% 2.91/1.42  tff(c_657, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_62, c_640])).
% 2.91/1.42  tff(c_24, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k3_xboole_0(A_20, B_21))=k4_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.91/1.42  tff(c_668, plain, (k4_xboole_0('#skF_5', k1_xboole_0)=k4_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_657, c_24])).
% 2.91/1.42  tff(c_675, plain, (k4_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_668])).
% 2.91/1.42  tff(c_14, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.91/1.42  tff(c_32, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.91/1.42  tff(c_68, plain, (![A_32, B_33]: (k4_xboole_0(A_32, B_33)=k1_xboole_0 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.91/1.42  tff(c_76, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_68])).
% 2.91/1.42  tff(c_144, plain, (![A_39, B_40]: (k2_xboole_0(A_39, k4_xboole_0(B_40, A_39))=k2_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.91/1.42  tff(c_162, plain, (k2_xboole_0('#skF_4', k1_xboole_0)=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_76, c_144])).
% 2.91/1.42  tff(c_169, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_162])).
% 2.91/1.42  tff(c_22, plain, (![A_17, B_18, C_19]: (k4_xboole_0(k4_xboole_0(A_17, B_18), C_19)=k4_xboole_0(A_17, k2_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.91/1.42  tff(c_1205, plain, (![C_75]: (k4_xboole_0('#skF_5', k2_xboole_0('#skF_4', C_75))=k4_xboole_0('#skF_5', C_75))), inference(superposition, [status(thm), theory('equality')], [c_675, c_22])).
% 2.91/1.42  tff(c_1238, plain, (k4_xboole_0('#skF_5', '#skF_3')=k4_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_169, c_1205])).
% 2.91/1.42  tff(c_1259, plain, (k4_xboole_0('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_675, c_1238])).
% 2.91/1.42  tff(c_26, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k4_xboole_0(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.91/1.42  tff(c_1275, plain, (k4_xboole_0('#skF_5', '#skF_5')=k3_xboole_0('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1259, c_26])).
% 2.91/1.42  tff(c_1280, plain, (k3_xboole_0('#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_122, c_1275])).
% 2.91/1.42  tff(c_4, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), k3_xboole_0(A_3, B_4)) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.91/1.42  tff(c_1288, plain, (r2_hidden('#skF_1'('#skF_5', '#skF_3'), k1_xboole_0) | r1_xboole_0('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1280, c_4])).
% 2.91/1.42  tff(c_1298, plain, (r1_xboole_0('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_240, c_1288])).
% 2.91/1.42  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.91/1.42  tff(c_1305, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_1298, c_2])).
% 2.91/1.42  tff(c_1311, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_1305])).
% 2.91/1.42  tff(c_1312, plain, (![A_13]: (~r1_xboole_0(A_13, k1_xboole_0))), inference(splitRight, [status(thm)], [c_238])).
% 2.91/1.42  tff(c_1620, plain, (![A_89, B_90]: (r2_hidden('#skF_1'(A_89, B_90), k3_xboole_0(A_89, B_90)) | r1_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.91/1.42  tff(c_1638, plain, (![A_13]: (r2_hidden('#skF_1'(A_13, k1_xboole_0), k1_xboole_0) | r1_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1620])).
% 2.91/1.42  tff(c_1640, plain, (![A_13]: (r2_hidden('#skF_1'(A_13, k1_xboole_0), k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_1312, c_1638])).
% 2.91/1.42  tff(c_1793, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1716, c_1640])).
% 2.91/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.42  
% 2.91/1.42  Inference rules
% 2.91/1.42  ----------------------
% 2.91/1.42  #Ref     : 0
% 2.91/1.42  #Sup     : 428
% 2.91/1.42  #Fact    : 0
% 2.91/1.42  #Define  : 0
% 2.91/1.42  #Split   : 4
% 2.91/1.42  #Chain   : 0
% 2.91/1.42  #Close   : 0
% 2.91/1.42  
% 2.91/1.42  Ordering : KBO
% 2.91/1.42  
% 2.91/1.42  Simplification rules
% 2.91/1.42  ----------------------
% 2.91/1.42  #Subsume      : 8
% 2.91/1.42  #Demod        : 284
% 2.91/1.42  #Tautology    : 280
% 2.91/1.42  #SimpNegUnit  : 13
% 2.91/1.42  #BackRed      : 2
% 2.91/1.42  
% 2.91/1.42  #Partial instantiations: 0
% 2.91/1.42  #Strategies tried      : 1
% 2.91/1.42  
% 2.91/1.42  Timing (in seconds)
% 2.91/1.42  ----------------------
% 2.91/1.43  Preprocessing        : 0.28
% 2.91/1.43  Parsing              : 0.16
% 2.91/1.43  CNF conversion       : 0.02
% 2.91/1.43  Main loop            : 0.45
% 2.91/1.43  Inferencing          : 0.17
% 2.91/1.43  Reduction            : 0.16
% 2.91/1.43  Demodulation         : 0.12
% 2.91/1.43  BG Simplification    : 0.02
% 2.91/1.43  Subsumption          : 0.06
% 2.91/1.43  Abstraction          : 0.02
% 2.91/1.43  MUC search           : 0.00
% 2.91/1.43  Cooper               : 0.00
% 2.91/1.43  Total                : 0.75
% 2.91/1.43  Index Insertion      : 0.00
% 2.91/1.43  Index Deletion       : 0.00
% 2.91/1.43  Index Matching       : 0.00
% 2.91/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
