%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:19 EST 2020

% Result     : Theorem 3.80s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :   76 (  99 expanded)
%              Number of leaves         :   30 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :   83 ( 118 expanded)
%              Number of equality atoms :   40 (  56 expanded)
%              Maximal formula depth    :    9 (   3 average)
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

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_38,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_72,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_76,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_66,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_74,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_182,plain,(
    ! [A_44,B_45] :
      ( r1_xboole_0(A_44,B_45)
      | k3_xboole_0(A_44,B_45) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( r1_xboole_0(B_10,A_9)
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_864,plain,(
    ! [B_87,A_88] :
      ( r1_xboole_0(B_87,A_88)
      | k3_xboole_0(A_88,B_87) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_182,c_14])).

tff(c_36,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_878,plain,(
    k3_xboole_0('#skF_5','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_864,c_36])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_420,plain,(
    ! [A_59,B_60] :
      ( r2_hidden('#skF_2'(A_59,B_60),B_60)
      | r1_xboole_0(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_426,plain,(
    ! [B_61,A_62] :
      ( ~ v1_xboole_0(B_61)
      | r1_xboole_0(A_62,B_61) ) ),
    inference(resolution,[status(thm)],[c_420,c_4])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_731,plain,(
    ! [A_81,B_82] :
      ( k3_xboole_0(A_81,B_82) = k1_xboole_0
      | ~ v1_xboole_0(B_82) ) ),
    inference(resolution,[status(thm)],[c_426,c_8])).

tff(c_734,plain,(
    ! [A_81] : k3_xboole_0(A_81,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_731])).

tff(c_30,plain,(
    ! [A_23] : k4_xboole_0(A_23,k1_xboole_0) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_252,plain,(
    ! [A_49,B_50] : k4_xboole_0(A_49,k4_xboole_0(A_49,B_50)) = k3_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_270,plain,(
    ! [A_23] : k4_xboole_0(A_23,A_23) = k3_xboole_0(A_23,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_252])).

tff(c_736,plain,(
    ! [A_23] : k4_xboole_0(A_23,A_23) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_734,c_270])).

tff(c_26,plain,(
    ! [A_19,B_20] : r1_tarski(k4_xboole_0(A_19,B_20),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_194,plain,(
    ! [A_46,B_47] :
      ( k2_xboole_0(A_46,B_47) = B_47
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_301,plain,(
    ! [A_53,B_54] : k2_xboole_0(k4_xboole_0(A_53,B_54),A_53) = A_53 ),
    inference(resolution,[status(thm)],[c_26,c_194])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_310,plain,(
    ! [A_53,B_54] : k2_xboole_0(A_53,k4_xboole_0(A_53,B_54)) = A_53 ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_2])).

tff(c_38,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_70,plain,(
    ! [B_37,A_38] :
      ( r1_xboole_0(B_37,A_38)
      | ~ r1_xboole_0(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_73,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_70])).

tff(c_163,plain,(
    ! [A_42,B_43] :
      ( k3_xboole_0(A_42,B_43) = k1_xboole_0
      | ~ r1_xboole_0(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_170,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_73,c_163])).

tff(c_34,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k4_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_376,plain,(
    ! [A_56,B_57] : k2_xboole_0(A_56,k4_xboole_0(B_57,A_56)) = k2_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_392,plain,(
    ! [A_27,B_28] : k2_xboole_0(k4_xboole_0(A_27,B_28),k3_xboole_0(A_27,B_28)) = k2_xboole_0(k4_xboole_0(A_27,B_28),A_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_376])).

tff(c_404,plain,(
    ! [A_27,B_28] : k2_xboole_0(k4_xboole_0(A_27,B_28),k3_xboole_0(A_27,B_28)) = k2_xboole_0(A_27,k4_xboole_0(A_27,B_28)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_392])).

tff(c_3018,plain,(
    ! [A_133,B_134] : k2_xboole_0(k4_xboole_0(A_133,B_134),k3_xboole_0(A_133,B_134)) = A_133 ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_404])).

tff(c_3126,plain,(
    k2_xboole_0(k4_xboole_0('#skF_5','#skF_4'),k1_xboole_0) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_3018])).

tff(c_24,plain,(
    ! [A_18] : k2_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3192,plain,(
    k4_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_3126,c_24])).

tff(c_40,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_206,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_194])).

tff(c_623,plain,(
    ! [A_76,B_77,C_78] : k4_xboole_0(k4_xboole_0(A_76,B_77),C_78) = k4_xboole_0(A_76,k2_xboole_0(B_77,C_78)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_931,plain,(
    ! [A_92,B_93,C_94] : r1_tarski(k4_xboole_0(A_92,k2_xboole_0(B_93,C_94)),k4_xboole_0(A_92,B_93)) ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_26])).

tff(c_1144,plain,(
    ! [A_99] : r1_tarski(k4_xboole_0(A_99,'#skF_4'),k4_xboole_0(A_99,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_931])).

tff(c_22,plain,(
    ! [A_16,B_17] :
      ( k2_xboole_0(A_16,B_17) = B_17
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1175,plain,(
    ! [A_99] : k2_xboole_0(k4_xboole_0(A_99,'#skF_4'),k4_xboole_0(A_99,'#skF_3')) = k4_xboole_0(A_99,'#skF_3') ),
    inference(resolution,[status(thm)],[c_1144,c_22])).

tff(c_3220,plain,(
    k2_xboole_0('#skF_5',k4_xboole_0('#skF_5','#skF_3')) = k4_xboole_0('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3192,c_1175])).

tff(c_3251,plain,(
    k4_xboole_0('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_3220])).

tff(c_3386,plain,(
    k4_xboole_0('#skF_5','#skF_5') = k3_xboole_0('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3251,c_34])).

tff(c_3401,plain,(
    k3_xboole_0('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_736,c_3386])).

tff(c_3403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_878,c_3401])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:20:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.80/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.69  
% 3.80/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.69  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.80/1.69  
% 3.80/1.69  %Foreground sorts:
% 3.80/1.69  
% 3.80/1.69  
% 3.80/1.69  %Background operators:
% 3.80/1.69  
% 3.80/1.69  
% 3.80/1.69  %Foreground operators:
% 3.80/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.80/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.80/1.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.80/1.69  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.80/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.80/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.80/1.69  tff('#skF_5', type, '#skF_5': $i).
% 3.80/1.69  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.80/1.69  tff('#skF_3', type, '#skF_3': $i).
% 3.80/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.80/1.69  tff('#skF_4', type, '#skF_4': $i).
% 3.80/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.80/1.69  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.80/1.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.80/1.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.80/1.69  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.80/1.69  
% 3.80/1.71  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.80/1.71  tff(f_42, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.80/1.71  tff(f_83, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.80/1.71  tff(f_38, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.80/1.71  tff(f_60, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.80/1.71  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.80/1.71  tff(f_72, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.80/1.71  tff(f_76, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.80/1.71  tff(f_68, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.80/1.71  tff(f_64, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.80/1.71  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.80/1.71  tff(f_70, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.80/1.71  tff(f_66, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.80/1.71  tff(f_74, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.80/1.71  tff(c_182, plain, (![A_44, B_45]: (r1_xboole_0(A_44, B_45) | k3_xboole_0(A_44, B_45)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.80/1.71  tff(c_14, plain, (![B_10, A_9]: (r1_xboole_0(B_10, A_9) | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.80/1.71  tff(c_864, plain, (![B_87, A_88]: (r1_xboole_0(B_87, A_88) | k3_xboole_0(A_88, B_87)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_182, c_14])).
% 3.80/1.71  tff(c_36, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.80/1.71  tff(c_878, plain, (k3_xboole_0('#skF_5', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_864, c_36])).
% 3.80/1.71  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.80/1.71  tff(c_420, plain, (![A_59, B_60]: (r2_hidden('#skF_2'(A_59, B_60), B_60) | r1_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.80/1.71  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.80/1.71  tff(c_426, plain, (![B_61, A_62]: (~v1_xboole_0(B_61) | r1_xboole_0(A_62, B_61))), inference(resolution, [status(thm)], [c_420, c_4])).
% 3.80/1.71  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.80/1.71  tff(c_731, plain, (![A_81, B_82]: (k3_xboole_0(A_81, B_82)=k1_xboole_0 | ~v1_xboole_0(B_82))), inference(resolution, [status(thm)], [c_426, c_8])).
% 3.80/1.71  tff(c_734, plain, (![A_81]: (k3_xboole_0(A_81, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_731])).
% 3.80/1.71  tff(c_30, plain, (![A_23]: (k4_xboole_0(A_23, k1_xboole_0)=A_23)), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.80/1.71  tff(c_252, plain, (![A_49, B_50]: (k4_xboole_0(A_49, k4_xboole_0(A_49, B_50))=k3_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.80/1.71  tff(c_270, plain, (![A_23]: (k4_xboole_0(A_23, A_23)=k3_xboole_0(A_23, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_252])).
% 3.80/1.71  tff(c_736, plain, (![A_23]: (k4_xboole_0(A_23, A_23)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_734, c_270])).
% 3.80/1.71  tff(c_26, plain, (![A_19, B_20]: (r1_tarski(k4_xboole_0(A_19, B_20), A_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.80/1.71  tff(c_194, plain, (![A_46, B_47]: (k2_xboole_0(A_46, B_47)=B_47 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.80/1.71  tff(c_301, plain, (![A_53, B_54]: (k2_xboole_0(k4_xboole_0(A_53, B_54), A_53)=A_53)), inference(resolution, [status(thm)], [c_26, c_194])).
% 3.80/1.71  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.80/1.71  tff(c_310, plain, (![A_53, B_54]: (k2_xboole_0(A_53, k4_xboole_0(A_53, B_54))=A_53)), inference(superposition, [status(thm), theory('equality')], [c_301, c_2])).
% 3.80/1.71  tff(c_38, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.80/1.71  tff(c_70, plain, (![B_37, A_38]: (r1_xboole_0(B_37, A_38) | ~r1_xboole_0(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.80/1.71  tff(c_73, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_70])).
% 3.80/1.71  tff(c_163, plain, (![A_42, B_43]: (k3_xboole_0(A_42, B_43)=k1_xboole_0 | ~r1_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.80/1.71  tff(c_170, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_73, c_163])).
% 3.80/1.71  tff(c_34, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k4_xboole_0(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.80/1.71  tff(c_376, plain, (![A_56, B_57]: (k2_xboole_0(A_56, k4_xboole_0(B_57, A_56))=k2_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.80/1.71  tff(c_392, plain, (![A_27, B_28]: (k2_xboole_0(k4_xboole_0(A_27, B_28), k3_xboole_0(A_27, B_28))=k2_xboole_0(k4_xboole_0(A_27, B_28), A_27))), inference(superposition, [status(thm), theory('equality')], [c_34, c_376])).
% 3.80/1.71  tff(c_404, plain, (![A_27, B_28]: (k2_xboole_0(k4_xboole_0(A_27, B_28), k3_xboole_0(A_27, B_28))=k2_xboole_0(A_27, k4_xboole_0(A_27, B_28)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_392])).
% 3.80/1.71  tff(c_3018, plain, (![A_133, B_134]: (k2_xboole_0(k4_xboole_0(A_133, B_134), k3_xboole_0(A_133, B_134))=A_133)), inference(demodulation, [status(thm), theory('equality')], [c_310, c_404])).
% 3.80/1.71  tff(c_3126, plain, (k2_xboole_0(k4_xboole_0('#skF_5', '#skF_4'), k1_xboole_0)='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_170, c_3018])).
% 3.80/1.71  tff(c_24, plain, (![A_18]: (k2_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.80/1.71  tff(c_3192, plain, (k4_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_3126, c_24])).
% 3.80/1.71  tff(c_40, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.80/1.71  tff(c_206, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_40, c_194])).
% 3.80/1.71  tff(c_623, plain, (![A_76, B_77, C_78]: (k4_xboole_0(k4_xboole_0(A_76, B_77), C_78)=k4_xboole_0(A_76, k2_xboole_0(B_77, C_78)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.80/1.71  tff(c_931, plain, (![A_92, B_93, C_94]: (r1_tarski(k4_xboole_0(A_92, k2_xboole_0(B_93, C_94)), k4_xboole_0(A_92, B_93)))), inference(superposition, [status(thm), theory('equality')], [c_623, c_26])).
% 3.80/1.71  tff(c_1144, plain, (![A_99]: (r1_tarski(k4_xboole_0(A_99, '#skF_4'), k4_xboole_0(A_99, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_206, c_931])).
% 3.80/1.71  tff(c_22, plain, (![A_16, B_17]: (k2_xboole_0(A_16, B_17)=B_17 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.80/1.71  tff(c_1175, plain, (![A_99]: (k2_xboole_0(k4_xboole_0(A_99, '#skF_4'), k4_xboole_0(A_99, '#skF_3'))=k4_xboole_0(A_99, '#skF_3'))), inference(resolution, [status(thm)], [c_1144, c_22])).
% 3.80/1.71  tff(c_3220, plain, (k2_xboole_0('#skF_5', k4_xboole_0('#skF_5', '#skF_3'))=k4_xboole_0('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3192, c_1175])).
% 3.80/1.71  tff(c_3251, plain, (k4_xboole_0('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_310, c_3220])).
% 3.80/1.71  tff(c_3386, plain, (k4_xboole_0('#skF_5', '#skF_5')=k3_xboole_0('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3251, c_34])).
% 3.80/1.71  tff(c_3401, plain, (k3_xboole_0('#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_736, c_3386])).
% 3.80/1.71  tff(c_3403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_878, c_3401])).
% 3.80/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.71  
% 3.80/1.71  Inference rules
% 3.80/1.71  ----------------------
% 3.80/1.71  #Ref     : 0
% 3.80/1.71  #Sup     : 834
% 3.80/1.71  #Fact    : 0
% 3.80/1.71  #Define  : 0
% 3.80/1.71  #Split   : 2
% 3.80/1.71  #Chain   : 0
% 3.80/1.71  #Close   : 0
% 3.80/1.71  
% 3.80/1.71  Ordering : KBO
% 3.80/1.71  
% 3.80/1.71  Simplification rules
% 3.80/1.71  ----------------------
% 3.80/1.71  #Subsume      : 6
% 3.80/1.71  #Demod        : 667
% 3.80/1.71  #Tautology    : 623
% 3.80/1.71  #SimpNegUnit  : 2
% 3.80/1.71  #BackRed      : 7
% 3.80/1.71  
% 3.80/1.71  #Partial instantiations: 0
% 3.80/1.71  #Strategies tried      : 1
% 3.80/1.71  
% 3.80/1.71  Timing (in seconds)
% 3.80/1.71  ----------------------
% 3.80/1.71  Preprocessing        : 0.28
% 3.80/1.71  Parsing              : 0.16
% 3.80/1.71  CNF conversion       : 0.02
% 3.80/1.71  Main loop            : 0.66
% 3.80/1.71  Inferencing          : 0.22
% 3.80/1.71  Reduction            : 0.28
% 3.80/1.71  Demodulation         : 0.22
% 3.80/1.71  BG Simplification    : 0.02
% 3.80/1.71  Subsumption          : 0.10
% 3.80/1.71  Abstraction          : 0.03
% 3.80/1.71  MUC search           : 0.00
% 3.80/1.71  Cooper               : 0.00
% 3.80/1.71  Total                : 0.98
% 3.80/1.71  Index Insertion      : 0.00
% 3.80/1.71  Index Deletion       : 0.00
% 3.80/1.71  Index Matching       : 0.00
% 3.80/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
