%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:51 EST 2020

% Result     : Theorem 8.93s
% Output     : CNFRefutation 8.99s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 177 expanded)
%              Number of leaves         :   33 (  72 expanded)
%              Depth                    :   15
%              Number of atoms          :   99 ( 212 expanded)
%              Number of equality atoms :   47 ( 132 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_63,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_77,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_58,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_28,plain,(
    ! [A_13] : k2_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_40,plain,(
    ! [B_25,A_24] : k2_tarski(B_25,A_24) = k2_tarski(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_158,plain,(
    ! [A_56,B_57] : k3_tarski(k2_tarski(A_56,B_57)) = k2_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_343,plain,(
    ! [A_74,B_75] : k3_tarski(k2_tarski(A_74,B_75)) = k2_xboole_0(B_75,A_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_158])).

tff(c_54,plain,(
    ! [A_38,B_39] : k3_tarski(k2_tarski(A_38,B_39)) = k2_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_371,plain,(
    ! [B_76,A_77] : k2_xboole_0(B_76,A_77) = k2_xboole_0(A_77,B_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_54])).

tff(c_438,plain,(
    ! [A_78] : k2_xboole_0(k1_xboole_0,A_78) = A_78 ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_28])).

tff(c_30,plain,(
    ! [A_14,B_15] : k2_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_458,plain,(
    ! [B_15] : k3_xboole_0(k1_xboole_0,B_15) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_30])).

tff(c_407,plain,(
    ! [A_77] : k2_xboole_0(k1_xboole_0,A_77) = A_77 ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_28])).

tff(c_562,plain,(
    ! [A_83,B_84] : k2_xboole_0(A_83,k4_xboole_0(B_84,A_83)) = k2_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_569,plain,(
    ! [B_84] : k4_xboole_0(B_84,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_562,c_407])).

tff(c_594,plain,(
    ! [B_85] : k4_xboole_0(B_85,k1_xboole_0) = B_85 ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_569])).

tff(c_38,plain,(
    ! [A_22,B_23] : k5_xboole_0(A_22,k4_xboole_0(B_23,A_22)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_603,plain,(
    ! [B_85] : k5_xboole_0(k1_xboole_0,B_85) = k2_xboole_0(k1_xboole_0,B_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_594,c_38])).

tff(c_612,plain,(
    ! [B_86] : k5_xboole_0(k1_xboole_0,B_86) = B_86 ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_603])).

tff(c_26,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_619,plain,(
    ! [B_12] : k4_xboole_0(k1_xboole_0,B_12) = k3_xboole_0(k1_xboole_0,B_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_612,c_26])).

tff(c_641,plain,(
    ! [B_87] : k4_xboole_0(k1_xboole_0,B_87) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_619])).

tff(c_653,plain,(
    ! [B_87] : k5_xboole_0(B_87,k1_xboole_0) = k2_xboole_0(B_87,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_641,c_38])).

tff(c_663,plain,(
    ! [B_87] : k5_xboole_0(B_87,k1_xboole_0) = B_87 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_653])).

tff(c_24,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_221,plain,(
    ! [A_63,B_64] :
      ( k3_xboole_0(A_63,B_64) = A_63
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_237,plain,(
    ! [B_10] : k3_xboole_0(B_10,B_10) = B_10 ),
    inference(resolution,[status(thm)],[c_24,c_221])).

tff(c_541,plain,(
    ! [A_81,B_82] : k5_xboole_0(A_81,k3_xboole_0(A_81,B_82)) = k4_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_556,plain,(
    ! [B_10] : k5_xboole_0(B_10,B_10) = k4_xboole_0(B_10,B_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_541])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1701,plain,(
    ! [A_153,B_154,C_155] :
      ( r2_hidden(A_153,B_154)
      | r2_hidden(A_153,C_155)
      | ~ r2_hidden(A_153,k5_xboole_0(B_154,C_155)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1730,plain,(
    ! [B_154,C_155,B_2] :
      ( r2_hidden('#skF_1'(k5_xboole_0(B_154,C_155),B_2),B_154)
      | r2_hidden('#skF_1'(k5_xboole_0(B_154,C_155),B_2),C_155)
      | r1_tarski(k5_xboole_0(B_154,C_155),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_1701])).

tff(c_5519,plain,(
    ! [B_154,B_2] :
      ( r1_tarski(k5_xboole_0(B_154,B_154),B_2)
      | r2_hidden('#skF_1'(k5_xboole_0(B_154,B_154),B_2),B_154) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_1730])).

tff(c_5521,plain,(
    ! [B_154,B_2] :
      ( r1_tarski(k4_xboole_0(B_154,B_154),B_2)
      | r2_hidden('#skF_1'(k4_xboole_0(B_154,B_154),B_2),B_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_556,c_5519])).

tff(c_1900,plain,(
    ! [A_167,C_168,B_169] :
      ( ~ r2_hidden(A_167,C_168)
      | ~ r2_hidden(A_167,B_169)
      | ~ r2_hidden(A_167,k5_xboole_0(B_169,C_168)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3762,plain,(
    ! [A_262,B_263] :
      ( ~ r2_hidden(A_262,B_263)
      | ~ r2_hidden(A_262,B_263)
      | ~ r2_hidden(A_262,k4_xboole_0(B_263,B_263)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_556,c_1900])).

tff(c_10873,plain,(
    ! [B_527,B_528] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(B_527,B_527),B_528),B_527)
      | r1_tarski(k4_xboole_0(B_527,B_527),B_528) ) ),
    inference(resolution,[status(thm)],[c_6,c_3762])).

tff(c_10985,plain,(
    ! [B_529,B_530] : r1_tarski(k4_xboole_0(B_529,B_529),B_530) ),
    inference(resolution,[status(thm)],[c_5521,c_10873])).

tff(c_36,plain,(
    ! [A_20,B_21] : r1_tarski(A_20,k2_xboole_0(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_499,plain,(
    ! [A_79] : r1_tarski(k1_xboole_0,A_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_36])).

tff(c_20,plain,(
    ! [B_10,A_9] :
      ( B_10 = A_9
      | ~ r1_tarski(B_10,A_9)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_505,plain,(
    ! [A_79] :
      ( k1_xboole_0 = A_79
      | ~ r1_tarski(A_79,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_499,c_20])).

tff(c_11036,plain,(
    ! [B_529] : k4_xboole_0(B_529,B_529) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10985,c_505])).

tff(c_52,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(k1_tarski(A_36),B_37)
      | ~ r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1522,plain,(
    ! [A_145,B_146] :
      ( k3_xboole_0(k1_tarski(A_145),B_146) = k1_tarski(A_145)
      | ~ r2_hidden(A_145,B_146) ) ),
    inference(resolution,[status(thm)],[c_52,c_221])).

tff(c_1547,plain,(
    ! [A_145,B_146] :
      ( k5_xboole_0(k1_tarski(A_145),k1_tarski(A_145)) = k4_xboole_0(k1_tarski(A_145),B_146)
      | ~ r2_hidden(A_145,B_146) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1522,c_26])).

tff(c_1582,plain,(
    ! [A_145,B_146] :
      ( k4_xboole_0(k1_tarski(A_145),k1_tarski(A_145)) = k4_xboole_0(k1_tarski(A_145),B_146)
      | ~ r2_hidden(A_145,B_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_1547])).

tff(c_12733,plain,(
    ! [A_549,B_550] :
      ( k4_xboole_0(k1_tarski(A_549),B_550) = k1_xboole_0
      | ~ r2_hidden(A_549,B_550) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11036,c_1582])).

tff(c_12895,plain,(
    ! [B_550,A_549] :
      ( k2_xboole_0(B_550,k1_tarski(A_549)) = k5_xboole_0(B_550,k1_xboole_0)
      | ~ r2_hidden(A_549,B_550) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12733,c_38])).

tff(c_15716,plain,(
    ! [B_570,A_571] :
      ( k2_xboole_0(B_570,k1_tarski(A_571)) = B_570
      | ~ r2_hidden(A_571,B_570) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_663,c_12895])).

tff(c_349,plain,(
    ! [B_75,A_74] : k2_xboole_0(B_75,A_74) = k2_xboole_0(A_74,B_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_54])).

tff(c_56,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),'#skF_3') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_370,plain,(
    k2_xboole_0('#skF_3',k1_tarski('#skF_2')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_56])).

tff(c_16022,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_15716,c_370])).

tff(c_16115,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_16022])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:31:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.93/3.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.93/3.28  
% 8.93/3.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.93/3.29  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 8.93/3.29  
% 8.93/3.29  %Foreground sorts:
% 8.93/3.29  
% 8.93/3.29  
% 8.93/3.29  %Background operators:
% 8.93/3.29  
% 8.93/3.29  
% 8.93/3.29  %Foreground operators:
% 8.93/3.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.93/3.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.93/3.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.93/3.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.93/3.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.93/3.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.93/3.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.93/3.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.93/3.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.93/3.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.93/3.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.93/3.29  tff('#skF_2', type, '#skF_2': $i).
% 8.93/3.29  tff('#skF_3', type, '#skF_3': $i).
% 8.93/3.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.93/3.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.93/3.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.93/3.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.93/3.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.93/3.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.93/3.29  
% 8.99/3.30  tff(f_82, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 8.99/3.30  tff(f_49, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 8.99/3.30  tff(f_63, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.99/3.30  tff(f_77, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 8.99/3.30  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 8.99/3.30  tff(f_57, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.99/3.30  tff(f_61, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 8.99/3.30  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.99/3.30  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.99/3.30  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.99/3.30  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.99/3.30  tff(f_39, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 8.99/3.30  tff(f_59, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 8.99/3.30  tff(f_75, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 8.99/3.30  tff(c_58, plain, (r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.99/3.30  tff(c_28, plain, (![A_13]: (k2_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.99/3.30  tff(c_40, plain, (![B_25, A_24]: (k2_tarski(B_25, A_24)=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.99/3.30  tff(c_158, plain, (![A_56, B_57]: (k3_tarski(k2_tarski(A_56, B_57))=k2_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.99/3.30  tff(c_343, plain, (![A_74, B_75]: (k3_tarski(k2_tarski(A_74, B_75))=k2_xboole_0(B_75, A_74))), inference(superposition, [status(thm), theory('equality')], [c_40, c_158])).
% 8.99/3.30  tff(c_54, plain, (![A_38, B_39]: (k3_tarski(k2_tarski(A_38, B_39))=k2_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.99/3.30  tff(c_371, plain, (![B_76, A_77]: (k2_xboole_0(B_76, A_77)=k2_xboole_0(A_77, B_76))), inference(superposition, [status(thm), theory('equality')], [c_343, c_54])).
% 8.99/3.30  tff(c_438, plain, (![A_78]: (k2_xboole_0(k1_xboole_0, A_78)=A_78)), inference(superposition, [status(thm), theory('equality')], [c_371, c_28])).
% 8.99/3.30  tff(c_30, plain, (![A_14, B_15]: (k2_xboole_0(A_14, k3_xboole_0(A_14, B_15))=A_14)), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.99/3.30  tff(c_458, plain, (![B_15]: (k3_xboole_0(k1_xboole_0, B_15)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_438, c_30])).
% 8.99/3.30  tff(c_407, plain, (![A_77]: (k2_xboole_0(k1_xboole_0, A_77)=A_77)), inference(superposition, [status(thm), theory('equality')], [c_371, c_28])).
% 8.99/3.30  tff(c_562, plain, (![A_83, B_84]: (k2_xboole_0(A_83, k4_xboole_0(B_84, A_83))=k2_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.99/3.30  tff(c_569, plain, (![B_84]: (k4_xboole_0(B_84, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_84))), inference(superposition, [status(thm), theory('equality')], [c_562, c_407])).
% 8.99/3.30  tff(c_594, plain, (![B_85]: (k4_xboole_0(B_85, k1_xboole_0)=B_85)), inference(demodulation, [status(thm), theory('equality')], [c_407, c_569])).
% 8.99/3.30  tff(c_38, plain, (![A_22, B_23]: (k5_xboole_0(A_22, k4_xboole_0(B_23, A_22))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.99/3.30  tff(c_603, plain, (![B_85]: (k5_xboole_0(k1_xboole_0, B_85)=k2_xboole_0(k1_xboole_0, B_85))), inference(superposition, [status(thm), theory('equality')], [c_594, c_38])).
% 8.99/3.30  tff(c_612, plain, (![B_86]: (k5_xboole_0(k1_xboole_0, B_86)=B_86)), inference(demodulation, [status(thm), theory('equality')], [c_407, c_603])).
% 8.99/3.30  tff(c_26, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.99/3.30  tff(c_619, plain, (![B_12]: (k4_xboole_0(k1_xboole_0, B_12)=k3_xboole_0(k1_xboole_0, B_12))), inference(superposition, [status(thm), theory('equality')], [c_612, c_26])).
% 8.99/3.30  tff(c_641, plain, (![B_87]: (k4_xboole_0(k1_xboole_0, B_87)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_458, c_619])).
% 8.99/3.30  tff(c_653, plain, (![B_87]: (k5_xboole_0(B_87, k1_xboole_0)=k2_xboole_0(B_87, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_641, c_38])).
% 8.99/3.30  tff(c_663, plain, (![B_87]: (k5_xboole_0(B_87, k1_xboole_0)=B_87)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_653])).
% 8.99/3.30  tff(c_24, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.99/3.30  tff(c_221, plain, (![A_63, B_64]: (k3_xboole_0(A_63, B_64)=A_63 | ~r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.99/3.30  tff(c_237, plain, (![B_10]: (k3_xboole_0(B_10, B_10)=B_10)), inference(resolution, [status(thm)], [c_24, c_221])).
% 8.99/3.30  tff(c_541, plain, (![A_81, B_82]: (k5_xboole_0(A_81, k3_xboole_0(A_81, B_82))=k4_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.99/3.30  tff(c_556, plain, (![B_10]: (k5_xboole_0(B_10, B_10)=k4_xboole_0(B_10, B_10))), inference(superposition, [status(thm), theory('equality')], [c_237, c_541])).
% 8.99/3.30  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.99/3.30  tff(c_1701, plain, (![A_153, B_154, C_155]: (r2_hidden(A_153, B_154) | r2_hidden(A_153, C_155) | ~r2_hidden(A_153, k5_xboole_0(B_154, C_155)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.99/3.30  tff(c_1730, plain, (![B_154, C_155, B_2]: (r2_hidden('#skF_1'(k5_xboole_0(B_154, C_155), B_2), B_154) | r2_hidden('#skF_1'(k5_xboole_0(B_154, C_155), B_2), C_155) | r1_tarski(k5_xboole_0(B_154, C_155), B_2))), inference(resolution, [status(thm)], [c_6, c_1701])).
% 8.99/3.30  tff(c_5519, plain, (![B_154, B_2]: (r1_tarski(k5_xboole_0(B_154, B_154), B_2) | r2_hidden('#skF_1'(k5_xboole_0(B_154, B_154), B_2), B_154))), inference(factorization, [status(thm), theory('equality')], [c_1730])).
% 8.99/3.30  tff(c_5521, plain, (![B_154, B_2]: (r1_tarski(k4_xboole_0(B_154, B_154), B_2) | r2_hidden('#skF_1'(k4_xboole_0(B_154, B_154), B_2), B_154))), inference(demodulation, [status(thm), theory('equality')], [c_556, c_556, c_5519])).
% 8.99/3.30  tff(c_1900, plain, (![A_167, C_168, B_169]: (~r2_hidden(A_167, C_168) | ~r2_hidden(A_167, B_169) | ~r2_hidden(A_167, k5_xboole_0(B_169, C_168)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.99/3.30  tff(c_3762, plain, (![A_262, B_263]: (~r2_hidden(A_262, B_263) | ~r2_hidden(A_262, B_263) | ~r2_hidden(A_262, k4_xboole_0(B_263, B_263)))), inference(superposition, [status(thm), theory('equality')], [c_556, c_1900])).
% 8.99/3.30  tff(c_10873, plain, (![B_527, B_528]: (~r2_hidden('#skF_1'(k4_xboole_0(B_527, B_527), B_528), B_527) | r1_tarski(k4_xboole_0(B_527, B_527), B_528))), inference(resolution, [status(thm)], [c_6, c_3762])).
% 8.99/3.30  tff(c_10985, plain, (![B_529, B_530]: (r1_tarski(k4_xboole_0(B_529, B_529), B_530))), inference(resolution, [status(thm)], [c_5521, c_10873])).
% 8.99/3.30  tff(c_36, plain, (![A_20, B_21]: (r1_tarski(A_20, k2_xboole_0(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.99/3.30  tff(c_499, plain, (![A_79]: (r1_tarski(k1_xboole_0, A_79))), inference(superposition, [status(thm), theory('equality')], [c_438, c_36])).
% 8.99/3.30  tff(c_20, plain, (![B_10, A_9]: (B_10=A_9 | ~r1_tarski(B_10, A_9) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.99/3.30  tff(c_505, plain, (![A_79]: (k1_xboole_0=A_79 | ~r1_tarski(A_79, k1_xboole_0))), inference(resolution, [status(thm)], [c_499, c_20])).
% 8.99/3.30  tff(c_11036, plain, (![B_529]: (k4_xboole_0(B_529, B_529)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10985, c_505])).
% 8.99/3.30  tff(c_52, plain, (![A_36, B_37]: (r1_tarski(k1_tarski(A_36), B_37) | ~r2_hidden(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.99/3.30  tff(c_1522, plain, (![A_145, B_146]: (k3_xboole_0(k1_tarski(A_145), B_146)=k1_tarski(A_145) | ~r2_hidden(A_145, B_146))), inference(resolution, [status(thm)], [c_52, c_221])).
% 8.99/3.30  tff(c_1547, plain, (![A_145, B_146]: (k5_xboole_0(k1_tarski(A_145), k1_tarski(A_145))=k4_xboole_0(k1_tarski(A_145), B_146) | ~r2_hidden(A_145, B_146))), inference(superposition, [status(thm), theory('equality')], [c_1522, c_26])).
% 8.99/3.30  tff(c_1582, plain, (![A_145, B_146]: (k4_xboole_0(k1_tarski(A_145), k1_tarski(A_145))=k4_xboole_0(k1_tarski(A_145), B_146) | ~r2_hidden(A_145, B_146))), inference(demodulation, [status(thm), theory('equality')], [c_556, c_1547])).
% 8.99/3.30  tff(c_12733, plain, (![A_549, B_550]: (k4_xboole_0(k1_tarski(A_549), B_550)=k1_xboole_0 | ~r2_hidden(A_549, B_550))), inference(demodulation, [status(thm), theory('equality')], [c_11036, c_1582])).
% 8.99/3.30  tff(c_12895, plain, (![B_550, A_549]: (k2_xboole_0(B_550, k1_tarski(A_549))=k5_xboole_0(B_550, k1_xboole_0) | ~r2_hidden(A_549, B_550))), inference(superposition, [status(thm), theory('equality')], [c_12733, c_38])).
% 8.99/3.30  tff(c_15716, plain, (![B_570, A_571]: (k2_xboole_0(B_570, k1_tarski(A_571))=B_570 | ~r2_hidden(A_571, B_570))), inference(demodulation, [status(thm), theory('equality')], [c_663, c_12895])).
% 8.99/3.30  tff(c_349, plain, (![B_75, A_74]: (k2_xboole_0(B_75, A_74)=k2_xboole_0(A_74, B_75))), inference(superposition, [status(thm), theory('equality')], [c_343, c_54])).
% 8.99/3.30  tff(c_56, plain, (k2_xboole_0(k1_tarski('#skF_2'), '#skF_3')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.99/3.30  tff(c_370, plain, (k2_xboole_0('#skF_3', k1_tarski('#skF_2'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_349, c_56])).
% 8.99/3.30  tff(c_16022, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_15716, c_370])).
% 8.99/3.30  tff(c_16115, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_16022])).
% 8.99/3.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.99/3.30  
% 8.99/3.30  Inference rules
% 8.99/3.30  ----------------------
% 8.99/3.30  #Ref     : 0
% 8.99/3.30  #Sup     : 3950
% 8.99/3.30  #Fact    : 2
% 8.99/3.30  #Define  : 0
% 8.99/3.30  #Split   : 2
% 8.99/3.30  #Chain   : 0
% 8.99/3.30  #Close   : 0
% 8.99/3.30  
% 8.99/3.30  Ordering : KBO
% 8.99/3.30  
% 8.99/3.30  Simplification rules
% 8.99/3.30  ----------------------
% 8.99/3.30  #Subsume      : 1086
% 8.99/3.30  #Demod        : 2950
% 8.99/3.30  #Tautology    : 1673
% 8.99/3.30  #SimpNegUnit  : 73
% 8.99/3.30  #BackRed      : 34
% 8.99/3.30  
% 8.99/3.30  #Partial instantiations: 0
% 8.99/3.30  #Strategies tried      : 1
% 8.99/3.30  
% 8.99/3.30  Timing (in seconds)
% 8.99/3.30  ----------------------
% 8.99/3.31  Preprocessing        : 0.31
% 8.99/3.31  Parsing              : 0.16
% 8.99/3.31  CNF conversion       : 0.02
% 8.99/3.31  Main loop            : 2.23
% 8.99/3.31  Inferencing          : 0.54
% 8.99/3.31  Reduction            : 1.02
% 8.99/3.31  Demodulation         : 0.83
% 8.99/3.31  BG Simplification    : 0.06
% 8.99/3.31  Subsumption          : 0.51
% 8.99/3.31  Abstraction          : 0.08
% 8.99/3.31  MUC search           : 0.00
% 8.99/3.31  Cooper               : 0.00
% 8.99/3.31  Total                : 2.58
% 8.99/3.31  Index Insertion      : 0.00
% 8.99/3.31  Index Deletion       : 0.00
% 8.99/3.31  Index Matching       : 0.00
% 8.99/3.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
