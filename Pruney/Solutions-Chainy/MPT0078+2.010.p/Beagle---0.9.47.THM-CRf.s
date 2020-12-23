%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:40 EST 2020

% Result     : Theorem 8.58s
% Output     : CNFRefutation 8.72s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 265 expanded)
%              Number of leaves         :   25 ( 103 expanded)
%              Depth                    :   10
%              Number of atoms          :   74 ( 306 expanded)
%              Number of equality atoms :   60 ( 247 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

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

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,B)
          & r1_xboole_0(A,B)
          & r1_xboole_0(C,B) )
       => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_53,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

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

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(c_24,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_14,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_301,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k4_xboole_0(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_325,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_301])).

tff(c_332,plain,(
    ! [A_44] : k4_xboole_0(A_44,A_44) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_325])).

tff(c_20,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_337,plain,(
    ! [A_44] : k4_xboole_0(A_44,k1_xboole_0) = k3_xboole_0(A_44,A_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_20])).

tff(c_349,plain,(
    ! [A_44] : k3_xboole_0(A_44,A_44) = A_44 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_337])).

tff(c_398,plain,(
    ! [A_46,B_47,C_48] : k4_xboole_0(k4_xboole_0(A_46,B_47),C_48) = k4_xboole_0(A_46,k2_xboole_0(B_47,C_48)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_467,plain,(
    ! [A_13,C_48] : k4_xboole_0(A_13,k2_xboole_0(k1_xboole_0,C_48)) = k4_xboole_0(A_13,C_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_398])).

tff(c_331,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_325])).

tff(c_22,plain,(
    ! [A_21,B_22,C_23] : k4_xboole_0(k3_xboole_0(A_21,B_22),C_23) = k3_xboole_0(A_21,k4_xboole_0(B_22,C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_443,plain,(
    ! [A_19,B_20,C_48] : k4_xboole_0(A_19,k2_xboole_0(k4_xboole_0(A_19,B_20),C_48)) = k4_xboole_0(k3_xboole_0(A_19,B_20),C_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_398])).

tff(c_8697,plain,(
    ! [A_173,B_174,C_175] : k4_xboole_0(A_173,k2_xboole_0(k4_xboole_0(A_173,B_174),C_175)) = k3_xboole_0(A_173,k4_xboole_0(B_174,C_175)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_443])).

tff(c_8914,plain,(
    ! [A_13,C_175] : k4_xboole_0(A_13,k2_xboole_0(k1_xboole_0,C_175)) = k3_xboole_0(A_13,k4_xboole_0(A_13,C_175)) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_8697])).

tff(c_19387,plain,(
    ! [A_275,C_276] : k3_xboole_0(A_275,k4_xboole_0(A_275,C_276)) = k4_xboole_0(A_275,C_276) ),
    inference(demodulation,[status(thm),theory(equality)],[c_467,c_8914])).

tff(c_28,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_212,plain,(
    ! [A_36,B_37,C_38] :
      ( ~ r1_xboole_0(A_36,B_37)
      | ~ r2_hidden(C_38,k3_xboole_0(A_36,B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_243,plain,(
    ! [A_40,B_41] :
      ( ~ r1_xboole_0(A_40,B_41)
      | k3_xboole_0(A_40,B_41) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_212])).

tff(c_251,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_243])).

tff(c_6020,plain,(
    ! [A_145,B_146] : k4_xboole_0(A_145,k3_xboole_0(A_145,B_146)) = k3_xboole_0(A_145,k4_xboole_0(A_145,B_146)) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_20])).

tff(c_6256,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_4')) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_6020])).

tff(c_6336,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_6256])).

tff(c_19494,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_19387,c_6336])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_14,B_15,C_16] : k4_xboole_0(k4_xboole_0(A_14,B_15),C_16) = k4_xboole_0(A_14,k2_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_447,plain,(
    ! [A_46,B_47,B_20] : k4_xboole_0(A_46,k2_xboole_0(B_47,k4_xboole_0(k4_xboole_0(A_46,B_47),B_20))) = k3_xboole_0(k4_xboole_0(A_46,B_47),B_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_398])).

tff(c_478,plain,(
    ! [A_46,B_47,B_20] : k4_xboole_0(A_46,k2_xboole_0(B_47,k4_xboole_0(A_46,k2_xboole_0(B_47,B_20)))) = k3_xboole_0(k4_xboole_0(A_46,B_47),B_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_447])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    k2_xboole_0('#skF_5','#skF_4') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_31,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_30])).

tff(c_9454,plain,(
    ! [A_182,B_183,B_184] : k4_xboole_0(A_182,k2_xboole_0(B_183,k4_xboole_0(A_182,k2_xboole_0(B_183,B_184)))) = k3_xboole_0(k4_xboole_0(A_182,B_183),B_184) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_447])).

tff(c_9727,plain,(
    ! [A_182] : k4_xboole_0(A_182,k2_xboole_0('#skF_4',k4_xboole_0(A_182,k2_xboole_0('#skF_4','#skF_3')))) = k3_xboole_0(k4_xboole_0(A_182,'#skF_4'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_9454])).

tff(c_10142,plain,(
    ! [A_189] : k3_xboole_0('#skF_5',k4_xboole_0(A_189,'#skF_4')) = k3_xboole_0('#skF_3',k4_xboole_0(A_189,'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_478,c_4,c_9727])).

tff(c_26,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_250,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_243])).

tff(c_6259,plain,(
    k3_xboole_0('#skF_5',k4_xboole_0('#skF_5','#skF_4')) = k4_xboole_0('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_6020])).

tff(c_6337,plain,(
    k3_xboole_0('#skF_5',k4_xboole_0('#skF_5','#skF_4')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_6259])).

tff(c_10169,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_5','#skF_4')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_10142,c_6337])).

tff(c_63,plain,(
    ! [B_28,A_29] : k2_xboole_0(B_28,A_29) = k2_xboole_0(A_29,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k2_xboole_0(A_17,B_18)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_186,plain,(
    ! [B_34,A_35] : k4_xboole_0(B_34,k2_xboole_0(A_35,B_34)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_18])).

tff(c_205,plain,(
    k4_xboole_0('#skF_5',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_186])).

tff(c_10844,plain,(
    ! [A_197,B_198,C_199] : k4_xboole_0(k4_xboole_0(A_197,B_198),k4_xboole_0(A_197,k2_xboole_0(B_198,C_199))) = k3_xboole_0(k4_xboole_0(A_197,B_198),C_199) ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_20])).

tff(c_11026,plain,(
    k4_xboole_0(k4_xboole_0('#skF_5','#skF_4'),k1_xboole_0) = k3_xboole_0(k4_xboole_0('#skF_5','#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_10844])).

tff(c_11096,plain,(
    k4_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10169,c_4,c_14,c_11026])).

tff(c_11103,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11096,c_10169])).

tff(c_9771,plain,(
    ! [A_182] : k3_xboole_0('#skF_5',k4_xboole_0(A_182,'#skF_4')) = k3_xboole_0('#skF_3',k4_xboole_0(A_182,'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_478,c_4,c_9727])).

tff(c_19862,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_4')) = k3_xboole_0('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_19494,c_9771])).

tff(c_19916,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_19494,c_11103,c_4,c_19862])).

tff(c_19918,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_19916])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:46:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.58/3.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.58/3.51  
% 8.58/3.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.58/3.51  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 8.58/3.51  
% 8.58/3.51  %Foreground sorts:
% 8.58/3.51  
% 8.58/3.51  
% 8.58/3.51  %Background operators:
% 8.58/3.51  
% 8.58/3.51  
% 8.58/3.51  %Foreground operators:
% 8.58/3.51  tff('#skF_2', type, '#skF_2': $i > $i).
% 8.58/3.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.58/3.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.58/3.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.58/3.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.58/3.51  tff('#skF_5', type, '#skF_5': $i).
% 8.58/3.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.58/3.51  tff('#skF_3', type, '#skF_3': $i).
% 8.58/3.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.58/3.51  tff('#skF_4', type, '#skF_4': $i).
% 8.58/3.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.58/3.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.58/3.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.58/3.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.58/3.51  
% 8.72/3.52  tff(f_72, negated_conjecture, ~(![A, B, C]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, B)) & r1_xboole_0(A, B)) & r1_xboole_0(C, B)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_xboole_1)).
% 8.72/3.52  tff(f_55, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 8.72/3.52  tff(f_53, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 8.72/3.52  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.72/3.52  tff(f_57, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 8.72/3.52  tff(f_63, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 8.72/3.52  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 8.72/3.52  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 8.72/3.52  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.72/3.52  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.72/3.52  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 8.72/3.52  tff(c_24, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.72/3.52  tff(c_14, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.72/3.52  tff(c_12, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.72/3.52  tff(c_301, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k4_xboole_0(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.72/3.52  tff(c_325, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_301])).
% 8.72/3.52  tff(c_332, plain, (![A_44]: (k4_xboole_0(A_44, A_44)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_325])).
% 8.72/3.52  tff(c_20, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.72/3.52  tff(c_337, plain, (![A_44]: (k4_xboole_0(A_44, k1_xboole_0)=k3_xboole_0(A_44, A_44))), inference(superposition, [status(thm), theory('equality')], [c_332, c_20])).
% 8.72/3.52  tff(c_349, plain, (![A_44]: (k3_xboole_0(A_44, A_44)=A_44)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_337])).
% 8.72/3.52  tff(c_398, plain, (![A_46, B_47, C_48]: (k4_xboole_0(k4_xboole_0(A_46, B_47), C_48)=k4_xboole_0(A_46, k2_xboole_0(B_47, C_48)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.72/3.52  tff(c_467, plain, (![A_13, C_48]: (k4_xboole_0(A_13, k2_xboole_0(k1_xboole_0, C_48))=k4_xboole_0(A_13, C_48))), inference(superposition, [status(thm), theory('equality')], [c_14, c_398])).
% 8.72/3.52  tff(c_331, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_325])).
% 8.72/3.52  tff(c_22, plain, (![A_21, B_22, C_23]: (k4_xboole_0(k3_xboole_0(A_21, B_22), C_23)=k3_xboole_0(A_21, k4_xboole_0(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.72/3.52  tff(c_443, plain, (![A_19, B_20, C_48]: (k4_xboole_0(A_19, k2_xboole_0(k4_xboole_0(A_19, B_20), C_48))=k4_xboole_0(k3_xboole_0(A_19, B_20), C_48))), inference(superposition, [status(thm), theory('equality')], [c_20, c_398])).
% 8.72/3.52  tff(c_8697, plain, (![A_173, B_174, C_175]: (k4_xboole_0(A_173, k2_xboole_0(k4_xboole_0(A_173, B_174), C_175))=k3_xboole_0(A_173, k4_xboole_0(B_174, C_175)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_443])).
% 8.72/3.52  tff(c_8914, plain, (![A_13, C_175]: (k4_xboole_0(A_13, k2_xboole_0(k1_xboole_0, C_175))=k3_xboole_0(A_13, k4_xboole_0(A_13, C_175)))), inference(superposition, [status(thm), theory('equality')], [c_331, c_8697])).
% 8.72/3.52  tff(c_19387, plain, (![A_275, C_276]: (k3_xboole_0(A_275, k4_xboole_0(A_275, C_276))=k4_xboole_0(A_275, C_276))), inference(demodulation, [status(thm), theory('equality')], [c_467, c_8914])).
% 8.72/3.52  tff(c_28, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.72/3.52  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.72/3.52  tff(c_212, plain, (![A_36, B_37, C_38]: (~r1_xboole_0(A_36, B_37) | ~r2_hidden(C_38, k3_xboole_0(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.72/3.52  tff(c_243, plain, (![A_40, B_41]: (~r1_xboole_0(A_40, B_41) | k3_xboole_0(A_40, B_41)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_212])).
% 8.72/3.52  tff(c_251, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_243])).
% 8.72/3.52  tff(c_6020, plain, (![A_145, B_146]: (k4_xboole_0(A_145, k3_xboole_0(A_145, B_146))=k3_xboole_0(A_145, k4_xboole_0(A_145, B_146)))), inference(superposition, [status(thm), theory('equality')], [c_301, c_20])).
% 8.72/3.52  tff(c_6256, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_4'))=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_251, c_6020])).
% 8.72/3.52  tff(c_6336, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_6256])).
% 8.72/3.52  tff(c_19494, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_19387, c_6336])).
% 8.72/3.52  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.72/3.52  tff(c_16, plain, (![A_14, B_15, C_16]: (k4_xboole_0(k4_xboole_0(A_14, B_15), C_16)=k4_xboole_0(A_14, k2_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.72/3.52  tff(c_447, plain, (![A_46, B_47, B_20]: (k4_xboole_0(A_46, k2_xboole_0(B_47, k4_xboole_0(k4_xboole_0(A_46, B_47), B_20)))=k3_xboole_0(k4_xboole_0(A_46, B_47), B_20))), inference(superposition, [status(thm), theory('equality')], [c_20, c_398])).
% 8.72/3.52  tff(c_478, plain, (![A_46, B_47, B_20]: (k4_xboole_0(A_46, k2_xboole_0(B_47, k4_xboole_0(A_46, k2_xboole_0(B_47, B_20))))=k3_xboole_0(k4_xboole_0(A_46, B_47), B_20))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_447])).
% 8.72/3.52  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.72/3.52  tff(c_30, plain, (k2_xboole_0('#skF_5', '#skF_4')=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.72/3.52  tff(c_31, plain, (k2_xboole_0('#skF_4', '#skF_5')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_30])).
% 8.72/3.52  tff(c_9454, plain, (![A_182, B_183, B_184]: (k4_xboole_0(A_182, k2_xboole_0(B_183, k4_xboole_0(A_182, k2_xboole_0(B_183, B_184))))=k3_xboole_0(k4_xboole_0(A_182, B_183), B_184))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_447])).
% 8.72/3.52  tff(c_9727, plain, (![A_182]: (k4_xboole_0(A_182, k2_xboole_0('#skF_4', k4_xboole_0(A_182, k2_xboole_0('#skF_4', '#skF_3'))))=k3_xboole_0(k4_xboole_0(A_182, '#skF_4'), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_31, c_9454])).
% 8.72/3.52  tff(c_10142, plain, (![A_189]: (k3_xboole_0('#skF_5', k4_xboole_0(A_189, '#skF_4'))=k3_xboole_0('#skF_3', k4_xboole_0(A_189, '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_478, c_4, c_9727])).
% 8.72/3.52  tff(c_26, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.72/3.52  tff(c_250, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_243])).
% 8.72/3.52  tff(c_6259, plain, (k3_xboole_0('#skF_5', k4_xboole_0('#skF_5', '#skF_4'))=k4_xboole_0('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_250, c_6020])).
% 8.72/3.52  tff(c_6337, plain, (k3_xboole_0('#skF_5', k4_xboole_0('#skF_5', '#skF_4'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_6259])).
% 8.72/3.52  tff(c_10169, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_5', '#skF_4'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_10142, c_6337])).
% 8.72/3.52  tff(c_63, plain, (![B_28, A_29]: (k2_xboole_0(B_28, A_29)=k2_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.72/3.52  tff(c_18, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k2_xboole_0(A_17, B_18))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.72/3.52  tff(c_186, plain, (![B_34, A_35]: (k4_xboole_0(B_34, k2_xboole_0(A_35, B_34))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_63, c_18])).
% 8.72/3.52  tff(c_205, plain, (k4_xboole_0('#skF_5', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_31, c_186])).
% 8.72/3.52  tff(c_10844, plain, (![A_197, B_198, C_199]: (k4_xboole_0(k4_xboole_0(A_197, B_198), k4_xboole_0(A_197, k2_xboole_0(B_198, C_199)))=k3_xboole_0(k4_xboole_0(A_197, B_198), C_199))), inference(superposition, [status(thm), theory('equality')], [c_398, c_20])).
% 8.72/3.52  tff(c_11026, plain, (k4_xboole_0(k4_xboole_0('#skF_5', '#skF_4'), k1_xboole_0)=k3_xboole_0(k4_xboole_0('#skF_5', '#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_205, c_10844])).
% 8.72/3.52  tff(c_11096, plain, (k4_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_10169, c_4, c_14, c_11026])).
% 8.72/3.52  tff(c_11103, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_11096, c_10169])).
% 8.72/3.52  tff(c_9771, plain, (![A_182]: (k3_xboole_0('#skF_5', k4_xboole_0(A_182, '#skF_4'))=k3_xboole_0('#skF_3', k4_xboole_0(A_182, '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_478, c_4, c_9727])).
% 8.72/3.52  tff(c_19862, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_4'))=k3_xboole_0('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_19494, c_9771])).
% 8.72/3.52  tff(c_19916, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_349, c_19494, c_11103, c_4, c_19862])).
% 8.72/3.52  tff(c_19918, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_19916])).
% 8.72/3.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.72/3.52  
% 8.72/3.52  Inference rules
% 8.72/3.52  ----------------------
% 8.72/3.52  #Ref     : 0
% 8.72/3.52  #Sup     : 4959
% 8.72/3.52  #Fact    : 0
% 8.72/3.52  #Define  : 0
% 8.72/3.52  #Split   : 9
% 8.72/3.52  #Chain   : 0
% 8.72/3.52  #Close   : 0
% 8.72/3.52  
% 8.72/3.52  Ordering : KBO
% 8.72/3.52  
% 8.72/3.52  Simplification rules
% 8.72/3.52  ----------------------
% 8.72/3.52  #Subsume      : 131
% 8.72/3.52  #Demod        : 5377
% 8.72/3.52  #Tautology    : 3421
% 8.72/3.52  #SimpNegUnit  : 99
% 8.72/3.52  #BackRed      : 13
% 8.72/3.52  
% 8.72/3.52  #Partial instantiations: 0
% 8.72/3.52  #Strategies tried      : 1
% 8.72/3.52  
% 8.72/3.52  Timing (in seconds)
% 8.72/3.52  ----------------------
% 8.72/3.53  Preprocessing        : 0.29
% 8.72/3.53  Parsing              : 0.15
% 8.72/3.53  CNF conversion       : 0.02
% 8.72/3.53  Main loop            : 2.47
% 8.72/3.53  Inferencing          : 0.51
% 8.72/3.53  Reduction            : 1.41
% 8.72/3.53  Demodulation         : 1.23
% 8.72/3.53  BG Simplification    : 0.05
% 8.72/3.53  Subsumption          : 0.38
% 8.72/3.53  Abstraction          : 0.08
% 8.72/3.53  MUC search           : 0.00
% 8.72/3.53  Cooper               : 0.00
% 8.72/3.53  Total                : 2.80
% 8.72/3.53  Index Insertion      : 0.00
% 8.72/3.53  Index Deletion       : 0.00
% 8.72/3.53  Index Matching       : 0.00
% 8.72/3.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
