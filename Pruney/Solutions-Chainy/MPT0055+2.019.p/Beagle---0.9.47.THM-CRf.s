%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:00 EST 2020

% Result     : Theorem 9.91s
% Output     : CNFRefutation 10.10s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 118 expanded)
%              Number of leaves         :   29 (  50 expanded)
%              Depth                    :   15
%              Number of atoms          :   86 ( 137 expanded)
%              Number of equality atoms :   54 (  93 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_77,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_83,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_79,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_87,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_85,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_75,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_38,plain,(
    ! [A_26] : k2_xboole_0(A_26,k1_xboole_0) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_44,plain,(
    ! [A_30] : k4_xboole_0(A_30,k1_xboole_0) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_96,plain,(
    ! [B_39,A_40] : k3_xboole_0(B_39,A_40) = k3_xboole_0(A_40,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_40,plain,(
    ! [A_27] : k3_xboole_0(A_27,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_112,plain,(
    ! [A_40] : k3_xboole_0(k1_xboole_0,A_40) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_40])).

tff(c_336,plain,(
    ! [A_62,B_63] : k4_xboole_0(A_62,k3_xboole_0(A_62,B_63)) = k4_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_351,plain,(
    ! [A_40] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_336])).

tff(c_366,plain,(
    ! [A_40] : k4_xboole_0(k1_xboole_0,A_40) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_351])).

tff(c_143,plain,(
    ! [B_41,A_42] : k2_xboole_0(B_41,A_42) = k2_xboole_0(A_42,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_181,plain,(
    ! [A_26] : k2_xboole_0(k1_xboole_0,A_26) = A_26 ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_143])).

tff(c_429,plain,(
    ! [A_68,B_69] : k4_xboole_0(k2_xboole_0(A_68,B_69),B_69) = k4_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_448,plain,(
    ! [A_26] : k4_xboole_0(k1_xboole_0,A_26) = k4_xboole_0(A_26,A_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_429])).

tff(c_465,plain,(
    ! [A_26] : k4_xboole_0(A_26,A_26) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_448])).

tff(c_24,plain,(
    ! [A_11] : k3_xboole_0(A_11,A_11) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_885,plain,(
    ! [A_99,B_100,C_101] : k3_xboole_0(k3_xboole_0(A_99,B_100),C_101) = k3_xboole_0(A_99,k3_xboole_0(B_100,C_101)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1073,plain,(
    ! [A_107,C_108] : k3_xboole_0(A_107,k3_xboole_0(A_107,C_108)) = k3_xboole_0(A_107,C_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_885])).

tff(c_354,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k3_xboole_0(B_4,A_3)) = k4_xboole_0(A_3,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_336])).

tff(c_1101,plain,(
    ! [A_107,C_108] : k4_xboole_0(k3_xboole_0(A_107,C_108),k3_xboole_0(A_107,C_108)) = k4_xboole_0(k3_xboole_0(A_107,C_108),A_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_1073,c_354])).

tff(c_1159,plain,(
    ! [A_109,C_110] : k4_xboole_0(k3_xboole_0(A_109,C_110),A_109) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_1101])).

tff(c_42,plain,(
    ! [A_28,B_29] : k2_xboole_0(A_28,k4_xboole_0(B_29,A_28)) = k2_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1167,plain,(
    ! [A_109,C_110] : k2_xboole_0(A_109,k3_xboole_0(A_109,C_110)) = k2_xboole_0(A_109,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1159,c_42])).

tff(c_1207,plain,(
    ! [A_109,C_110] : k2_xboole_0(A_109,k3_xboole_0(A_109,C_110)) = A_109 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1167])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_48,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k3_xboole_0(A_33,B_34)) = k4_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_30,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_3'(A_13,B_14),A_13)
      | r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_403,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_3'(A_65,B_66),B_66)
      | r1_xboole_0(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [D_10,B_6,A_5] :
      ( ~ r2_hidden(D_10,B_6)
      | ~ r2_hidden(D_10,k4_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10708,plain,(
    ! [A_269,A_270,B_271] :
      ( ~ r2_hidden('#skF_3'(A_269,k4_xboole_0(A_270,B_271)),B_271)
      | r1_xboole_0(A_269,k4_xboole_0(A_270,B_271)) ) ),
    inference(resolution,[status(thm)],[c_403,c_8])).

tff(c_10809,plain,(
    ! [A_272,A_273] : r1_xboole_0(A_272,k4_xboole_0(A_273,A_272)) ),
    inference(resolution,[status(thm)],[c_30,c_10708])).

tff(c_1691,plain,(
    ! [A_132,B_133,C_134] :
      ( r2_hidden('#skF_1'(A_132,B_133,C_134),A_132)
      | r2_hidden('#skF_2'(A_132,B_133,C_134),C_134)
      | k4_xboole_0(A_132,B_133) = C_134 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [A_5,B_6,C_7] :
      ( ~ r2_hidden('#skF_1'(A_5,B_6,C_7),B_6)
      | r2_hidden('#skF_2'(A_5,B_6,C_7),C_7)
      | k4_xboole_0(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1694,plain,(
    ! [A_132,C_134] :
      ( r2_hidden('#skF_2'(A_132,A_132,C_134),C_134)
      | k4_xboole_0(A_132,A_132) = C_134 ) ),
    inference(resolution,[status(thm)],[c_1691,c_20])).

tff(c_1937,plain,(
    ! [A_143,C_144] :
      ( r2_hidden('#skF_2'(A_143,A_143,C_144),C_144)
      | k1_xboole_0 = C_144 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_1694])).

tff(c_34,plain,(
    ! [A_18,B_19,C_22] :
      ( ~ r1_xboole_0(A_18,B_19)
      | ~ r2_hidden(C_22,k3_xboole_0(A_18,B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1961,plain,(
    ! [A_18,B_19] :
      ( ~ r1_xboole_0(A_18,B_19)
      | k3_xboole_0(A_18,B_19) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1937,c_34])).

tff(c_10996,plain,(
    ! [A_276,A_277] : k3_xboole_0(A_276,k4_xboole_0(A_277,A_276)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10809,c_1961])).

tff(c_11127,plain,(
    ! [A_276,A_277] : k4_xboole_0(A_276,k4_xboole_0(A_277,A_276)) = k4_xboole_0(A_276,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10996,c_48])).

tff(c_11254,plain,(
    ! [A_276,A_277] : k4_xboole_0(A_276,k4_xboole_0(A_277,A_276)) = A_276 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_11127])).

tff(c_499,plain,(
    ! [A_71,B_72] : k2_xboole_0(A_71,k4_xboole_0(B_72,A_71)) = k2_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_46,plain,(
    ! [A_31,B_32] : k4_xboole_0(k2_xboole_0(A_31,B_32),B_32) = k4_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_505,plain,(
    ! [A_71,B_72] : k4_xboole_0(k2_xboole_0(A_71,B_72),k4_xboole_0(B_72,A_71)) = k4_xboole_0(A_71,k4_xboole_0(B_72,A_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_46])).

tff(c_22916,plain,(
    ! [A_409,B_410] : k4_xboole_0(k2_xboole_0(A_409,B_410),k4_xboole_0(B_410,A_409)) = A_409 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11254,c_505])).

tff(c_23228,plain,(
    ! [A_33,B_34] : k4_xboole_0(k2_xboole_0(k3_xboole_0(A_33,B_34),A_33),k4_xboole_0(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_22916])).

tff(c_23320,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k4_xboole_0(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1207,c_2,c_23228])).

tff(c_50,plain,(
    k4_xboole_0('#skF_5',k4_xboole_0('#skF_5','#skF_6')) != k3_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_51,plain,(
    k4_xboole_0('#skF_5',k4_xboole_0('#skF_5','#skF_6')) != k3_xboole_0('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_50])).

tff(c_29409,plain,(
    k3_xboole_0('#skF_5','#skF_6') != k3_xboole_0('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23320,c_51])).

tff(c_29412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_29409])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:26:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.91/4.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.91/4.10  
% 9.91/4.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.91/4.10  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 9.91/4.10  
% 9.91/4.10  %Foreground sorts:
% 9.91/4.10  
% 9.91/4.10  
% 9.91/4.10  %Background operators:
% 9.91/4.10  
% 9.91/4.10  
% 9.91/4.10  %Foreground operators:
% 9.91/4.10  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.91/4.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.91/4.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.91/4.10  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.91/4.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.91/4.10  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.91/4.10  tff('#skF_5', type, '#skF_5': $i).
% 9.91/4.10  tff('#skF_6', type, '#skF_6': $i).
% 9.91/4.10  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.91/4.10  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.91/4.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.91/4.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.91/4.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.91/4.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.91/4.10  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.91/4.10  
% 10.10/4.12  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.10/4.12  tff(f_77, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 10.10/4.12  tff(f_83, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 10.10/4.12  tff(f_79, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 10.10/4.12  tff(f_87, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 10.10/4.12  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 10.10/4.12  tff(f_85, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 10.10/4.12  tff(f_41, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 10.10/4.12  tff(f_75, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 10.10/4.12  tff(f_81, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 10.10/4.12  tff(f_59, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 10.10/4.12  tff(f_39, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 10.10/4.12  tff(f_73, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 10.10/4.12  tff(f_90, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.10/4.12  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.10/4.12  tff(c_38, plain, (![A_26]: (k2_xboole_0(A_26, k1_xboole_0)=A_26)), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.10/4.12  tff(c_44, plain, (![A_30]: (k4_xboole_0(A_30, k1_xboole_0)=A_30)), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.10/4.12  tff(c_96, plain, (![B_39, A_40]: (k3_xboole_0(B_39, A_40)=k3_xboole_0(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.10/4.12  tff(c_40, plain, (![A_27]: (k3_xboole_0(A_27, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.10/4.12  tff(c_112, plain, (![A_40]: (k3_xboole_0(k1_xboole_0, A_40)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_96, c_40])).
% 10.10/4.12  tff(c_336, plain, (![A_62, B_63]: (k4_xboole_0(A_62, k3_xboole_0(A_62, B_63))=k4_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.10/4.12  tff(c_351, plain, (![A_40]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_40))), inference(superposition, [status(thm), theory('equality')], [c_112, c_336])).
% 10.10/4.12  tff(c_366, plain, (![A_40]: (k4_xboole_0(k1_xboole_0, A_40)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_351])).
% 10.10/4.12  tff(c_143, plain, (![B_41, A_42]: (k2_xboole_0(B_41, A_42)=k2_xboole_0(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.10/4.12  tff(c_181, plain, (![A_26]: (k2_xboole_0(k1_xboole_0, A_26)=A_26)), inference(superposition, [status(thm), theory('equality')], [c_38, c_143])).
% 10.10/4.12  tff(c_429, plain, (![A_68, B_69]: (k4_xboole_0(k2_xboole_0(A_68, B_69), B_69)=k4_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.10/4.12  tff(c_448, plain, (![A_26]: (k4_xboole_0(k1_xboole_0, A_26)=k4_xboole_0(A_26, A_26))), inference(superposition, [status(thm), theory('equality')], [c_181, c_429])).
% 10.10/4.12  tff(c_465, plain, (![A_26]: (k4_xboole_0(A_26, A_26)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_366, c_448])).
% 10.10/4.12  tff(c_24, plain, (![A_11]: (k3_xboole_0(A_11, A_11)=A_11)), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.10/4.12  tff(c_885, plain, (![A_99, B_100, C_101]: (k3_xboole_0(k3_xboole_0(A_99, B_100), C_101)=k3_xboole_0(A_99, k3_xboole_0(B_100, C_101)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.10/4.12  tff(c_1073, plain, (![A_107, C_108]: (k3_xboole_0(A_107, k3_xboole_0(A_107, C_108))=k3_xboole_0(A_107, C_108))), inference(superposition, [status(thm), theory('equality')], [c_24, c_885])).
% 10.10/4.12  tff(c_354, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k3_xboole_0(B_4, A_3))=k4_xboole_0(A_3, B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_336])).
% 10.10/4.12  tff(c_1101, plain, (![A_107, C_108]: (k4_xboole_0(k3_xboole_0(A_107, C_108), k3_xboole_0(A_107, C_108))=k4_xboole_0(k3_xboole_0(A_107, C_108), A_107))), inference(superposition, [status(thm), theory('equality')], [c_1073, c_354])).
% 10.10/4.12  tff(c_1159, plain, (![A_109, C_110]: (k4_xboole_0(k3_xboole_0(A_109, C_110), A_109)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_465, c_1101])).
% 10.10/4.12  tff(c_42, plain, (![A_28, B_29]: (k2_xboole_0(A_28, k4_xboole_0(B_29, A_28))=k2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.10/4.12  tff(c_1167, plain, (![A_109, C_110]: (k2_xboole_0(A_109, k3_xboole_0(A_109, C_110))=k2_xboole_0(A_109, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1159, c_42])).
% 10.10/4.12  tff(c_1207, plain, (![A_109, C_110]: (k2_xboole_0(A_109, k3_xboole_0(A_109, C_110))=A_109)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1167])).
% 10.10/4.12  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.10/4.12  tff(c_48, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k3_xboole_0(A_33, B_34))=k4_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.10/4.12  tff(c_30, plain, (![A_13, B_14]: (r2_hidden('#skF_3'(A_13, B_14), A_13) | r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.10/4.12  tff(c_403, plain, (![A_65, B_66]: (r2_hidden('#skF_3'(A_65, B_66), B_66) | r1_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.10/4.12  tff(c_8, plain, (![D_10, B_6, A_5]: (~r2_hidden(D_10, B_6) | ~r2_hidden(D_10, k4_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.10/4.12  tff(c_10708, plain, (![A_269, A_270, B_271]: (~r2_hidden('#skF_3'(A_269, k4_xboole_0(A_270, B_271)), B_271) | r1_xboole_0(A_269, k4_xboole_0(A_270, B_271)))), inference(resolution, [status(thm)], [c_403, c_8])).
% 10.10/4.12  tff(c_10809, plain, (![A_272, A_273]: (r1_xboole_0(A_272, k4_xboole_0(A_273, A_272)))), inference(resolution, [status(thm)], [c_30, c_10708])).
% 10.10/4.12  tff(c_1691, plain, (![A_132, B_133, C_134]: (r2_hidden('#skF_1'(A_132, B_133, C_134), A_132) | r2_hidden('#skF_2'(A_132, B_133, C_134), C_134) | k4_xboole_0(A_132, B_133)=C_134)), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.10/4.12  tff(c_20, plain, (![A_5, B_6, C_7]: (~r2_hidden('#skF_1'(A_5, B_6, C_7), B_6) | r2_hidden('#skF_2'(A_5, B_6, C_7), C_7) | k4_xboole_0(A_5, B_6)=C_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.10/4.12  tff(c_1694, plain, (![A_132, C_134]: (r2_hidden('#skF_2'(A_132, A_132, C_134), C_134) | k4_xboole_0(A_132, A_132)=C_134)), inference(resolution, [status(thm)], [c_1691, c_20])).
% 10.10/4.12  tff(c_1937, plain, (![A_143, C_144]: (r2_hidden('#skF_2'(A_143, A_143, C_144), C_144) | k1_xboole_0=C_144)), inference(demodulation, [status(thm), theory('equality')], [c_465, c_1694])).
% 10.10/4.12  tff(c_34, plain, (![A_18, B_19, C_22]: (~r1_xboole_0(A_18, B_19) | ~r2_hidden(C_22, k3_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.10/4.12  tff(c_1961, plain, (![A_18, B_19]: (~r1_xboole_0(A_18, B_19) | k3_xboole_0(A_18, B_19)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1937, c_34])).
% 10.10/4.12  tff(c_10996, plain, (![A_276, A_277]: (k3_xboole_0(A_276, k4_xboole_0(A_277, A_276))=k1_xboole_0)), inference(resolution, [status(thm)], [c_10809, c_1961])).
% 10.10/4.12  tff(c_11127, plain, (![A_276, A_277]: (k4_xboole_0(A_276, k4_xboole_0(A_277, A_276))=k4_xboole_0(A_276, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10996, c_48])).
% 10.10/4.12  tff(c_11254, plain, (![A_276, A_277]: (k4_xboole_0(A_276, k4_xboole_0(A_277, A_276))=A_276)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_11127])).
% 10.10/4.12  tff(c_499, plain, (![A_71, B_72]: (k2_xboole_0(A_71, k4_xboole_0(B_72, A_71))=k2_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.10/4.12  tff(c_46, plain, (![A_31, B_32]: (k4_xboole_0(k2_xboole_0(A_31, B_32), B_32)=k4_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.10/4.12  tff(c_505, plain, (![A_71, B_72]: (k4_xboole_0(k2_xboole_0(A_71, B_72), k4_xboole_0(B_72, A_71))=k4_xboole_0(A_71, k4_xboole_0(B_72, A_71)))), inference(superposition, [status(thm), theory('equality')], [c_499, c_46])).
% 10.10/4.12  tff(c_22916, plain, (![A_409, B_410]: (k4_xboole_0(k2_xboole_0(A_409, B_410), k4_xboole_0(B_410, A_409))=A_409)), inference(demodulation, [status(thm), theory('equality')], [c_11254, c_505])).
% 10.10/4.12  tff(c_23228, plain, (![A_33, B_34]: (k4_xboole_0(k2_xboole_0(k3_xboole_0(A_33, B_34), A_33), k4_xboole_0(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(superposition, [status(thm), theory('equality')], [c_48, c_22916])).
% 10.10/4.12  tff(c_23320, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k4_xboole_0(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(demodulation, [status(thm), theory('equality')], [c_1207, c_2, c_23228])).
% 10.10/4.12  tff(c_50, plain, (k4_xboole_0('#skF_5', k4_xboole_0('#skF_5', '#skF_6'))!=k3_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.10/4.12  tff(c_51, plain, (k4_xboole_0('#skF_5', k4_xboole_0('#skF_5', '#skF_6'))!=k3_xboole_0('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_50])).
% 10.10/4.12  tff(c_29409, plain, (k3_xboole_0('#skF_5', '#skF_6')!=k3_xboole_0('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_23320, c_51])).
% 10.10/4.12  tff(c_29412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_29409])).
% 10.10/4.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.10/4.12  
% 10.10/4.12  Inference rules
% 10.10/4.12  ----------------------
% 10.10/4.12  #Ref     : 0
% 10.10/4.12  #Sup     : 7311
% 10.10/4.12  #Fact    : 0
% 10.10/4.12  #Define  : 0
% 10.10/4.12  #Split   : 1
% 10.10/4.12  #Chain   : 0
% 10.10/4.12  #Close   : 0
% 10.10/4.12  
% 10.10/4.12  Ordering : KBO
% 10.10/4.12  
% 10.10/4.12  Simplification rules
% 10.10/4.12  ----------------------
% 10.10/4.12  #Subsume      : 605
% 10.10/4.12  #Demod        : 8273
% 10.10/4.12  #Tautology    : 4626
% 10.10/4.12  #SimpNegUnit  : 136
% 10.10/4.12  #BackRed      : 2
% 10.10/4.12  
% 10.10/4.12  #Partial instantiations: 0
% 10.10/4.12  #Strategies tried      : 1
% 10.10/4.12  
% 10.10/4.12  Timing (in seconds)
% 10.10/4.12  ----------------------
% 10.10/4.12  Preprocessing        : 0.29
% 10.10/4.12  Parsing              : 0.16
% 10.10/4.12  CNF conversion       : 0.02
% 10.10/4.12  Main loop            : 3.04
% 10.10/4.12  Inferencing          : 0.62
% 10.10/4.12  Reduction            : 1.68
% 10.10/4.12  Demodulation         : 1.48
% 10.10/4.12  BG Simplification    : 0.07
% 10.10/4.12  Subsumption          : 0.53
% 10.10/4.12  Abstraction          : 0.12
% 10.10/4.12  MUC search           : 0.00
% 10.10/4.12  Cooper               : 0.00
% 10.10/4.12  Total                : 3.37
% 10.10/4.12  Index Insertion      : 0.00
% 10.10/4.12  Index Deletion       : 0.00
% 10.10/4.12  Index Matching       : 0.00
% 10.10/4.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
