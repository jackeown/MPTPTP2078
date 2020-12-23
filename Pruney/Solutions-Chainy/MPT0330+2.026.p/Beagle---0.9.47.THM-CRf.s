%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:43 EST 2020

% Result     : Theorem 9.15s
% Output     : CNFRefutation 9.15s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 138 expanded)
%              Number of leaves         :   30 (  58 expanded)
%              Depth                    :   13
%              Number of atoms          :  104 ( 228 expanded)
%              Number of equality atoms :   19 (  40 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_55,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,k2_zfmisc_1(C,D))
          & r1_tarski(B,k2_zfmisc_1(E,F)) )
       => r1_tarski(k2_xboole_0(A,B),k2_zfmisc_1(k2_xboole_0(C,E),k2_xboole_0(D,F))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

tff(c_34,plain,(
    ! [C_33,A_31,B_32] : k2_xboole_0(k2_zfmisc_1(C_33,A_31),k2_zfmisc_1(C_33,B_32)) = k2_zfmisc_1(C_33,k2_xboole_0(A_31,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_18,plain,(
    ! [A_15] : r1_tarski(k1_xboole_0,A_15) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_40,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_71,plain,(
    ! [A_46,C_47,B_48] :
      ( r1_xboole_0(A_46,C_47)
      | ~ r1_tarski(A_46,k4_xboole_0(B_48,C_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_90,plain,(
    ! [C_49] : r1_xboole_0(k1_xboole_0,C_49) ),
    inference(resolution,[status(thm)],[c_18,c_71])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_93,plain,(
    ! [C_49] : r1_xboole_0(C_49,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_90,c_2])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1275,plain,(
    ! [A_128,B_129,C_130] :
      ( r1_tarski(A_128,k4_xboole_0(B_129,C_130))
      | ~ r1_xboole_0(A_128,C_130)
      | ~ r1_tarski(A_128,B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_20,plain,(
    ! [A_16,B_17] : r1_tarski(k4_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_168,plain,(
    ! [B_67,A_68] :
      ( B_67 = A_68
      | ~ r1_tarski(B_67,A_68)
      | ~ r1_tarski(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_186,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,k4_xboole_0(A_16,B_17)) ) ),
    inference(resolution,[status(thm)],[c_20,c_168])).

tff(c_1285,plain,(
    ! [B_129,C_130] :
      ( k4_xboole_0(B_129,C_130) = B_129
      | ~ r1_xboole_0(B_129,C_130)
      | ~ r1_tarski(B_129,B_129) ) ),
    inference(resolution,[status(thm)],[c_1275,c_186])).

tff(c_1323,plain,(
    ! [B_131,C_132] :
      ( k4_xboole_0(B_131,C_132) = B_131
      | ~ r1_xboole_0(B_131,C_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1285])).

tff(c_1358,plain,(
    ! [C_49] : k4_xboole_0(C_49,k1_xboole_0) = C_49 ),
    inference(resolution,[status(thm)],[c_93,c_1323])).

tff(c_22,plain,(
    ! [A_18,B_19] : k4_xboole_0(k2_xboole_0(A_18,B_19),B_19) = k4_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1365,plain,(
    ! [C_133] : k4_xboole_0(C_133,k1_xboole_0) = C_133 ),
    inference(resolution,[status(thm)],[c_93,c_1323])).

tff(c_1484,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = k2_xboole_0(A_18,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1365])).

tff(c_1513,plain,(
    ! [A_18] : k2_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1358,c_1484])).

tff(c_355,plain,(
    ! [A_86,B_87,C_88] :
      ( r1_tarski(k4_xboole_0(A_86,B_87),C_88)
      | ~ r1_tarski(A_86,k2_xboole_0(B_87,C_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_192,plain,(
    ! [A_15] :
      ( k1_xboole_0 = A_15
      | ~ r1_tarski(A_15,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_168])).

tff(c_388,plain,(
    ! [A_86,B_87] :
      ( k4_xboole_0(A_86,B_87) = k1_xboole_0
      | ~ r1_tarski(A_86,k2_xboole_0(B_87,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_355,c_192])).

tff(c_2447,plain,(
    ! [A_163,B_164] :
      ( k4_xboole_0(A_163,B_164) = k1_xboole_0
      | ~ r1_tarski(A_163,B_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1513,c_388])).

tff(c_2527,plain,(
    k4_xboole_0('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_2447])).

tff(c_26,plain,(
    ! [A_23,B_24,C_25] :
      ( r1_tarski(A_23,k2_xboole_0(B_24,C_25))
      | ~ r1_tarski(k4_xboole_0(A_23,B_24),C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3025,plain,(
    ! [C_25] :
      ( r1_tarski('#skF_1',k2_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),C_25))
      | ~ r1_tarski(k1_xboole_0,C_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2527,c_26])).

tff(c_3540,plain,(
    ! [C_188] : r1_tarski('#skF_1',k2_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),C_188)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_3025])).

tff(c_3559,plain,(
    ! [B_32] : r1_tarski('#skF_1',k2_zfmisc_1('#skF_3',k2_xboole_0('#skF_4',B_32))) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_3540])).

tff(c_1010,plain,(
    ! [A_109,B_110,C_111] :
      ( r1_tarski(A_109,k2_xboole_0(B_110,C_111))
      | ~ r1_tarski(k4_xboole_0(A_109,B_110),C_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1080,plain,(
    ! [A_16,B_17] : r1_tarski(A_16,k2_xboole_0(B_17,A_16)) ),
    inference(resolution,[status(thm)],[c_20,c_1010])).

tff(c_38,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_16,plain,(
    ! [A_12,C_14,B_13] :
      ( r1_tarski(A_12,C_14)
      | ~ r1_tarski(B_13,C_14)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10970,plain,(
    ! [A_311,B_312,C_313,A_314] :
      ( r1_tarski(A_311,k4_xboole_0(B_312,C_313))
      | ~ r1_tarski(A_311,A_314)
      | ~ r1_xboole_0(A_314,C_313)
      | ~ r1_tarski(A_314,B_312) ) ),
    inference(resolution,[status(thm)],[c_1275,c_16])).

tff(c_11234,plain,(
    ! [B_318,C_319] :
      ( r1_tarski('#skF_2',k4_xboole_0(B_318,C_319))
      | ~ r1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'),C_319)
      | ~ r1_tarski(k2_zfmisc_1('#skF_5','#skF_6'),B_318) ) ),
    inference(resolution,[status(thm)],[c_38,c_10970])).

tff(c_11255,plain,(
    ! [B_318] :
      ( r1_tarski('#skF_2',k4_xboole_0(B_318,k1_xboole_0))
      | ~ r1_tarski(k2_zfmisc_1('#skF_5','#skF_6'),B_318) ) ),
    inference(resolution,[status(thm)],[c_93,c_11234])).

tff(c_11264,plain,(
    ! [B_320] :
      ( r1_tarski('#skF_2',B_320)
      | ~ r1_tarski(k2_zfmisc_1('#skF_5','#skF_6'),B_320) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1358,c_11255])).

tff(c_11348,plain,(
    ! [B_321] : r1_tarski('#skF_2',k2_xboole_0(B_321,k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_1080,c_11264])).

tff(c_11377,plain,(
    ! [A_31] : r1_tarski('#skF_2',k2_zfmisc_1('#skF_5',k2_xboole_0(A_31,'#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_11348])).

tff(c_32,plain,(
    ! [A_31,C_33,B_32] : k2_xboole_0(k2_zfmisc_1(A_31,C_33),k2_zfmisc_1(B_32,C_33)) = k2_zfmisc_1(k2_xboole_0(A_31,B_32),C_33) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2690,plain,(
    ! [A_167,C_168,B_169,D_170] :
      ( r1_tarski(k2_xboole_0(A_167,C_168),k2_xboole_0(B_169,D_170))
      | ~ r1_tarski(C_168,D_170)
      | ~ r1_tarski(A_167,B_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20548,plain,(
    ! [A_449,C_447,B_445,C_448,A_446] :
      ( r1_tarski(k2_xboole_0(A_449,C_447),k2_zfmisc_1(k2_xboole_0(A_446,B_445),C_448))
      | ~ r1_tarski(C_447,k2_zfmisc_1(B_445,C_448))
      | ~ r1_tarski(A_449,k2_zfmisc_1(A_446,C_448)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2690])).

tff(c_36,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_20570,plain,
    ( ~ r1_tarski('#skF_2',k2_zfmisc_1('#skF_5',k2_xboole_0('#skF_4','#skF_6')))
    | ~ r1_tarski('#skF_1',k2_zfmisc_1('#skF_3',k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_20548,c_36])).

tff(c_20624,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3559,c_11377,c_20570])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:13:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.15/3.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.15/3.39  
% 9.15/3.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.15/3.39  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.15/3.39  
% 9.15/3.39  %Foreground sorts:
% 9.15/3.39  
% 9.15/3.39  
% 9.15/3.39  %Background operators:
% 9.15/3.39  
% 9.15/3.39  
% 9.15/3.39  %Foreground operators:
% 9.15/3.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.15/3.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.15/3.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.15/3.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.15/3.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.15/3.39  tff('#skF_5', type, '#skF_5': $i).
% 9.15/3.39  tff('#skF_6', type, '#skF_6': $i).
% 9.15/3.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.15/3.39  tff('#skF_2', type, '#skF_2': $i).
% 9.15/3.39  tff('#skF_3', type, '#skF_3': $i).
% 9.15/3.39  tff('#skF_1', type, '#skF_1': $i).
% 9.15/3.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.15/3.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.15/3.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.15/3.39  tff('#skF_4', type, '#skF_4': $i).
% 9.15/3.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.15/3.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.15/3.39  
% 9.15/3.40  tff(f_79, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 9.15/3.40  tff(f_55, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.15/3.40  tff(f_86, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 9.15/3.40  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 9.15/3.40  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 9.15/3.40  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.15/3.40  tff(f_73, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 9.15/3.40  tff(f_57, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 9.15/3.40  tff(f_59, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 9.15/3.40  tff(f_63, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 9.15/3.40  tff(f_67, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 9.15/3.40  tff(f_53, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 9.15/3.40  tff(f_47, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_xboole_1)).
% 9.15/3.40  tff(c_34, plain, (![C_33, A_31, B_32]: (k2_xboole_0(k2_zfmisc_1(C_33, A_31), k2_zfmisc_1(C_33, B_32))=k2_zfmisc_1(C_33, k2_xboole_0(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.15/3.40  tff(c_18, plain, (![A_15]: (r1_tarski(k1_xboole_0, A_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.15/3.40  tff(c_40, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.15/3.40  tff(c_71, plain, (![A_46, C_47, B_48]: (r1_xboole_0(A_46, C_47) | ~r1_tarski(A_46, k4_xboole_0(B_48, C_47)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.15/3.40  tff(c_90, plain, (![C_49]: (r1_xboole_0(k1_xboole_0, C_49))), inference(resolution, [status(thm)], [c_18, c_71])).
% 9.15/3.40  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.15/3.40  tff(c_93, plain, (![C_49]: (r1_xboole_0(C_49, k1_xboole_0))), inference(resolution, [status(thm)], [c_90, c_2])).
% 9.15/3.40  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.15/3.40  tff(c_1275, plain, (![A_128, B_129, C_130]: (r1_tarski(A_128, k4_xboole_0(B_129, C_130)) | ~r1_xboole_0(A_128, C_130) | ~r1_tarski(A_128, B_129))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.15/3.40  tff(c_20, plain, (![A_16, B_17]: (r1_tarski(k4_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.15/3.40  tff(c_168, plain, (![B_67, A_68]: (B_67=A_68 | ~r1_tarski(B_67, A_68) | ~r1_tarski(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.15/3.40  tff(c_186, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, k4_xboole_0(A_16, B_17)))), inference(resolution, [status(thm)], [c_20, c_168])).
% 9.15/3.40  tff(c_1285, plain, (![B_129, C_130]: (k4_xboole_0(B_129, C_130)=B_129 | ~r1_xboole_0(B_129, C_130) | ~r1_tarski(B_129, B_129))), inference(resolution, [status(thm)], [c_1275, c_186])).
% 9.15/3.40  tff(c_1323, plain, (![B_131, C_132]: (k4_xboole_0(B_131, C_132)=B_131 | ~r1_xboole_0(B_131, C_132))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1285])).
% 9.15/3.40  tff(c_1358, plain, (![C_49]: (k4_xboole_0(C_49, k1_xboole_0)=C_49)), inference(resolution, [status(thm)], [c_93, c_1323])).
% 9.15/3.40  tff(c_22, plain, (![A_18, B_19]: (k4_xboole_0(k2_xboole_0(A_18, B_19), B_19)=k4_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.15/3.40  tff(c_1365, plain, (![C_133]: (k4_xboole_0(C_133, k1_xboole_0)=C_133)), inference(resolution, [status(thm)], [c_93, c_1323])).
% 9.15/3.40  tff(c_1484, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=k2_xboole_0(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1365])).
% 9.15/3.40  tff(c_1513, plain, (![A_18]: (k2_xboole_0(A_18, k1_xboole_0)=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_1358, c_1484])).
% 9.15/3.40  tff(c_355, plain, (![A_86, B_87, C_88]: (r1_tarski(k4_xboole_0(A_86, B_87), C_88) | ~r1_tarski(A_86, k2_xboole_0(B_87, C_88)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.15/3.40  tff(c_192, plain, (![A_15]: (k1_xboole_0=A_15 | ~r1_tarski(A_15, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_168])).
% 9.15/3.40  tff(c_388, plain, (![A_86, B_87]: (k4_xboole_0(A_86, B_87)=k1_xboole_0 | ~r1_tarski(A_86, k2_xboole_0(B_87, k1_xboole_0)))), inference(resolution, [status(thm)], [c_355, c_192])).
% 9.15/3.40  tff(c_2447, plain, (![A_163, B_164]: (k4_xboole_0(A_163, B_164)=k1_xboole_0 | ~r1_tarski(A_163, B_164))), inference(demodulation, [status(thm), theory('equality')], [c_1513, c_388])).
% 9.15/3.40  tff(c_2527, plain, (k4_xboole_0('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_2447])).
% 9.15/3.40  tff(c_26, plain, (![A_23, B_24, C_25]: (r1_tarski(A_23, k2_xboole_0(B_24, C_25)) | ~r1_tarski(k4_xboole_0(A_23, B_24), C_25))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.15/3.40  tff(c_3025, plain, (![C_25]: (r1_tarski('#skF_1', k2_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), C_25)) | ~r1_tarski(k1_xboole_0, C_25))), inference(superposition, [status(thm), theory('equality')], [c_2527, c_26])).
% 9.15/3.40  tff(c_3540, plain, (![C_188]: (r1_tarski('#skF_1', k2_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), C_188)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_3025])).
% 9.15/3.40  tff(c_3559, plain, (![B_32]: (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', k2_xboole_0('#skF_4', B_32))))), inference(superposition, [status(thm), theory('equality')], [c_34, c_3540])).
% 9.15/3.40  tff(c_1010, plain, (![A_109, B_110, C_111]: (r1_tarski(A_109, k2_xboole_0(B_110, C_111)) | ~r1_tarski(k4_xboole_0(A_109, B_110), C_111))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.15/3.40  tff(c_1080, plain, (![A_16, B_17]: (r1_tarski(A_16, k2_xboole_0(B_17, A_16)))), inference(resolution, [status(thm)], [c_20, c_1010])).
% 9.15/3.40  tff(c_38, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.15/3.40  tff(c_16, plain, (![A_12, C_14, B_13]: (r1_tarski(A_12, C_14) | ~r1_tarski(B_13, C_14) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.15/3.40  tff(c_10970, plain, (![A_311, B_312, C_313, A_314]: (r1_tarski(A_311, k4_xboole_0(B_312, C_313)) | ~r1_tarski(A_311, A_314) | ~r1_xboole_0(A_314, C_313) | ~r1_tarski(A_314, B_312))), inference(resolution, [status(thm)], [c_1275, c_16])).
% 9.15/3.40  tff(c_11234, plain, (![B_318, C_319]: (r1_tarski('#skF_2', k4_xboole_0(B_318, C_319)) | ~r1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'), C_319) | ~r1_tarski(k2_zfmisc_1('#skF_5', '#skF_6'), B_318))), inference(resolution, [status(thm)], [c_38, c_10970])).
% 9.15/3.40  tff(c_11255, plain, (![B_318]: (r1_tarski('#skF_2', k4_xboole_0(B_318, k1_xboole_0)) | ~r1_tarski(k2_zfmisc_1('#skF_5', '#skF_6'), B_318))), inference(resolution, [status(thm)], [c_93, c_11234])).
% 9.15/3.40  tff(c_11264, plain, (![B_320]: (r1_tarski('#skF_2', B_320) | ~r1_tarski(k2_zfmisc_1('#skF_5', '#skF_6'), B_320))), inference(demodulation, [status(thm), theory('equality')], [c_1358, c_11255])).
% 9.15/3.40  tff(c_11348, plain, (![B_321]: (r1_tarski('#skF_2', k2_xboole_0(B_321, k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(resolution, [status(thm)], [c_1080, c_11264])).
% 9.15/3.40  tff(c_11377, plain, (![A_31]: (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', k2_xboole_0(A_31, '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_34, c_11348])).
% 9.15/3.40  tff(c_32, plain, (![A_31, C_33, B_32]: (k2_xboole_0(k2_zfmisc_1(A_31, C_33), k2_zfmisc_1(B_32, C_33))=k2_zfmisc_1(k2_xboole_0(A_31, B_32), C_33))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.15/3.40  tff(c_2690, plain, (![A_167, C_168, B_169, D_170]: (r1_tarski(k2_xboole_0(A_167, C_168), k2_xboole_0(B_169, D_170)) | ~r1_tarski(C_168, D_170) | ~r1_tarski(A_167, B_169))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.15/3.40  tff(c_20548, plain, (![A_449, C_447, B_445, C_448, A_446]: (r1_tarski(k2_xboole_0(A_449, C_447), k2_zfmisc_1(k2_xboole_0(A_446, B_445), C_448)) | ~r1_tarski(C_447, k2_zfmisc_1(B_445, C_448)) | ~r1_tarski(A_449, k2_zfmisc_1(A_446, C_448)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_2690])).
% 9.15/3.40  tff(c_36, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.15/3.40  tff(c_20570, plain, (~r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', k2_xboole_0('#skF_4', '#skF_6'))) | ~r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', k2_xboole_0('#skF_4', '#skF_6')))), inference(resolution, [status(thm)], [c_20548, c_36])).
% 9.15/3.40  tff(c_20624, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3559, c_11377, c_20570])).
% 9.15/3.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.15/3.40  
% 9.15/3.40  Inference rules
% 9.15/3.40  ----------------------
% 9.15/3.40  #Ref     : 0
% 9.15/3.40  #Sup     : 5148
% 9.15/3.40  #Fact    : 0
% 9.15/3.40  #Define  : 0
% 9.15/3.40  #Split   : 6
% 9.15/3.40  #Chain   : 0
% 9.15/3.40  #Close   : 0
% 9.15/3.40  
% 9.15/3.40  Ordering : KBO
% 9.15/3.40  
% 9.15/3.40  Simplification rules
% 9.15/3.40  ----------------------
% 9.15/3.40  #Subsume      : 674
% 9.15/3.40  #Demod        : 4393
% 9.15/3.40  #Tautology    : 2895
% 9.15/3.40  #SimpNegUnit  : 12
% 9.15/3.40  #BackRed      : 11
% 9.15/3.40  
% 9.15/3.40  #Partial instantiations: 0
% 9.15/3.40  #Strategies tried      : 1
% 9.15/3.40  
% 9.15/3.40  Timing (in seconds)
% 9.15/3.40  ----------------------
% 9.15/3.41  Preprocessing        : 0.31
% 9.15/3.41  Parsing              : 0.17
% 9.15/3.41  CNF conversion       : 0.02
% 9.15/3.41  Main loop            : 2.33
% 9.15/3.41  Inferencing          : 0.53
% 9.15/3.41  Reduction            : 1.06
% 9.15/3.41  Demodulation         : 0.86
% 9.15/3.41  BG Simplification    : 0.06
% 9.15/3.41  Subsumption          : 0.54
% 9.15/3.41  Abstraction          : 0.08
% 9.15/3.41  MUC search           : 0.00
% 9.15/3.41  Cooper               : 0.00
% 9.15/3.41  Total                : 2.68
% 9.15/3.41  Index Insertion      : 0.00
% 9.15/3.41  Index Deletion       : 0.00
% 9.15/3.41  Index Matching       : 0.00
% 9.15/3.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
