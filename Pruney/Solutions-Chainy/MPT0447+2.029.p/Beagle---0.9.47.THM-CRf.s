%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:31 EST 2020

% Result     : Theorem 5.99s
% Output     : CNFRefutation 6.35s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 190 expanded)
%              Number of leaves         :   30 (  79 expanded)
%              Depth                    :   14
%              Number of atoms          :  104 ( 309 expanded)
%              Number of equality atoms :   25 (  90 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_81,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k1_relat_1(A),k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_99,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k2_relat_1(A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_relat_1)).

tff(c_50,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_48,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_38,plain,(
    ! [A_36] :
      ( k2_xboole_0(k1_relat_1(A_36),k2_relat_1(A_36)) = k3_relat_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_8,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    ! [B_28,A_27] : k2_tarski(B_28,A_27) = k2_tarski(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_108,plain,(
    ! [A_57,B_58] : k3_tarski(k2_tarski(A_57,B_58)) = k2_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_123,plain,(
    ! [B_59,A_60] : k3_tarski(k2_tarski(B_59,A_60)) = k2_xboole_0(A_60,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_108])).

tff(c_36,plain,(
    ! [A_34,B_35] : k3_tarski(k2_tarski(A_34,B_35)) = k2_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_129,plain,(
    ! [B_59,A_60] : k2_xboole_0(B_59,A_60) = k2_xboole_0(A_60,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_36])).

tff(c_46,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_26,plain,(
    ! [A_22,C_24,B_23] :
      ( r1_tarski(k2_xboole_0(A_22,C_24),B_23)
      | ~ r1_tarski(C_24,B_23)
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_24,plain,(
    ! [A_20,B_21] : r1_tarski(A_20,k2_xboole_0(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_217,plain,(
    ! [B_72,A_73] :
      ( B_72 = A_73
      | ~ r1_tarski(B_72,A_73)
      | ~ r1_tarski(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_747,plain,(
    ! [A_123,B_124] :
      ( k2_xboole_0(A_123,B_124) = A_123
      | ~ r1_tarski(k2_xboole_0(A_123,B_124),A_123) ) ),
    inference(resolution,[status(thm)],[c_24,c_217])).

tff(c_754,plain,(
    ! [B_23,C_24] :
      ( k2_xboole_0(B_23,C_24) = B_23
      | ~ r1_tarski(C_24,B_23)
      | ~ r1_tarski(B_23,B_23) ) ),
    inference(resolution,[status(thm)],[c_26,c_747])).

tff(c_782,plain,(
    ! [B_125,C_126] :
      ( k2_xboole_0(B_125,C_126) = B_125
      | ~ r1_tarski(C_126,B_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_754])).

tff(c_847,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_46,c_782])).

tff(c_233,plain,(
    ! [A_20,B_21] :
      ( k2_xboole_0(A_20,B_21) = A_20
      | ~ r1_tarski(k2_xboole_0(A_20,B_21),A_20) ) ),
    inference(resolution,[status(thm)],[c_24,c_217])).

tff(c_852,plain,
    ( k2_xboole_0('#skF_2','#skF_1') = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_847,c_233])).

tff(c_907,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_129,c_852])).

tff(c_681,plain,(
    ! [A_119,B_120] :
      ( k2_xboole_0(k1_relat_1(A_119),k1_relat_1(B_120)) = k1_relat_1(k2_xboole_0(A_119,B_120))
      | ~ v1_relat_1(B_120)
      | ~ v1_relat_1(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2356,plain,(
    ! [A_167,B_168] :
      ( r1_tarski(k1_relat_1(A_167),k1_relat_1(k2_xboole_0(A_167,B_168)))
      | ~ v1_relat_1(B_168)
      | ~ v1_relat_1(A_167) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_681,c_24])).

tff(c_2383,plain,
    ( r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_907,c_2356])).

tff(c_2412,plain,(
    r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_2383])).

tff(c_778,plain,(
    ! [B_23,C_24] :
      ( k2_xboole_0(B_23,C_24) = B_23
      | ~ r1_tarski(C_24,B_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_754])).

tff(c_2426,plain,(
    k2_xboole_0(k1_relat_1('#skF_2'),k1_relat_1('#skF_1')) = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2412,c_778])).

tff(c_240,plain,(
    ! [A_74,C_75,B_76] :
      ( r1_tarski(A_74,C_75)
      | ~ r1_tarski(k2_xboole_0(A_74,B_76),C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_268,plain,(
    ! [A_77,B_78,B_79] : r1_tarski(A_77,k2_xboole_0(k2_xboole_0(A_77,B_78),B_79)) ),
    inference(resolution,[status(thm)],[c_24,c_240])).

tff(c_277,plain,(
    ! [A_60,B_59,B_79] : r1_tarski(A_60,k2_xboole_0(k2_xboole_0(B_59,A_60),B_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_268])).

tff(c_5011,plain,(
    ! [B_230] : r1_tarski(k1_relat_1('#skF_1'),k2_xboole_0(k1_relat_1('#skF_2'),B_230)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2426,c_277])).

tff(c_5044,plain,
    ( r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_5011])).

tff(c_5065,plain,(
    r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_5044])).

tff(c_1060,plain,(
    ! [A_128,B_129] :
      ( k2_xboole_0(k2_relat_1(A_128),k2_relat_1(B_129)) = k2_relat_1(k2_xboole_0(A_128,B_129))
      | ~ v1_relat_1(B_129)
      | ~ v1_relat_1(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2774,plain,(
    ! [A_179,B_180] :
      ( r1_tarski(k2_relat_1(A_179),k2_relat_1(k2_xboole_0(A_179,B_180)))
      | ~ v1_relat_1(B_180)
      | ~ v1_relat_1(A_179) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1060,c_24])).

tff(c_2801,plain,
    ( r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_907,c_2774])).

tff(c_2830,plain,(
    r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_2801])).

tff(c_2844,plain,(
    k2_xboole_0(k2_relat_1('#skF_2'),k2_relat_1('#skF_1')) = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2830,c_778])).

tff(c_316,plain,(
    ! [A_83,B_84,B_85] : r1_tarski(A_83,k2_xboole_0(B_84,k2_xboole_0(A_83,B_85))) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_268])).

tff(c_332,plain,(
    ! [B_59,B_84,A_60] : r1_tarski(B_59,k2_xboole_0(B_84,k2_xboole_0(A_60,B_59))) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_316])).

tff(c_5392,plain,(
    ! [B_237] : r1_tarski(k2_relat_1('#skF_1'),k2_xboole_0(B_237,k2_relat_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2844,c_332])).

tff(c_5423,plain,
    ( r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_5392])).

tff(c_5444,plain,(
    r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_5423])).

tff(c_518,plain,(
    ! [A_108,C_109,B_110] :
      ( r1_tarski(k2_xboole_0(A_108,C_109),B_110)
      | ~ r1_tarski(C_109,B_110)
      | ~ r1_tarski(A_108,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_5655,plain,(
    ! [A_243,B_244] :
      ( r1_tarski(k3_relat_1(A_243),B_244)
      | ~ r1_tarski(k2_relat_1(A_243),B_244)
      | ~ r1_tarski(k1_relat_1(A_243),B_244)
      | ~ v1_relat_1(A_243) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_518])).

tff(c_44,plain,(
    ~ r1_tarski(k3_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_5701,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_5655,c_44])).

tff(c_5721,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_5065,c_5444,c_5701])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:35:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.99/2.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.99/2.23  
% 5.99/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.99/2.23  %$ r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.99/2.23  
% 5.99/2.23  %Foreground sorts:
% 5.99/2.23  
% 5.99/2.23  
% 5.99/2.23  %Background operators:
% 5.99/2.23  
% 5.99/2.23  
% 5.99/2.23  %Foreground operators:
% 5.99/2.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.99/2.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.99/2.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.99/2.23  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 5.99/2.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.99/2.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.99/2.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.99/2.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.99/2.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.99/2.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.99/2.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.99/2.23  tff('#skF_2', type, '#skF_2': $i).
% 5.99/2.23  tff('#skF_1', type, '#skF_1': $i).
% 5.99/2.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.99/2.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.99/2.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.99/2.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.99/2.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.99/2.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.99/2.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.99/2.23  
% 6.35/2.24  tff(f_109, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 6.35/2.24  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 6.35/2.24  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.35/2.24  tff(f_75, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.35/2.24  tff(f_81, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.35/2.24  tff(f_71, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 6.35/2.24  tff(f_65, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.35/2.24  tff(f_92, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relat_1)).
% 6.35/2.24  tff(f_43, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 6.35/2.24  tff(f_99, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_relat_1)).
% 6.35/2.24  tff(c_50, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.35/2.24  tff(c_48, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.35/2.24  tff(c_38, plain, (![A_36]: (k2_xboole_0(k1_relat_1(A_36), k2_relat_1(A_36))=k3_relat_1(A_36) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.35/2.24  tff(c_8, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.35/2.24  tff(c_30, plain, (![B_28, A_27]: (k2_tarski(B_28, A_27)=k2_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.35/2.24  tff(c_108, plain, (![A_57, B_58]: (k3_tarski(k2_tarski(A_57, B_58))=k2_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.35/2.24  tff(c_123, plain, (![B_59, A_60]: (k3_tarski(k2_tarski(B_59, A_60))=k2_xboole_0(A_60, B_59))), inference(superposition, [status(thm), theory('equality')], [c_30, c_108])).
% 6.35/2.24  tff(c_36, plain, (![A_34, B_35]: (k3_tarski(k2_tarski(A_34, B_35))=k2_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.35/2.24  tff(c_129, plain, (![B_59, A_60]: (k2_xboole_0(B_59, A_60)=k2_xboole_0(A_60, B_59))), inference(superposition, [status(thm), theory('equality')], [c_123, c_36])).
% 6.35/2.24  tff(c_46, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.35/2.24  tff(c_26, plain, (![A_22, C_24, B_23]: (r1_tarski(k2_xboole_0(A_22, C_24), B_23) | ~r1_tarski(C_24, B_23) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.35/2.24  tff(c_24, plain, (![A_20, B_21]: (r1_tarski(A_20, k2_xboole_0(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.35/2.24  tff(c_217, plain, (![B_72, A_73]: (B_72=A_73 | ~r1_tarski(B_72, A_73) | ~r1_tarski(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.35/2.24  tff(c_747, plain, (![A_123, B_124]: (k2_xboole_0(A_123, B_124)=A_123 | ~r1_tarski(k2_xboole_0(A_123, B_124), A_123))), inference(resolution, [status(thm)], [c_24, c_217])).
% 6.35/2.24  tff(c_754, plain, (![B_23, C_24]: (k2_xboole_0(B_23, C_24)=B_23 | ~r1_tarski(C_24, B_23) | ~r1_tarski(B_23, B_23))), inference(resolution, [status(thm)], [c_26, c_747])).
% 6.35/2.24  tff(c_782, plain, (![B_125, C_126]: (k2_xboole_0(B_125, C_126)=B_125 | ~r1_tarski(C_126, B_125))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_754])).
% 6.35/2.24  tff(c_847, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_46, c_782])).
% 6.35/2.24  tff(c_233, plain, (![A_20, B_21]: (k2_xboole_0(A_20, B_21)=A_20 | ~r1_tarski(k2_xboole_0(A_20, B_21), A_20))), inference(resolution, [status(thm)], [c_24, c_217])).
% 6.35/2.24  tff(c_852, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_2' | ~r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_847, c_233])).
% 6.35/2.24  tff(c_907, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_129, c_852])).
% 6.35/2.24  tff(c_681, plain, (![A_119, B_120]: (k2_xboole_0(k1_relat_1(A_119), k1_relat_1(B_120))=k1_relat_1(k2_xboole_0(A_119, B_120)) | ~v1_relat_1(B_120) | ~v1_relat_1(A_119))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.35/2.24  tff(c_2356, plain, (![A_167, B_168]: (r1_tarski(k1_relat_1(A_167), k1_relat_1(k2_xboole_0(A_167, B_168))) | ~v1_relat_1(B_168) | ~v1_relat_1(A_167))), inference(superposition, [status(thm), theory('equality')], [c_681, c_24])).
% 6.35/2.24  tff(c_2383, plain, (r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_907, c_2356])).
% 6.35/2.24  tff(c_2412, plain, (r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_2383])).
% 6.35/2.24  tff(c_778, plain, (![B_23, C_24]: (k2_xboole_0(B_23, C_24)=B_23 | ~r1_tarski(C_24, B_23))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_754])).
% 6.35/2.24  tff(c_2426, plain, (k2_xboole_0(k1_relat_1('#skF_2'), k1_relat_1('#skF_1'))=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2412, c_778])).
% 6.35/2.24  tff(c_240, plain, (![A_74, C_75, B_76]: (r1_tarski(A_74, C_75) | ~r1_tarski(k2_xboole_0(A_74, B_76), C_75))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.35/2.24  tff(c_268, plain, (![A_77, B_78, B_79]: (r1_tarski(A_77, k2_xboole_0(k2_xboole_0(A_77, B_78), B_79)))), inference(resolution, [status(thm)], [c_24, c_240])).
% 6.35/2.24  tff(c_277, plain, (![A_60, B_59, B_79]: (r1_tarski(A_60, k2_xboole_0(k2_xboole_0(B_59, A_60), B_79)))), inference(superposition, [status(thm), theory('equality')], [c_129, c_268])).
% 6.35/2.24  tff(c_5011, plain, (![B_230]: (r1_tarski(k1_relat_1('#skF_1'), k2_xboole_0(k1_relat_1('#skF_2'), B_230)))), inference(superposition, [status(thm), theory('equality')], [c_2426, c_277])).
% 6.35/2.24  tff(c_5044, plain, (r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_38, c_5011])).
% 6.35/2.24  tff(c_5065, plain, (r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_5044])).
% 6.35/2.24  tff(c_1060, plain, (![A_128, B_129]: (k2_xboole_0(k2_relat_1(A_128), k2_relat_1(B_129))=k2_relat_1(k2_xboole_0(A_128, B_129)) | ~v1_relat_1(B_129) | ~v1_relat_1(A_128))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.35/2.24  tff(c_2774, plain, (![A_179, B_180]: (r1_tarski(k2_relat_1(A_179), k2_relat_1(k2_xboole_0(A_179, B_180))) | ~v1_relat_1(B_180) | ~v1_relat_1(A_179))), inference(superposition, [status(thm), theory('equality')], [c_1060, c_24])).
% 6.35/2.24  tff(c_2801, plain, (r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_907, c_2774])).
% 6.35/2.24  tff(c_2830, plain, (r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_2801])).
% 6.35/2.24  tff(c_2844, plain, (k2_xboole_0(k2_relat_1('#skF_2'), k2_relat_1('#skF_1'))=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2830, c_778])).
% 6.35/2.24  tff(c_316, plain, (![A_83, B_84, B_85]: (r1_tarski(A_83, k2_xboole_0(B_84, k2_xboole_0(A_83, B_85))))), inference(superposition, [status(thm), theory('equality')], [c_129, c_268])).
% 6.35/2.24  tff(c_332, plain, (![B_59, B_84, A_60]: (r1_tarski(B_59, k2_xboole_0(B_84, k2_xboole_0(A_60, B_59))))), inference(superposition, [status(thm), theory('equality')], [c_129, c_316])).
% 6.35/2.24  tff(c_5392, plain, (![B_237]: (r1_tarski(k2_relat_1('#skF_1'), k2_xboole_0(B_237, k2_relat_1('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_2844, c_332])).
% 6.35/2.24  tff(c_5423, plain, (r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_38, c_5392])).
% 6.35/2.24  tff(c_5444, plain, (r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_5423])).
% 6.35/2.24  tff(c_518, plain, (![A_108, C_109, B_110]: (r1_tarski(k2_xboole_0(A_108, C_109), B_110) | ~r1_tarski(C_109, B_110) | ~r1_tarski(A_108, B_110))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.35/2.24  tff(c_5655, plain, (![A_243, B_244]: (r1_tarski(k3_relat_1(A_243), B_244) | ~r1_tarski(k2_relat_1(A_243), B_244) | ~r1_tarski(k1_relat_1(A_243), B_244) | ~v1_relat_1(A_243))), inference(superposition, [status(thm), theory('equality')], [c_38, c_518])).
% 6.35/2.24  tff(c_44, plain, (~r1_tarski(k3_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.35/2.24  tff(c_5701, plain, (~r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_5655, c_44])).
% 6.35/2.24  tff(c_5721, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_5065, c_5444, c_5701])).
% 6.35/2.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.35/2.24  
% 6.35/2.24  Inference rules
% 6.35/2.24  ----------------------
% 6.35/2.24  #Ref     : 0
% 6.35/2.24  #Sup     : 1458
% 6.35/2.24  #Fact    : 0
% 6.35/2.24  #Define  : 0
% 6.35/2.24  #Split   : 4
% 6.35/2.24  #Chain   : 0
% 6.35/2.24  #Close   : 0
% 6.35/2.24  
% 6.35/2.24  Ordering : KBO
% 6.35/2.24  
% 6.35/2.24  Simplification rules
% 6.35/2.24  ----------------------
% 6.35/2.24  #Subsume      : 146
% 6.35/2.24  #Demod        : 781
% 6.35/2.24  #Tautology    : 699
% 6.35/2.24  #SimpNegUnit  : 0
% 6.35/2.24  #BackRed      : 8
% 6.35/2.24  
% 6.35/2.24  #Partial instantiations: 0
% 6.35/2.24  #Strategies tried      : 1
% 6.35/2.24  
% 6.35/2.24  Timing (in seconds)
% 6.35/2.24  ----------------------
% 6.35/2.25  Preprocessing        : 0.33
% 6.35/2.25  Parsing              : 0.18
% 6.35/2.25  CNF conversion       : 0.02
% 6.35/2.25  Main loop            : 1.16
% 6.35/2.25  Inferencing          : 0.33
% 6.35/2.25  Reduction            : 0.46
% 6.35/2.25  Demodulation         : 0.36
% 6.35/2.25  BG Simplification    : 0.04
% 6.35/2.25  Subsumption          : 0.25
% 6.35/2.25  Abstraction          : 0.05
% 6.35/2.25  MUC search           : 0.00
% 6.35/2.25  Cooper               : 0.00
% 6.35/2.25  Total                : 1.53
% 6.35/2.25  Index Insertion      : 0.00
% 6.35/2.25  Index Deletion       : 0.00
% 6.35/2.25  Index Matching       : 0.00
% 6.35/2.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
