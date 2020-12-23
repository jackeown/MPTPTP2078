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
% DateTime   : Thu Dec  3 09:59:16 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 130 expanded)
%              Number of leaves         :   39 (  60 expanded)
%              Depth                    :   13
%              Number of atoms          :  132 ( 214 expanded)
%              Number of equality atoms :   31 (  55 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_122,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_56,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_52,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_54,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_115,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_112,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_103,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_50,plain,
    ( k5_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_78,plain,(
    k5_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_52,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_34,plain,(
    ! [A_23] :
      ( r2_hidden('#skF_2'(A_23),A_23)
      | v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_111,plain,(
    ! [A_66,B_67,C_68] :
      ( ~ r1_xboole_0(A_66,B_67)
      | ~ r2_hidden(C_68,k3_xboole_0(A_66,B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_118,plain,(
    ! [A_9,C_68] :
      ( ~ r1_xboole_0(A_9,k1_xboole_0)
      | ~ r2_hidden(C_68,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_111])).

tff(c_122,plain,(
    ! [C_69] : ~ r2_hidden(C_69,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_118])).

tff(c_127,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_34,c_122])).

tff(c_36,plain,(
    ! [A_41,B_42] :
      ( v1_relat_1(k5_relat_1(A_41,B_42))
      | ~ v1_relat_1(B_42)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_18,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_48,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_46,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_370,plain,(
    ! [A_100,B_101] :
      ( k1_relat_1(k5_relat_1(A_100,B_101)) = k1_relat_1(A_100)
      | ~ r1_tarski(k2_relat_1(A_100),k1_relat_1(B_101))
      | ~ v1_relat_1(B_101)
      | ~ v1_relat_1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_379,plain,(
    ! [B_101] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_101)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_101))
      | ~ v1_relat_1(B_101)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_370])).

tff(c_386,plain,(
    ! [B_102] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_102)) = k1_xboole_0
      | ~ v1_relat_1(B_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_18,c_48,c_379])).

tff(c_38,plain,(
    ! [A_43] :
      ( ~ v1_xboole_0(k1_relat_1(A_43))
      | ~ v1_relat_1(A_43)
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_395,plain,(
    ! [B_102] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_102))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_102))
      | ~ v1_relat_1(B_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_386,c_38])).

tff(c_413,plain,(
    ! [B_105] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_105))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_105))
      | ~ v1_relat_1(B_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_395])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_423,plain,(
    ! [B_106] :
      ( k5_relat_1(k1_xboole_0,B_106) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_106))
      | ~ v1_relat_1(B_106) ) ),
    inference(resolution,[status(thm)],[c_413,c_4])).

tff(c_430,plain,(
    ! [B_42] :
      ( k5_relat_1(k1_xboole_0,B_42) = k1_xboole_0
      | ~ v1_relat_1(B_42)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_36,c_423])).

tff(c_436,plain,(
    ! [B_107] :
      ( k5_relat_1(k1_xboole_0,B_107) = k1_xboole_0
      | ~ v1_relat_1(B_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_430])).

tff(c_448,plain,(
    k5_relat_1(k1_xboole_0,'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_436])).

tff(c_456,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_448])).

tff(c_457,plain,(
    k5_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_524,plain,(
    ! [A_123,B_124,C_125] :
      ( ~ r1_xboole_0(A_123,B_124)
      | ~ r2_hidden(C_125,k3_xboole_0(A_123,B_124)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_531,plain,(
    ! [A_9,C_125] :
      ( ~ r1_xboole_0(A_9,k1_xboole_0)
      | ~ r2_hidden(C_125,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_524])).

tff(c_535,plain,(
    ! [C_126] : ~ r2_hidden(C_126,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_531])).

tff(c_540,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_34,c_535])).

tff(c_575,plain,(
    ! [A_138,B_139] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_138,B_139)),k2_relat_1(B_139))
      | ~ v1_relat_1(B_139)
      | ~ v1_relat_1(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_583,plain,(
    ! [A_138] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_138,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_138) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_575])).

tff(c_589,plain,(
    ! [A_140] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_140,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_583])).

tff(c_495,plain,(
    ! [B_118,A_119] :
      ( B_118 = A_119
      | ~ r1_tarski(B_118,A_119)
      | ~ r1_tarski(A_119,B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_504,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_495])).

tff(c_609,plain,(
    ! [A_143] :
      ( k2_relat_1(k5_relat_1(A_143,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_143) ) ),
    inference(resolution,[status(thm)],[c_589,c_504])).

tff(c_40,plain,(
    ! [A_44] :
      ( ~ v1_xboole_0(k2_relat_1(A_44))
      | ~ v1_relat_1(A_44)
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_624,plain,(
    ! [A_143] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_143,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_143,k1_xboole_0))
      | ~ v1_relat_1(A_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_609,c_40])).

tff(c_693,plain,(
    ! [A_153] :
      ( ~ v1_relat_1(k5_relat_1(A_153,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_153,k1_xboole_0))
      | ~ v1_relat_1(A_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_624])).

tff(c_831,plain,(
    ! [A_160] :
      ( k5_relat_1(A_160,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_160,k1_xboole_0))
      | ~ v1_relat_1(A_160) ) ),
    inference(resolution,[status(thm)],[c_693,c_4])).

tff(c_838,plain,(
    ! [A_41] :
      ( k5_relat_1(A_41,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_41) ) ),
    inference(resolution,[status(thm)],[c_36,c_831])).

tff(c_844,plain,(
    ! [A_161] :
      ( k5_relat_1(A_161,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_838])).

tff(c_856,plain,(
    k5_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_844])).

tff(c_864,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_457,c_856])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:08:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.56  
% 3.15/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.57  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4
% 3.15/1.57  
% 3.15/1.57  %Foreground sorts:
% 3.15/1.57  
% 3.15/1.57  
% 3.15/1.57  %Background operators:
% 3.15/1.57  
% 3.15/1.57  
% 3.15/1.57  %Foreground operators:
% 3.15/1.57  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.15/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.15/1.57  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.15/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.15/1.57  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.15/1.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.15/1.57  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.15/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.15/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.15/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.15/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.15/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.15/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.15/1.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.15/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.15/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.15/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.15/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.15/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.15/1.57  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.15/1.57  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.15/1.57  
% 3.15/1.58  tff(f_122, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 3.15/1.58  tff(f_74, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 3.15/1.58  tff(f_56, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.15/1.58  tff(f_52, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.15/1.58  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.15/1.58  tff(f_80, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.15/1.58  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.15/1.58  tff(f_54, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.15/1.58  tff(f_115, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.15/1.58  tff(f_112, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 3.15/1.58  tff(f_88, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 3.15/1.58  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.15/1.58  tff(f_103, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 3.15/1.58  tff(f_50, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.15/1.58  tff(f_96, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 3.15/1.58  tff(c_50, plain, (k5_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.15/1.58  tff(c_78, plain, (k5_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_50])).
% 3.15/1.58  tff(c_52, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.15/1.58  tff(c_34, plain, (![A_23]: (r2_hidden('#skF_2'(A_23), A_23) | v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.15/1.58  tff(c_20, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.15/1.58  tff(c_16, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.15/1.58  tff(c_111, plain, (![A_66, B_67, C_68]: (~r1_xboole_0(A_66, B_67) | ~r2_hidden(C_68, k3_xboole_0(A_66, B_67)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.15/1.58  tff(c_118, plain, (![A_9, C_68]: (~r1_xboole_0(A_9, k1_xboole_0) | ~r2_hidden(C_68, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_111])).
% 3.15/1.58  tff(c_122, plain, (![C_69]: (~r2_hidden(C_69, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_118])).
% 3.15/1.58  tff(c_127, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_122])).
% 3.15/1.58  tff(c_36, plain, (![A_41, B_42]: (v1_relat_1(k5_relat_1(A_41, B_42)) | ~v1_relat_1(B_42) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.15/1.58  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.15/1.58  tff(c_18, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.15/1.58  tff(c_48, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.15/1.58  tff(c_46, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.15/1.58  tff(c_370, plain, (![A_100, B_101]: (k1_relat_1(k5_relat_1(A_100, B_101))=k1_relat_1(A_100) | ~r1_tarski(k2_relat_1(A_100), k1_relat_1(B_101)) | ~v1_relat_1(B_101) | ~v1_relat_1(A_100))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.15/1.58  tff(c_379, plain, (![B_101]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_101))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_101)) | ~v1_relat_1(B_101) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_370])).
% 3.15/1.58  tff(c_386, plain, (![B_102]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_102))=k1_xboole_0 | ~v1_relat_1(B_102))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_18, c_48, c_379])).
% 3.15/1.58  tff(c_38, plain, (![A_43]: (~v1_xboole_0(k1_relat_1(A_43)) | ~v1_relat_1(A_43) | v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.15/1.58  tff(c_395, plain, (![B_102]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_102)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_102)) | ~v1_relat_1(B_102))), inference(superposition, [status(thm), theory('equality')], [c_386, c_38])).
% 3.15/1.58  tff(c_413, plain, (![B_105]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_105)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_105)) | ~v1_relat_1(B_105))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_395])).
% 3.15/1.58  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.15/1.58  tff(c_423, plain, (![B_106]: (k5_relat_1(k1_xboole_0, B_106)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_106)) | ~v1_relat_1(B_106))), inference(resolution, [status(thm)], [c_413, c_4])).
% 3.15/1.58  tff(c_430, plain, (![B_42]: (k5_relat_1(k1_xboole_0, B_42)=k1_xboole_0 | ~v1_relat_1(B_42) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_36, c_423])).
% 3.15/1.58  tff(c_436, plain, (![B_107]: (k5_relat_1(k1_xboole_0, B_107)=k1_xboole_0 | ~v1_relat_1(B_107))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_430])).
% 3.15/1.58  tff(c_448, plain, (k5_relat_1(k1_xboole_0, '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_436])).
% 3.15/1.58  tff(c_456, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_448])).
% 3.15/1.58  tff(c_457, plain, (k5_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 3.15/1.58  tff(c_524, plain, (![A_123, B_124, C_125]: (~r1_xboole_0(A_123, B_124) | ~r2_hidden(C_125, k3_xboole_0(A_123, B_124)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.15/1.58  tff(c_531, plain, (![A_9, C_125]: (~r1_xboole_0(A_9, k1_xboole_0) | ~r2_hidden(C_125, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_524])).
% 3.15/1.58  tff(c_535, plain, (![C_126]: (~r2_hidden(C_126, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_531])).
% 3.15/1.58  tff(c_540, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_535])).
% 3.15/1.58  tff(c_575, plain, (![A_138, B_139]: (r1_tarski(k2_relat_1(k5_relat_1(A_138, B_139)), k2_relat_1(B_139)) | ~v1_relat_1(B_139) | ~v1_relat_1(A_138))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.15/1.58  tff(c_583, plain, (![A_138]: (r1_tarski(k2_relat_1(k5_relat_1(A_138, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_138))), inference(superposition, [status(thm), theory('equality')], [c_46, c_575])).
% 3.15/1.58  tff(c_589, plain, (![A_140]: (r1_tarski(k2_relat_1(k5_relat_1(A_140, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_140))), inference(demodulation, [status(thm), theory('equality')], [c_540, c_583])).
% 3.15/1.58  tff(c_495, plain, (![B_118, A_119]: (B_118=A_119 | ~r1_tarski(B_118, A_119) | ~r1_tarski(A_119, B_118))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.15/1.58  tff(c_504, plain, (![A_10]: (k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_495])).
% 3.15/1.58  tff(c_609, plain, (![A_143]: (k2_relat_1(k5_relat_1(A_143, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_143))), inference(resolution, [status(thm)], [c_589, c_504])).
% 3.15/1.58  tff(c_40, plain, (![A_44]: (~v1_xboole_0(k2_relat_1(A_44)) | ~v1_relat_1(A_44) | v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.15/1.58  tff(c_624, plain, (![A_143]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_143, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_143, k1_xboole_0)) | ~v1_relat_1(A_143))), inference(superposition, [status(thm), theory('equality')], [c_609, c_40])).
% 3.15/1.58  tff(c_693, plain, (![A_153]: (~v1_relat_1(k5_relat_1(A_153, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_153, k1_xboole_0)) | ~v1_relat_1(A_153))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_624])).
% 3.15/1.58  tff(c_831, plain, (![A_160]: (k5_relat_1(A_160, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_160, k1_xboole_0)) | ~v1_relat_1(A_160))), inference(resolution, [status(thm)], [c_693, c_4])).
% 3.15/1.58  tff(c_838, plain, (![A_41]: (k5_relat_1(A_41, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_41))), inference(resolution, [status(thm)], [c_36, c_831])).
% 3.15/1.58  tff(c_844, plain, (![A_161]: (k5_relat_1(A_161, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_161))), inference(demodulation, [status(thm), theory('equality')], [c_540, c_838])).
% 3.15/1.58  tff(c_856, plain, (k5_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_844])).
% 3.15/1.58  tff(c_864, plain, $false, inference(negUnitSimplification, [status(thm)], [c_457, c_856])).
% 3.15/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.58  
% 3.15/1.58  Inference rules
% 3.15/1.58  ----------------------
% 3.15/1.58  #Ref     : 2
% 3.15/1.58  #Sup     : 168
% 3.15/1.58  #Fact    : 0
% 3.15/1.58  #Define  : 0
% 3.15/1.58  #Split   : 1
% 3.15/1.58  #Chain   : 0
% 3.15/1.58  #Close   : 0
% 3.15/1.58  
% 3.15/1.58  Ordering : KBO
% 3.15/1.58  
% 3.15/1.58  Simplification rules
% 3.15/1.58  ----------------------
% 3.15/1.58  #Subsume      : 9
% 3.15/1.58  #Demod        : 174
% 3.15/1.58  #Tautology    : 111
% 3.15/1.58  #SimpNegUnit  : 4
% 3.15/1.58  #BackRed      : 0
% 3.15/1.58  
% 3.15/1.58  #Partial instantiations: 0
% 3.15/1.58  #Strategies tried      : 1
% 3.15/1.58  
% 3.15/1.58  Timing (in seconds)
% 3.15/1.58  ----------------------
% 3.15/1.58  Preprocessing        : 0.45
% 3.15/1.59  Parsing              : 0.26
% 3.15/1.59  CNF conversion       : 0.02
% 3.15/1.59  Main loop            : 0.35
% 3.15/1.59  Inferencing          : 0.14
% 3.15/1.59  Reduction            : 0.11
% 3.15/1.59  Demodulation         : 0.08
% 3.15/1.59  BG Simplification    : 0.02
% 3.15/1.59  Subsumption          : 0.06
% 3.15/1.59  Abstraction          : 0.02
% 3.15/1.59  MUC search           : 0.00
% 3.15/1.59  Cooper               : 0.00
% 3.15/1.59  Total                : 0.84
% 3.15/1.59  Index Insertion      : 0.00
% 3.15/1.59  Index Deletion       : 0.00
% 3.15/1.59  Index Matching       : 0.00
% 3.15/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
