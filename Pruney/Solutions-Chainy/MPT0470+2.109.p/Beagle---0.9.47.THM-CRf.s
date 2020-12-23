%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:16 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 116 expanded)
%              Number of leaves         :   36 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  124 ( 190 expanded)
%              Number of equality atoms :   29 (  47 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_40,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_104,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_101,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_77,axiom,(
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

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_85,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_46,plain,
    ( k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_68,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_48,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_30,plain,(
    ! [A_23] :
      ( r2_hidden('#skF_1'(A_23),A_23)
      | v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_115,plain,(
    ! [A_68,C_69,B_70] :
      ( ~ r2_hidden(A_68,C_69)
      | ~ r1_xboole_0(k2_tarski(A_68,B_70),C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_130,plain,(
    ! [A_74] : ~ r2_hidden(A_74,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_115])).

tff(c_135,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_30,c_130])).

tff(c_32,plain,(
    ! [A_41,B_42] :
      ( v1_relat_1(k5_relat_1(A_41,B_42))
      | ~ v1_relat_1(B_42)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_44,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_42,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_344,plain,(
    ! [A_95,B_96] :
      ( k1_relat_1(k5_relat_1(A_95,B_96)) = k1_relat_1(A_95)
      | ~ r1_tarski(k2_relat_1(A_95),k1_relat_1(B_96))
      | ~ v1_relat_1(B_96)
      | ~ v1_relat_1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_353,plain,(
    ! [B_96] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_96)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_96))
      | ~ v1_relat_1(B_96)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_344])).

tff(c_360,plain,(
    ! [B_97] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_97)) = k1_xboole_0
      | ~ v1_relat_1(B_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_12,c_44,c_353])).

tff(c_34,plain,(
    ! [A_43] :
      ( ~ v1_xboole_0(k1_relat_1(A_43))
      | ~ v1_relat_1(A_43)
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_369,plain,(
    ! [B_97] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_97))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_97))
      | ~ v1_relat_1(B_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_34])).

tff(c_415,plain,(
    ! [B_105] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_105))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_105))
      | ~ v1_relat_1(B_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_369])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_425,plain,(
    ! [B_106] :
      ( k5_relat_1(k1_xboole_0,B_106) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_106))
      | ~ v1_relat_1(B_106) ) ),
    inference(resolution,[status(thm)],[c_415,c_4])).

tff(c_432,plain,(
    ! [B_42] :
      ( k5_relat_1(k1_xboole_0,B_42) = k1_xboole_0
      | ~ v1_relat_1(B_42)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_32,c_425])).

tff(c_438,plain,(
    ! [B_107] :
      ( k5_relat_1(k1_xboole_0,B_107) = k1_xboole_0
      | ~ v1_relat_1(B_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_432])).

tff(c_447,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_438])).

tff(c_454,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_447])).

tff(c_455,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_506,plain,(
    ! [A_118,C_119,B_120] :
      ( ~ r2_hidden(A_118,C_119)
      | ~ r1_xboole_0(k2_tarski(A_118,B_120),C_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_512,plain,(
    ! [A_121] : ~ r2_hidden(A_121,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_506])).

tff(c_517,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_30,c_512])).

tff(c_533,plain,(
    ! [A_127,B_128] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_127,B_128)),k2_relat_1(B_128))
      | ~ v1_relat_1(B_128)
      | ~ v1_relat_1(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_541,plain,(
    ! [A_127] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_127,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_533])).

tff(c_547,plain,(
    ! [A_129] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_129,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_541])).

tff(c_483,plain,(
    ! [B_115,A_116] :
      ( B_115 = A_116
      | ~ r1_tarski(B_115,A_116)
      | ~ r1_tarski(A_116,B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_492,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_483])).

tff(c_557,plain,(
    ! [A_130] :
      ( k2_relat_1(k5_relat_1(A_130,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_130) ) ),
    inference(resolution,[status(thm)],[c_547,c_492])).

tff(c_36,plain,(
    ! [A_44] :
      ( ~ v1_xboole_0(k2_relat_1(A_44))
      | ~ v1_relat_1(A_44)
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_572,plain,(
    ! [A_130] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_130,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_130,k1_xboole_0))
      | ~ v1_relat_1(A_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_557,c_36])).

tff(c_592,plain,(
    ! [A_135] :
      ( ~ v1_relat_1(k5_relat_1(A_135,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_135,k1_xboole_0))
      | ~ v1_relat_1(A_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_572])).

tff(c_597,plain,(
    ! [A_136] :
      ( k5_relat_1(A_136,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_136,k1_xboole_0))
      | ~ v1_relat_1(A_136) ) ),
    inference(resolution,[status(thm)],[c_592,c_4])).

tff(c_601,plain,(
    ! [A_41] :
      ( k5_relat_1(A_41,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_41) ) ),
    inference(resolution,[status(thm)],[c_32,c_597])).

tff(c_605,plain,(
    ! [A_137] :
      ( k5_relat_1(A_137,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_601])).

tff(c_614,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_605])).

tff(c_620,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_455,c_614])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:07:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.34  
% 2.47/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.34  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.47/1.34  
% 2.47/1.34  %Foreground sorts:
% 2.47/1.34  
% 2.47/1.34  
% 2.47/1.34  %Background operators:
% 2.47/1.34  
% 2.47/1.34  
% 2.47/1.34  %Foreground operators:
% 2.47/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.34  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.47/1.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.47/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.34  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.47/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.47/1.34  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.47/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.47/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.47/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.47/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.47/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.47/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.47/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.47/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.47/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.47/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.47/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.47/1.34  
% 2.73/1.36  tff(f_111, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 2.73/1.36  tff(f_63, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.73/1.36  tff(f_40, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.73/1.36  tff(f_53, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.73/1.36  tff(f_69, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.73/1.36  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.73/1.36  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.73/1.36  tff(f_104, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.73/1.36  tff(f_101, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 2.73/1.36  tff(f_77, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.73/1.36  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.73/1.36  tff(f_92, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 2.73/1.36  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.73/1.36  tff(f_85, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.73/1.36  tff(c_46, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.73/1.36  tff(c_68, plain, (k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_46])).
% 2.73/1.36  tff(c_48, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.73/1.36  tff(c_30, plain, (![A_23]: (r2_hidden('#skF_1'(A_23), A_23) | v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.73/1.36  tff(c_14, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.73/1.36  tff(c_115, plain, (![A_68, C_69, B_70]: (~r2_hidden(A_68, C_69) | ~r1_xboole_0(k2_tarski(A_68, B_70), C_69))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.73/1.36  tff(c_130, plain, (![A_74]: (~r2_hidden(A_74, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_115])).
% 2.73/1.36  tff(c_135, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_130])).
% 2.73/1.36  tff(c_32, plain, (![A_41, B_42]: (v1_relat_1(k5_relat_1(A_41, B_42)) | ~v1_relat_1(B_42) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.73/1.36  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.73/1.36  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.73/1.36  tff(c_44, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.73/1.36  tff(c_42, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.73/1.36  tff(c_344, plain, (![A_95, B_96]: (k1_relat_1(k5_relat_1(A_95, B_96))=k1_relat_1(A_95) | ~r1_tarski(k2_relat_1(A_95), k1_relat_1(B_96)) | ~v1_relat_1(B_96) | ~v1_relat_1(A_95))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.73/1.36  tff(c_353, plain, (![B_96]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_96))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_96)) | ~v1_relat_1(B_96) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_42, c_344])).
% 2.73/1.36  tff(c_360, plain, (![B_97]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_97))=k1_xboole_0 | ~v1_relat_1(B_97))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_12, c_44, c_353])).
% 2.73/1.36  tff(c_34, plain, (![A_43]: (~v1_xboole_0(k1_relat_1(A_43)) | ~v1_relat_1(A_43) | v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.73/1.36  tff(c_369, plain, (![B_97]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_97)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_97)) | ~v1_relat_1(B_97))), inference(superposition, [status(thm), theory('equality')], [c_360, c_34])).
% 2.73/1.36  tff(c_415, plain, (![B_105]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_105)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_105)) | ~v1_relat_1(B_105))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_369])).
% 2.73/1.36  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.73/1.36  tff(c_425, plain, (![B_106]: (k5_relat_1(k1_xboole_0, B_106)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_106)) | ~v1_relat_1(B_106))), inference(resolution, [status(thm)], [c_415, c_4])).
% 2.73/1.36  tff(c_432, plain, (![B_42]: (k5_relat_1(k1_xboole_0, B_42)=k1_xboole_0 | ~v1_relat_1(B_42) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_425])).
% 2.73/1.36  tff(c_438, plain, (![B_107]: (k5_relat_1(k1_xboole_0, B_107)=k1_xboole_0 | ~v1_relat_1(B_107))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_432])).
% 2.73/1.36  tff(c_447, plain, (k5_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_438])).
% 2.73/1.36  tff(c_454, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_447])).
% 2.73/1.36  tff(c_455, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_46])).
% 2.73/1.36  tff(c_506, plain, (![A_118, C_119, B_120]: (~r2_hidden(A_118, C_119) | ~r1_xboole_0(k2_tarski(A_118, B_120), C_119))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.73/1.36  tff(c_512, plain, (![A_121]: (~r2_hidden(A_121, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_506])).
% 2.73/1.36  tff(c_517, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_512])).
% 2.73/1.36  tff(c_533, plain, (![A_127, B_128]: (r1_tarski(k2_relat_1(k5_relat_1(A_127, B_128)), k2_relat_1(B_128)) | ~v1_relat_1(B_128) | ~v1_relat_1(A_127))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.73/1.36  tff(c_541, plain, (![A_127]: (r1_tarski(k2_relat_1(k5_relat_1(A_127, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_127))), inference(superposition, [status(thm), theory('equality')], [c_42, c_533])).
% 2.73/1.36  tff(c_547, plain, (![A_129]: (r1_tarski(k2_relat_1(k5_relat_1(A_129, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_129))), inference(demodulation, [status(thm), theory('equality')], [c_517, c_541])).
% 2.73/1.36  tff(c_483, plain, (![B_115, A_116]: (B_115=A_116 | ~r1_tarski(B_115, A_116) | ~r1_tarski(A_116, B_115))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.73/1.36  tff(c_492, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_483])).
% 2.73/1.36  tff(c_557, plain, (![A_130]: (k2_relat_1(k5_relat_1(A_130, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_130))), inference(resolution, [status(thm)], [c_547, c_492])).
% 2.73/1.36  tff(c_36, plain, (![A_44]: (~v1_xboole_0(k2_relat_1(A_44)) | ~v1_relat_1(A_44) | v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.73/1.36  tff(c_572, plain, (![A_130]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_130, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_130, k1_xboole_0)) | ~v1_relat_1(A_130))), inference(superposition, [status(thm), theory('equality')], [c_557, c_36])).
% 2.73/1.36  tff(c_592, plain, (![A_135]: (~v1_relat_1(k5_relat_1(A_135, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_135, k1_xboole_0)) | ~v1_relat_1(A_135))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_572])).
% 2.73/1.36  tff(c_597, plain, (![A_136]: (k5_relat_1(A_136, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_136, k1_xboole_0)) | ~v1_relat_1(A_136))), inference(resolution, [status(thm)], [c_592, c_4])).
% 2.73/1.36  tff(c_601, plain, (![A_41]: (k5_relat_1(A_41, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_41))), inference(resolution, [status(thm)], [c_32, c_597])).
% 2.73/1.36  tff(c_605, plain, (![A_137]: (k5_relat_1(A_137, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_137))), inference(demodulation, [status(thm), theory('equality')], [c_517, c_601])).
% 2.73/1.36  tff(c_614, plain, (k5_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_605])).
% 2.73/1.36  tff(c_620, plain, $false, inference(negUnitSimplification, [status(thm)], [c_455, c_614])).
% 2.73/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.36  
% 2.73/1.36  Inference rules
% 2.73/1.36  ----------------------
% 2.73/1.36  #Ref     : 1
% 2.73/1.36  #Sup     : 118
% 2.73/1.36  #Fact    : 0
% 2.73/1.36  #Define  : 0
% 2.73/1.36  #Split   : 1
% 2.73/1.36  #Chain   : 0
% 2.73/1.36  #Close   : 0
% 2.73/1.36  
% 2.73/1.36  Ordering : KBO
% 2.73/1.36  
% 2.73/1.36  Simplification rules
% 2.73/1.36  ----------------------
% 2.73/1.36  #Subsume      : 8
% 2.73/1.36  #Demod        : 108
% 2.73/1.36  #Tautology    : 76
% 2.73/1.36  #SimpNegUnit  : 2
% 2.73/1.36  #BackRed      : 0
% 2.73/1.36  
% 2.73/1.36  #Partial instantiations: 0
% 2.73/1.36  #Strategies tried      : 1
% 2.73/1.36  
% 2.73/1.36  Timing (in seconds)
% 2.73/1.36  ----------------------
% 2.73/1.36  Preprocessing        : 0.32
% 2.73/1.37  Parsing              : 0.17
% 2.73/1.37  CNF conversion       : 0.02
% 2.73/1.37  Main loop            : 0.27
% 2.73/1.37  Inferencing          : 0.11
% 2.73/1.37  Reduction            : 0.08
% 2.73/1.37  Demodulation         : 0.06
% 2.73/1.37  BG Simplification    : 0.02
% 2.73/1.37  Subsumption          : 0.04
% 2.73/1.37  Abstraction          : 0.02
% 2.73/1.37  MUC search           : 0.00
% 2.73/1.37  Cooper               : 0.00
% 2.73/1.37  Total                : 0.62
% 2.73/1.37  Index Insertion      : 0.00
% 2.73/1.37  Index Deletion       : 0.00
% 2.73/1.37  Index Matching       : 0.00
% 2.73/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
