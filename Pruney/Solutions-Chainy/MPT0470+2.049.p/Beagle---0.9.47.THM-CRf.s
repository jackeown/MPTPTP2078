%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:07 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 118 expanded)
%              Number of leaves         :   30 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  137 ( 208 expanded)
%              Number of equality atoms :   32 (  48 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_36,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_58,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_105,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_102,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_38,plain,
    ( k5_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_66,plain,(
    k5_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_10,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_49,plain,(
    ! [A_26] :
      ( v1_relat_1(A_26)
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_53,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_49])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( v1_relat_1(k5_relat_1(A_16,B_17))
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_87,plain,(
    ! [A_41,B_42] :
      ( r2_hidden('#skF_2'(A_41,B_42),B_42)
      | r1_xboole_0(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,(
    ! [B_43,A_44] :
      ( ~ v1_xboole_0(B_43)
      | r1_xboole_0(A_44,B_43) ) ),
    inference(resolution,[status(thm)],[c_87,c_2])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_107,plain,(
    ! [A_49,B_50] :
      ( k3_xboole_0(A_49,B_50) = k1_xboole_0
      | ~ v1_xboole_0(B_50) ) ),
    inference(resolution,[status(thm)],[c_92,c_6])).

tff(c_110,plain,(
    ! [A_49] : k3_xboole_0(A_49,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_107])).

tff(c_36,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_173,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_64,B_65)),k1_relat_1(A_64))
      | ~ v1_relat_1(B_65)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_179,plain,(
    ! [B_65] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_65)),k1_xboole_0)
      | ~ v1_relat_1(B_65)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_173])).

tff(c_183,plain,(
    ! [B_66] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_66)),k1_xboole_0)
      | ~ v1_relat_1(B_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_179])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,B_14) = A_13
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_186,plain,(
    ! [B_66] :
      ( k3_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,B_66)),k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,B_66))
      | ~ v1_relat_1(B_66) ) ),
    inference(resolution,[status(thm)],[c_183,c_20])).

tff(c_189,plain,(
    ! [B_67] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_67)) = k1_xboole_0
      | ~ v1_relat_1(B_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_186])).

tff(c_26,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(k1_relat_1(A_18))
      | ~ v1_relat_1(A_18)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_204,plain,(
    ! [B_67] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_67))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_67))
      | ~ v1_relat_1(B_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_26])).

tff(c_357,plain,(
    ! [B_85] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_85))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_85))
      | ~ v1_relat_1(B_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_204])).

tff(c_12,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_372,plain,(
    ! [B_86] :
      ( k5_relat_1(k1_xboole_0,B_86) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_86))
      | ~ v1_relat_1(B_86) ) ),
    inference(resolution,[status(thm)],[c_357,c_12])).

tff(c_376,plain,(
    ! [B_17] :
      ( k5_relat_1(k1_xboole_0,B_17) = k1_xboole_0
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_372])).

tff(c_380,plain,(
    ! [B_87] :
      ( k5_relat_1(k1_xboole_0,B_87) = k1_xboole_0
      | ~ v1_relat_1(B_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_376])).

tff(c_389,plain,(
    k5_relat_1(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_380])).

tff(c_395,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_389])).

tff(c_396,plain,(
    k5_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_448,plain,(
    ! [A_105,B_106] :
      ( r2_hidden('#skF_2'(A_105,B_106),B_106)
      | r1_xboole_0(A_105,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_453,plain,(
    ! [B_107,A_108] :
      ( ~ v1_xboole_0(B_107)
      | r1_xboole_0(A_108,B_107) ) ),
    inference(resolution,[status(thm)],[c_448,c_2])).

tff(c_468,plain,(
    ! [A_112,B_113] :
      ( k3_xboole_0(A_112,B_113) = k1_xboole_0
      | ~ v1_xboole_0(B_113) ) ),
    inference(resolution,[status(thm)],[c_453,c_6])).

tff(c_471,plain,(
    ! [A_112] : k3_xboole_0(A_112,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_468])).

tff(c_34,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_497,plain,(
    ! [A_118,B_119] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_118,B_119)),k2_relat_1(B_119))
      | ~ v1_relat_1(B_119)
      | ~ v1_relat_1(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_506,plain,(
    ! [A_118] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_118,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_497])).

tff(c_517,plain,(
    ! [A_120] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_120,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_506])).

tff(c_520,plain,(
    ! [A_120] :
      ( k3_xboole_0(k2_relat_1(k5_relat_1(A_120,k1_xboole_0)),k1_xboole_0) = k2_relat_1(k5_relat_1(A_120,k1_xboole_0))
      | ~ v1_relat_1(A_120) ) ),
    inference(resolution,[status(thm)],[c_517,c_20])).

tff(c_523,plain,(
    ! [A_121] :
      ( k2_relat_1(k5_relat_1(A_121,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_520])).

tff(c_28,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0(k2_relat_1(A_19))
      | ~ v1_relat_1(A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_538,plain,(
    ! [A_121] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_121,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_121,k1_xboole_0))
      | ~ v1_relat_1(A_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_28])).

tff(c_635,plain,(
    ! [A_129] :
      ( ~ v1_relat_1(k5_relat_1(A_129,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_129,k1_xboole_0))
      | ~ v1_relat_1(A_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_538])).

tff(c_698,plain,(
    ! [A_133] :
      ( k5_relat_1(A_133,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_133,k1_xboole_0))
      | ~ v1_relat_1(A_133) ) ),
    inference(resolution,[status(thm)],[c_635,c_12])).

tff(c_702,plain,(
    ! [A_16] :
      ( k5_relat_1(A_16,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_16) ) ),
    inference(resolution,[status(thm)],[c_24,c_698])).

tff(c_706,plain,(
    ! [A_134] :
      ( k5_relat_1(A_134,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_702])).

tff(c_715,plain,(
    k5_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_706])).

tff(c_721,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_396,c_715])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:44:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.03/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.54  
% 3.16/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.54  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 3.16/1.54  
% 3.16/1.54  %Foreground sorts:
% 3.16/1.54  
% 3.16/1.54  
% 3.16/1.54  %Background operators:
% 3.16/1.54  
% 3.16/1.54  
% 3.16/1.54  %Foreground operators:
% 3.16/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.16/1.54  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.16/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.16/1.54  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.16/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.16/1.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.16/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.16/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.16/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.54  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.16/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.16/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.16/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.16/1.54  
% 3.24/1.57  tff(f_112, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 3.24/1.57  tff(f_36, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.24/1.57  tff(f_66, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.24/1.57  tff(f_72, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.24/1.57  tff(f_58, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.24/1.57  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.24/1.57  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.24/1.57  tff(f_105, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.24/1.57  tff(f_95, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 3.24/1.57  tff(f_62, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.24/1.57  tff(f_80, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 3.24/1.57  tff(f_40, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.24/1.57  tff(f_102, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 3.24/1.57  tff(f_88, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 3.24/1.57  tff(c_38, plain, (k5_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.24/1.57  tff(c_66, plain, (k5_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_38])).
% 3.24/1.57  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.24/1.57  tff(c_10, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.24/1.57  tff(c_49, plain, (![A_26]: (v1_relat_1(A_26) | ~v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.24/1.57  tff(c_53, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_49])).
% 3.24/1.57  tff(c_24, plain, (![A_16, B_17]: (v1_relat_1(k5_relat_1(A_16, B_17)) | ~v1_relat_1(B_17) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.24/1.57  tff(c_87, plain, (![A_41, B_42]: (r2_hidden('#skF_2'(A_41, B_42), B_42) | r1_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.24/1.57  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.24/1.57  tff(c_92, plain, (![B_43, A_44]: (~v1_xboole_0(B_43) | r1_xboole_0(A_44, B_43))), inference(resolution, [status(thm)], [c_87, c_2])).
% 3.24/1.57  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.24/1.57  tff(c_107, plain, (![A_49, B_50]: (k3_xboole_0(A_49, B_50)=k1_xboole_0 | ~v1_xboole_0(B_50))), inference(resolution, [status(thm)], [c_92, c_6])).
% 3.24/1.57  tff(c_110, plain, (![A_49]: (k3_xboole_0(A_49, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_107])).
% 3.24/1.57  tff(c_36, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.24/1.57  tff(c_173, plain, (![A_64, B_65]: (r1_tarski(k1_relat_1(k5_relat_1(A_64, B_65)), k1_relat_1(A_64)) | ~v1_relat_1(B_65) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.24/1.57  tff(c_179, plain, (![B_65]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_65)), k1_xboole_0) | ~v1_relat_1(B_65) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_173])).
% 3.24/1.57  tff(c_183, plain, (![B_66]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_66)), k1_xboole_0) | ~v1_relat_1(B_66))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_179])).
% 3.24/1.57  tff(c_20, plain, (![A_13, B_14]: (k3_xboole_0(A_13, B_14)=A_13 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.24/1.57  tff(c_186, plain, (![B_66]: (k3_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0, B_66)), k1_xboole_0)=k1_relat_1(k5_relat_1(k1_xboole_0, B_66)) | ~v1_relat_1(B_66))), inference(resolution, [status(thm)], [c_183, c_20])).
% 3.24/1.57  tff(c_189, plain, (![B_67]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_67))=k1_xboole_0 | ~v1_relat_1(B_67))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_186])).
% 3.24/1.57  tff(c_26, plain, (![A_18]: (~v1_xboole_0(k1_relat_1(A_18)) | ~v1_relat_1(A_18) | v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.24/1.57  tff(c_204, plain, (![B_67]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_67)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_67)) | ~v1_relat_1(B_67))), inference(superposition, [status(thm), theory('equality')], [c_189, c_26])).
% 3.24/1.57  tff(c_357, plain, (![B_85]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_85)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_85)) | ~v1_relat_1(B_85))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_204])).
% 3.24/1.57  tff(c_12, plain, (![A_7]: (k1_xboole_0=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.24/1.57  tff(c_372, plain, (![B_86]: (k5_relat_1(k1_xboole_0, B_86)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_86)) | ~v1_relat_1(B_86))), inference(resolution, [status(thm)], [c_357, c_12])).
% 3.24/1.57  tff(c_376, plain, (![B_17]: (k5_relat_1(k1_xboole_0, B_17)=k1_xboole_0 | ~v1_relat_1(B_17) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_372])).
% 3.24/1.57  tff(c_380, plain, (![B_87]: (k5_relat_1(k1_xboole_0, B_87)=k1_xboole_0 | ~v1_relat_1(B_87))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_376])).
% 3.24/1.57  tff(c_389, plain, (k5_relat_1(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_380])).
% 3.24/1.57  tff(c_395, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_389])).
% 3.24/1.57  tff(c_396, plain, (k5_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 3.24/1.57  tff(c_448, plain, (![A_105, B_106]: (r2_hidden('#skF_2'(A_105, B_106), B_106) | r1_xboole_0(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.24/1.57  tff(c_453, plain, (![B_107, A_108]: (~v1_xboole_0(B_107) | r1_xboole_0(A_108, B_107))), inference(resolution, [status(thm)], [c_448, c_2])).
% 3.24/1.57  tff(c_468, plain, (![A_112, B_113]: (k3_xboole_0(A_112, B_113)=k1_xboole_0 | ~v1_xboole_0(B_113))), inference(resolution, [status(thm)], [c_453, c_6])).
% 3.24/1.57  tff(c_471, plain, (![A_112]: (k3_xboole_0(A_112, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_468])).
% 3.24/1.57  tff(c_34, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.24/1.57  tff(c_497, plain, (![A_118, B_119]: (r1_tarski(k2_relat_1(k5_relat_1(A_118, B_119)), k2_relat_1(B_119)) | ~v1_relat_1(B_119) | ~v1_relat_1(A_118))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.24/1.57  tff(c_506, plain, (![A_118]: (r1_tarski(k2_relat_1(k5_relat_1(A_118, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_118))), inference(superposition, [status(thm), theory('equality')], [c_34, c_497])).
% 3.24/1.57  tff(c_517, plain, (![A_120]: (r1_tarski(k2_relat_1(k5_relat_1(A_120, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_120))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_506])).
% 3.24/1.57  tff(c_520, plain, (![A_120]: (k3_xboole_0(k2_relat_1(k5_relat_1(A_120, k1_xboole_0)), k1_xboole_0)=k2_relat_1(k5_relat_1(A_120, k1_xboole_0)) | ~v1_relat_1(A_120))), inference(resolution, [status(thm)], [c_517, c_20])).
% 3.24/1.57  tff(c_523, plain, (![A_121]: (k2_relat_1(k5_relat_1(A_121, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_121))), inference(demodulation, [status(thm), theory('equality')], [c_471, c_520])).
% 3.24/1.57  tff(c_28, plain, (![A_19]: (~v1_xboole_0(k2_relat_1(A_19)) | ~v1_relat_1(A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.24/1.57  tff(c_538, plain, (![A_121]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_121, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_121, k1_xboole_0)) | ~v1_relat_1(A_121))), inference(superposition, [status(thm), theory('equality')], [c_523, c_28])).
% 3.24/1.57  tff(c_635, plain, (![A_129]: (~v1_relat_1(k5_relat_1(A_129, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_129, k1_xboole_0)) | ~v1_relat_1(A_129))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_538])).
% 3.24/1.57  tff(c_698, plain, (![A_133]: (k5_relat_1(A_133, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_133, k1_xboole_0)) | ~v1_relat_1(A_133))), inference(resolution, [status(thm)], [c_635, c_12])).
% 3.24/1.57  tff(c_702, plain, (![A_16]: (k5_relat_1(A_16, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_16))), inference(resolution, [status(thm)], [c_24, c_698])).
% 3.24/1.57  tff(c_706, plain, (![A_134]: (k5_relat_1(A_134, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_134))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_702])).
% 3.24/1.57  tff(c_715, plain, (k5_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_706])).
% 3.24/1.57  tff(c_721, plain, $false, inference(negUnitSimplification, [status(thm)], [c_396, c_715])).
% 3.24/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.57  
% 3.24/1.57  Inference rules
% 3.24/1.57  ----------------------
% 3.24/1.57  #Ref     : 0
% 3.24/1.57  #Sup     : 146
% 3.24/1.57  #Fact    : 0
% 3.24/1.57  #Define  : 0
% 3.24/1.57  #Split   : 3
% 3.24/1.57  #Chain   : 0
% 3.24/1.57  #Close   : 0
% 3.24/1.57  
% 3.24/1.57  Ordering : KBO
% 3.24/1.57  
% 3.24/1.57  Simplification rules
% 3.24/1.57  ----------------------
% 3.24/1.57  #Subsume      : 24
% 3.24/1.57  #Demod        : 90
% 3.24/1.57  #Tautology    : 67
% 3.24/1.57  #SimpNegUnit  : 10
% 3.24/1.57  #BackRed      : 6
% 3.24/1.57  
% 3.24/1.57  #Partial instantiations: 0
% 3.24/1.57  #Strategies tried      : 1
% 3.24/1.57  
% 3.24/1.57  Timing (in seconds)
% 3.24/1.57  ----------------------
% 3.24/1.58  Preprocessing        : 0.33
% 3.24/1.58  Parsing              : 0.19
% 3.24/1.58  CNF conversion       : 0.02
% 3.24/1.58  Main loop            : 0.38
% 3.24/1.58  Inferencing          : 0.16
% 3.24/1.58  Reduction            : 0.10
% 3.24/1.58  Demodulation         : 0.07
% 3.24/1.58  BG Simplification    : 0.02
% 3.24/1.58  Subsumption          : 0.07
% 3.24/1.58  Abstraction          : 0.02
% 3.24/1.58  MUC search           : 0.00
% 3.24/1.58  Cooper               : 0.00
% 3.24/1.58  Total                : 0.77
% 3.24/1.58  Index Insertion      : 0.00
% 3.24/1.58  Index Deletion       : 0.00
% 3.24/1.58  Index Matching       : 0.00
% 3.24/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
