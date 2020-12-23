%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:08 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 118 expanded)
%              Number of leaves         :   30 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  133 ( 204 expanded)
%              Number of equality atoms :   30 (  48 expanded)
%              Maximal formula depth    :    8 (   4 average)
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

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_56,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_99,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_96,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_34,plain,
    ( k5_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_58,plain,(
    k5_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_46,plain,(
    ! [A_26] :
      ( v1_relat_1(A_26)
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_50,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_46])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( v1_relat_1(k5_relat_1(A_15,B_16))
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_77,plain,(
    ! [A_35,B_36,C_37] :
      ( ~ r1_xboole_0(A_35,B_36)
      | ~ r2_hidden(C_37,k3_xboole_0(A_35,B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_83,plain,(
    ! [A_38,B_39] :
      ( ~ r1_xboole_0(A_38,B_39)
      | v1_xboole_0(k3_xboole_0(A_38,B_39)) ) ),
    inference(resolution,[status(thm)],[c_4,c_77])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_92,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_xboole_0(A_40,B_41) ) ),
    inference(resolution,[status(thm)],[c_83,c_8])).

tff(c_96,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_92])).

tff(c_32,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_152,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_52,B_53)),k1_relat_1(A_52))
      | ~ v1_relat_1(B_53)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_158,plain,(
    ! [B_53] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_53)),k1_xboole_0)
      | ~ v1_relat_1(B_53)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_152])).

tff(c_172,plain,(
    ! [B_56] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_56)),k1_xboole_0)
      | ~ v1_relat_1(B_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_158])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_175,plain,(
    ! [B_56] :
      ( k3_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,B_56)),k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,B_56))
      | ~ v1_relat_1(B_56) ) ),
    inference(resolution,[status(thm)],[c_172,c_14])).

tff(c_178,plain,(
    ! [B_57] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_57)) = k1_xboole_0
      | ~ v1_relat_1(B_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_175])).

tff(c_22,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(k1_relat_1(A_17))
      | ~ v1_relat_1(A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_193,plain,(
    ! [B_57] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_57))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_57))
      | ~ v1_relat_1(B_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_22])).

tff(c_325,plain,(
    ! [B_64] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_64))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_64))
      | ~ v1_relat_1(B_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_193])).

tff(c_343,plain,(
    ! [B_66] :
      ( k5_relat_1(k1_xboole_0,B_66) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_66))
      | ~ v1_relat_1(B_66) ) ),
    inference(resolution,[status(thm)],[c_325,c_8])).

tff(c_347,plain,(
    ! [B_16] :
      ( k5_relat_1(k1_xboole_0,B_16) = k1_xboole_0
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_343])).

tff(c_359,plain,(
    ! [B_68] :
      ( k5_relat_1(k1_xboole_0,B_68) = k1_xboole_0
      | ~ v1_relat_1(B_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_347])).

tff(c_371,plain,(
    k5_relat_1(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_359])).

tff(c_378,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_371])).

tff(c_379,plain,(
    k5_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_403,plain,(
    ! [A_74,B_75,C_76] :
      ( ~ r1_xboole_0(A_74,B_75)
      | ~ r2_hidden(C_76,k3_xboole_0(A_74,B_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_409,plain,(
    ! [A_77,B_78] :
      ( ~ r1_xboole_0(A_77,B_78)
      | v1_xboole_0(k3_xboole_0(A_77,B_78)) ) ),
    inference(resolution,[status(thm)],[c_4,c_403])).

tff(c_424,plain,(
    ! [A_81,B_82] :
      ( k3_xboole_0(A_81,B_82) = k1_xboole_0
      | ~ r1_xboole_0(A_81,B_82) ) ),
    inference(resolution,[status(thm)],[c_409,c_8])).

tff(c_428,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_424])).

tff(c_30,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_514,plain,(
    ! [A_94,B_95] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_94,B_95)),k2_relat_1(B_95))
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_523,plain,(
    ! [A_94] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_94,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_514])).

tff(c_594,plain,(
    ! [A_97] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_97,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_523])).

tff(c_597,plain,(
    ! [A_97] :
      ( k3_xboole_0(k2_relat_1(k5_relat_1(A_97,k1_xboole_0)),k1_xboole_0) = k2_relat_1(k5_relat_1(A_97,k1_xboole_0))
      | ~ v1_relat_1(A_97) ) ),
    inference(resolution,[status(thm)],[c_594,c_14])).

tff(c_600,plain,(
    ! [A_98] :
      ( k2_relat_1(k5_relat_1(A_98,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_428,c_597])).

tff(c_24,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(k2_relat_1(A_18))
      | ~ v1_relat_1(A_18)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_615,plain,(
    ! [A_98] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_98,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_98,k1_xboole_0))
      | ~ v1_relat_1(A_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_600,c_24])).

tff(c_640,plain,(
    ! [A_100] :
      ( ~ v1_relat_1(k5_relat_1(A_100,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_100,k1_xboole_0))
      | ~ v1_relat_1(A_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_615])).

tff(c_775,plain,(
    ! [A_105] :
      ( k5_relat_1(A_105,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_105,k1_xboole_0))
      | ~ v1_relat_1(A_105) ) ),
    inference(resolution,[status(thm)],[c_640,c_8])).

tff(c_782,plain,(
    ! [A_15] :
      ( k5_relat_1(A_15,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_15) ) ),
    inference(resolution,[status(thm)],[c_20,c_775])).

tff(c_788,plain,(
    ! [A_106] :
      ( k5_relat_1(A_106,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_782])).

tff(c_800,plain,(
    k5_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_788])).

tff(c_808,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_379,c_800])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:51:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.38  
% 2.51/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.38  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.51/1.38  
% 2.51/1.38  %Foreground sorts:
% 2.51/1.38  
% 2.51/1.38  
% 2.51/1.38  %Background operators:
% 2.51/1.38  
% 2.51/1.38  
% 2.51/1.38  %Foreground operators:
% 2.51/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.51/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.51/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.51/1.38  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.51/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.51/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.51/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.51/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.51/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.51/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.51/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.51/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.51/1.38  
% 2.78/1.40  tff(f_106, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 2.78/1.40  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.78/1.40  tff(f_60, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.78/1.40  tff(f_66, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.78/1.40  tff(f_56, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.78/1.40  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.78/1.40  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.78/1.40  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.78/1.40  tff(f_99, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.78/1.40  tff(f_89, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 2.78/1.40  tff(f_54, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.78/1.40  tff(f_74, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.78/1.40  tff(f_96, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 2.78/1.40  tff(f_82, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.78/1.40  tff(c_34, plain, (k5_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.78/1.40  tff(c_58, plain, (k5_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_34])).
% 2.78/1.40  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.78/1.40  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.78/1.40  tff(c_46, plain, (![A_26]: (v1_relat_1(A_26) | ~v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.78/1.40  tff(c_50, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_46])).
% 2.78/1.40  tff(c_20, plain, (![A_15, B_16]: (v1_relat_1(k5_relat_1(A_15, B_16)) | ~v1_relat_1(B_16) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.78/1.40  tff(c_16, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.78/1.40  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.78/1.40  tff(c_77, plain, (![A_35, B_36, C_37]: (~r1_xboole_0(A_35, B_36) | ~r2_hidden(C_37, k3_xboole_0(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.78/1.40  tff(c_83, plain, (![A_38, B_39]: (~r1_xboole_0(A_38, B_39) | v1_xboole_0(k3_xboole_0(A_38, B_39)))), inference(resolution, [status(thm)], [c_4, c_77])).
% 2.78/1.40  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.78/1.40  tff(c_92, plain, (![A_40, B_41]: (k3_xboole_0(A_40, B_41)=k1_xboole_0 | ~r1_xboole_0(A_40, B_41))), inference(resolution, [status(thm)], [c_83, c_8])).
% 2.78/1.40  tff(c_96, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_92])).
% 2.78/1.40  tff(c_32, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.78/1.40  tff(c_152, plain, (![A_52, B_53]: (r1_tarski(k1_relat_1(k5_relat_1(A_52, B_53)), k1_relat_1(A_52)) | ~v1_relat_1(B_53) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.78/1.40  tff(c_158, plain, (![B_53]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_53)), k1_xboole_0) | ~v1_relat_1(B_53) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_152])).
% 2.78/1.40  tff(c_172, plain, (![B_56]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_56)), k1_xboole_0) | ~v1_relat_1(B_56))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_158])).
% 2.78/1.40  tff(c_14, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.78/1.40  tff(c_175, plain, (![B_56]: (k3_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0, B_56)), k1_xboole_0)=k1_relat_1(k5_relat_1(k1_xboole_0, B_56)) | ~v1_relat_1(B_56))), inference(resolution, [status(thm)], [c_172, c_14])).
% 2.78/1.40  tff(c_178, plain, (![B_57]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_57))=k1_xboole_0 | ~v1_relat_1(B_57))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_175])).
% 2.78/1.40  tff(c_22, plain, (![A_17]: (~v1_xboole_0(k1_relat_1(A_17)) | ~v1_relat_1(A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.78/1.40  tff(c_193, plain, (![B_57]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_57)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_57)) | ~v1_relat_1(B_57))), inference(superposition, [status(thm), theory('equality')], [c_178, c_22])).
% 2.78/1.40  tff(c_325, plain, (![B_64]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_64)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_64)) | ~v1_relat_1(B_64))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_193])).
% 2.78/1.40  tff(c_343, plain, (![B_66]: (k5_relat_1(k1_xboole_0, B_66)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_66)) | ~v1_relat_1(B_66))), inference(resolution, [status(thm)], [c_325, c_8])).
% 2.78/1.40  tff(c_347, plain, (![B_16]: (k5_relat_1(k1_xboole_0, B_16)=k1_xboole_0 | ~v1_relat_1(B_16) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_343])).
% 2.78/1.40  tff(c_359, plain, (![B_68]: (k5_relat_1(k1_xboole_0, B_68)=k1_xboole_0 | ~v1_relat_1(B_68))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_347])).
% 2.78/1.40  tff(c_371, plain, (k5_relat_1(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_359])).
% 2.78/1.40  tff(c_378, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_371])).
% 2.78/1.40  tff(c_379, plain, (k5_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 2.78/1.40  tff(c_403, plain, (![A_74, B_75, C_76]: (~r1_xboole_0(A_74, B_75) | ~r2_hidden(C_76, k3_xboole_0(A_74, B_75)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.78/1.40  tff(c_409, plain, (![A_77, B_78]: (~r1_xboole_0(A_77, B_78) | v1_xboole_0(k3_xboole_0(A_77, B_78)))), inference(resolution, [status(thm)], [c_4, c_403])).
% 2.78/1.40  tff(c_424, plain, (![A_81, B_82]: (k3_xboole_0(A_81, B_82)=k1_xboole_0 | ~r1_xboole_0(A_81, B_82))), inference(resolution, [status(thm)], [c_409, c_8])).
% 2.78/1.40  tff(c_428, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_424])).
% 2.78/1.40  tff(c_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.78/1.40  tff(c_514, plain, (![A_94, B_95]: (r1_tarski(k2_relat_1(k5_relat_1(A_94, B_95)), k2_relat_1(B_95)) | ~v1_relat_1(B_95) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.78/1.40  tff(c_523, plain, (![A_94]: (r1_tarski(k2_relat_1(k5_relat_1(A_94, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_94))), inference(superposition, [status(thm), theory('equality')], [c_30, c_514])).
% 2.78/1.40  tff(c_594, plain, (![A_97]: (r1_tarski(k2_relat_1(k5_relat_1(A_97, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_97))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_523])).
% 2.78/1.40  tff(c_597, plain, (![A_97]: (k3_xboole_0(k2_relat_1(k5_relat_1(A_97, k1_xboole_0)), k1_xboole_0)=k2_relat_1(k5_relat_1(A_97, k1_xboole_0)) | ~v1_relat_1(A_97))), inference(resolution, [status(thm)], [c_594, c_14])).
% 2.78/1.40  tff(c_600, plain, (![A_98]: (k2_relat_1(k5_relat_1(A_98, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_98))), inference(demodulation, [status(thm), theory('equality')], [c_428, c_597])).
% 2.78/1.40  tff(c_24, plain, (![A_18]: (~v1_xboole_0(k2_relat_1(A_18)) | ~v1_relat_1(A_18) | v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.78/1.40  tff(c_615, plain, (![A_98]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_98, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_98, k1_xboole_0)) | ~v1_relat_1(A_98))), inference(superposition, [status(thm), theory('equality')], [c_600, c_24])).
% 2.78/1.40  tff(c_640, plain, (![A_100]: (~v1_relat_1(k5_relat_1(A_100, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_100, k1_xboole_0)) | ~v1_relat_1(A_100))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_615])).
% 2.78/1.40  tff(c_775, plain, (![A_105]: (k5_relat_1(A_105, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_105, k1_xboole_0)) | ~v1_relat_1(A_105))), inference(resolution, [status(thm)], [c_640, c_8])).
% 2.78/1.40  tff(c_782, plain, (![A_15]: (k5_relat_1(A_15, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_15))), inference(resolution, [status(thm)], [c_20, c_775])).
% 2.78/1.40  tff(c_788, plain, (![A_106]: (k5_relat_1(A_106, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_106))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_782])).
% 2.78/1.40  tff(c_800, plain, (k5_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_788])).
% 2.78/1.40  tff(c_808, plain, $false, inference(negUnitSimplification, [status(thm)], [c_379, c_800])).
% 2.78/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.40  
% 2.78/1.40  Inference rules
% 2.78/1.40  ----------------------
% 2.78/1.40  #Ref     : 0
% 2.78/1.40  #Sup     : 164
% 2.78/1.40  #Fact    : 0
% 2.78/1.40  #Define  : 0
% 2.78/1.40  #Split   : 2
% 2.78/1.40  #Chain   : 0
% 2.78/1.40  #Close   : 0
% 2.78/1.40  
% 2.78/1.40  Ordering : KBO
% 2.78/1.40  
% 2.78/1.40  Simplification rules
% 2.78/1.40  ----------------------
% 2.78/1.40  #Subsume      : 16
% 2.78/1.40  #Demod        : 154
% 2.78/1.40  #Tautology    : 90
% 2.78/1.40  #SimpNegUnit  : 10
% 2.78/1.40  #BackRed      : 4
% 2.78/1.40  
% 2.78/1.40  #Partial instantiations: 0
% 2.78/1.40  #Strategies tried      : 1
% 2.78/1.40  
% 2.78/1.40  Timing (in seconds)
% 2.78/1.40  ----------------------
% 2.78/1.40  Preprocessing        : 0.29
% 2.78/1.40  Parsing              : 0.17
% 2.78/1.40  CNF conversion       : 0.02
% 2.78/1.40  Main loop            : 0.32
% 2.78/1.40  Inferencing          : 0.13
% 2.78/1.40  Reduction            : 0.09
% 2.78/1.40  Demodulation         : 0.06
% 2.78/1.40  BG Simplification    : 0.02
% 2.78/1.40  Subsumption          : 0.05
% 2.78/1.40  Abstraction          : 0.01
% 2.78/1.40  MUC search           : 0.00
% 2.78/1.40  Cooper               : 0.00
% 2.78/1.40  Total                : 0.64
% 2.78/1.40  Index Insertion      : 0.00
% 2.78/1.40  Index Deletion       : 0.00
% 2.78/1.40  Index Matching       : 0.00
% 2.78/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
