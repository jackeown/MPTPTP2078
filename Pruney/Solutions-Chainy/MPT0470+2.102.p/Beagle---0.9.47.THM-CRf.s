%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:15 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 130 expanded)
%              Number of leaves         :   42 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :  124 ( 196 expanded)
%              Number of equality atoms :   39 (  61 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_42,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_38,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_106,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_103,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_54,plain,
    ( k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_82,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_56,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_40,plain,(
    ! [A_30] :
      ( r2_hidden('#skF_1'(A_30),A_30)
      | v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_16,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_202,plain,(
    ! [A_82,B_83] :
      ( ~ r2_hidden(A_82,B_83)
      | ~ r1_xboole_0(k1_tarski(A_82),B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_208,plain,(
    ! [A_84] : ~ r2_hidden(A_84,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_202])).

tff(c_213,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_40,c_208])).

tff(c_42,plain,(
    ! [A_48,B_49] :
      ( v1_relat_1(k5_relat_1(A_48,B_49))
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_12,plain,(
    ! [A_4] : k3_xboole_0(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_98,plain,(
    ! [A_66,B_67] :
      ( v1_xboole_0(k2_zfmisc_1(A_66,B_67))
      | ~ v1_xboole_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_138,plain,(
    ! [A_73,B_74] :
      ( k2_zfmisc_1(A_73,B_74) = k1_xboole_0
      | ~ v1_xboole_0(A_73) ) ),
    inference(resolution,[status(thm)],[c_98,c_4])).

tff(c_147,plain,(
    ! [B_74] : k2_zfmisc_1(k1_xboole_0,B_74) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_138])).

tff(c_52,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_530,plain,(
    ! [A_106,B_107] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_106,B_107)),k1_relat_1(A_106))
      | ~ v1_relat_1(B_107)
      | ~ v1_relat_1(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_535,plain,(
    ! [B_107] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_107)),k1_xboole_0)
      | ~ v1_relat_1(B_107)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_530])).

tff(c_539,plain,(
    ! [B_108] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_108)),k1_xboole_0)
      | ~ v1_relat_1(B_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_535])).

tff(c_14,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_214,plain,(
    ! [B_85,A_86] :
      ( B_85 = A_86
      | ~ r1_tarski(B_85,A_86)
      | ~ r1_tarski(A_86,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_223,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_214])).

tff(c_549,plain,(
    ! [B_109] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_109)) = k1_xboole_0
      | ~ v1_relat_1(B_109) ) ),
    inference(resolution,[status(thm)],[c_539,c_223])).

tff(c_44,plain,(
    ! [A_50] :
      ( k3_xboole_0(A_50,k2_zfmisc_1(k1_relat_1(A_50),k2_relat_1(A_50))) = A_50
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_564,plain,(
    ! [B_109] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_109),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_109)))) = k5_relat_1(k1_xboole_0,B_109)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_109))
      | ~ v1_relat_1(B_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_549,c_44])).

tff(c_583,plain,(
    ! [B_114] :
      ( k5_relat_1(k1_xboole_0,B_114) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_114))
      | ~ v1_relat_1(B_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_147,c_564])).

tff(c_587,plain,(
    ! [B_49] :
      ( k5_relat_1(k1_xboole_0,B_49) = k1_xboole_0
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_42,c_583])).

tff(c_591,plain,(
    ! [B_115] :
      ( k5_relat_1(k1_xboole_0,B_115) = k1_xboole_0
      | ~ v1_relat_1(B_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_587])).

tff(c_600,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_591])).

tff(c_606,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_600])).

tff(c_607,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_723,plain,(
    ! [A_134,B_135] :
      ( ~ r2_hidden(A_134,B_135)
      | ~ r1_xboole_0(k1_tarski(A_134),B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_729,plain,(
    ! [A_136] : ~ r2_hidden(A_136,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_723])).

tff(c_734,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_40,c_729])).

tff(c_628,plain,(
    ! [A_120,B_121] :
      ( v1_xboole_0(k2_zfmisc_1(A_120,B_121))
      | ~ v1_xboole_0(B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_671,plain,(
    ! [A_127,B_128] :
      ( k2_zfmisc_1(A_127,B_128) = k1_xboole_0
      | ~ v1_xboole_0(B_128) ) ),
    inference(resolution,[status(thm)],[c_628,c_4])).

tff(c_680,plain,(
    ! [A_127] : k2_zfmisc_1(A_127,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_671])).

tff(c_50,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1250,plain,(
    ! [B_179,A_180] :
      ( k2_relat_1(k5_relat_1(B_179,A_180)) = k2_relat_1(A_180)
      | ~ r1_tarski(k1_relat_1(A_180),k2_relat_1(B_179))
      | ~ v1_relat_1(B_179)
      | ~ v1_relat_1(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1256,plain,(
    ! [B_179] :
      ( k2_relat_1(k5_relat_1(B_179,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_179))
      | ~ v1_relat_1(B_179)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1250])).

tff(c_1266,plain,(
    ! [B_181] :
      ( k2_relat_1(k5_relat_1(B_181,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_181) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_734,c_14,c_50,c_1256])).

tff(c_1275,plain,(
    ! [B_181] :
      ( k3_xboole_0(k5_relat_1(B_181,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(B_181,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(B_181,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_181,k1_xboole_0))
      | ~ v1_relat_1(B_181) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1266,c_44])).

tff(c_1297,plain,(
    ! [B_187] :
      ( k5_relat_1(B_187,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_187,k1_xboole_0))
      | ~ v1_relat_1(B_187) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_680,c_1275])).

tff(c_1304,plain,(
    ! [A_48] :
      ( k5_relat_1(A_48,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_48) ) ),
    inference(resolution,[status(thm)],[c_42,c_1297])).

tff(c_1310,plain,(
    ! [A_188] :
      ( k5_relat_1(A_188,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_188) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_734,c_1304])).

tff(c_1319,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_1310])).

tff(c_1326,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_607,c_1319])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:02:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.42  
% 2.84/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.43  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.84/1.43  
% 2.84/1.43  %Foreground sorts:
% 2.84/1.43  
% 2.84/1.43  
% 2.84/1.43  %Background operators:
% 2.84/1.43  
% 2.84/1.43  
% 2.84/1.43  %Foreground operators:
% 2.84/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.84/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.84/1.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.84/1.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.84/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.84/1.43  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.84/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.84/1.43  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.84/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.84/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.84/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.84/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.84/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.84/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.84/1.43  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.84/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.84/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.84/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.84/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.84/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.84/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.84/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.84/1.43  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.84/1.43  
% 3.07/1.44  tff(f_113, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 3.07/1.44  tff(f_77, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 3.07/1.44  tff(f_42, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.07/1.44  tff(f_65, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 3.07/1.44  tff(f_83, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.07/1.44  tff(f_38, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.07/1.44  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.07/1.44  tff(f_60, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 3.07/1.44  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.07/1.44  tff(f_106, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.07/1.44  tff(f_94, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 3.07/1.44  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.07/1.44  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.07/1.44  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 3.07/1.44  tff(f_56, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 3.07/1.44  tff(f_103, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 3.07/1.44  tff(c_54, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.07/1.44  tff(c_82, plain, (k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_54])).
% 3.07/1.44  tff(c_56, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.07/1.44  tff(c_40, plain, (![A_30]: (r2_hidden('#skF_1'(A_30), A_30) | v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.07/1.44  tff(c_16, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.07/1.44  tff(c_202, plain, (![A_82, B_83]: (~r2_hidden(A_82, B_83) | ~r1_xboole_0(k1_tarski(A_82), B_83))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.07/1.44  tff(c_208, plain, (![A_84]: (~r2_hidden(A_84, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_202])).
% 3.07/1.44  tff(c_213, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_208])).
% 3.07/1.44  tff(c_42, plain, (![A_48, B_49]: (v1_relat_1(k5_relat_1(A_48, B_49)) | ~v1_relat_1(B_49) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.07/1.44  tff(c_12, plain, (![A_4]: (k3_xboole_0(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.07/1.44  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.07/1.44  tff(c_98, plain, (![A_66, B_67]: (v1_xboole_0(k2_zfmisc_1(A_66, B_67)) | ~v1_xboole_0(A_66))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.07/1.44  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.07/1.44  tff(c_138, plain, (![A_73, B_74]: (k2_zfmisc_1(A_73, B_74)=k1_xboole_0 | ~v1_xboole_0(A_73))), inference(resolution, [status(thm)], [c_98, c_4])).
% 3.07/1.44  tff(c_147, plain, (![B_74]: (k2_zfmisc_1(k1_xboole_0, B_74)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_138])).
% 3.07/1.44  tff(c_52, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.07/1.44  tff(c_530, plain, (![A_106, B_107]: (r1_tarski(k1_relat_1(k5_relat_1(A_106, B_107)), k1_relat_1(A_106)) | ~v1_relat_1(B_107) | ~v1_relat_1(A_106))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.07/1.44  tff(c_535, plain, (![B_107]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_107)), k1_xboole_0) | ~v1_relat_1(B_107) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_52, c_530])).
% 3.07/1.44  tff(c_539, plain, (![B_108]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_108)), k1_xboole_0) | ~v1_relat_1(B_108))), inference(demodulation, [status(thm), theory('equality')], [c_213, c_535])).
% 3.07/1.44  tff(c_14, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.07/1.44  tff(c_214, plain, (![B_85, A_86]: (B_85=A_86 | ~r1_tarski(B_85, A_86) | ~r1_tarski(A_86, B_85))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.07/1.44  tff(c_223, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_214])).
% 3.07/1.44  tff(c_549, plain, (![B_109]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_109))=k1_xboole_0 | ~v1_relat_1(B_109))), inference(resolution, [status(thm)], [c_539, c_223])).
% 3.07/1.44  tff(c_44, plain, (![A_50]: (k3_xboole_0(A_50, k2_zfmisc_1(k1_relat_1(A_50), k2_relat_1(A_50)))=A_50 | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.07/1.44  tff(c_564, plain, (![B_109]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_109), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_109))))=k5_relat_1(k1_xboole_0, B_109) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_109)) | ~v1_relat_1(B_109))), inference(superposition, [status(thm), theory('equality')], [c_549, c_44])).
% 3.07/1.44  tff(c_583, plain, (![B_114]: (k5_relat_1(k1_xboole_0, B_114)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_114)) | ~v1_relat_1(B_114))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_147, c_564])).
% 3.07/1.44  tff(c_587, plain, (![B_49]: (k5_relat_1(k1_xboole_0, B_49)=k1_xboole_0 | ~v1_relat_1(B_49) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_42, c_583])).
% 3.07/1.44  tff(c_591, plain, (![B_115]: (k5_relat_1(k1_xboole_0, B_115)=k1_xboole_0 | ~v1_relat_1(B_115))), inference(demodulation, [status(thm), theory('equality')], [c_213, c_587])).
% 3.07/1.44  tff(c_600, plain, (k5_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_591])).
% 3.07/1.44  tff(c_606, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_600])).
% 3.07/1.44  tff(c_607, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 3.07/1.44  tff(c_723, plain, (![A_134, B_135]: (~r2_hidden(A_134, B_135) | ~r1_xboole_0(k1_tarski(A_134), B_135))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.07/1.44  tff(c_729, plain, (![A_136]: (~r2_hidden(A_136, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_723])).
% 3.07/1.44  tff(c_734, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_729])).
% 3.07/1.44  tff(c_628, plain, (![A_120, B_121]: (v1_xboole_0(k2_zfmisc_1(A_120, B_121)) | ~v1_xboole_0(B_121))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.07/1.44  tff(c_671, plain, (![A_127, B_128]: (k2_zfmisc_1(A_127, B_128)=k1_xboole_0 | ~v1_xboole_0(B_128))), inference(resolution, [status(thm)], [c_628, c_4])).
% 3.07/1.44  tff(c_680, plain, (![A_127]: (k2_zfmisc_1(A_127, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_671])).
% 3.07/1.44  tff(c_50, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.07/1.44  tff(c_1250, plain, (![B_179, A_180]: (k2_relat_1(k5_relat_1(B_179, A_180))=k2_relat_1(A_180) | ~r1_tarski(k1_relat_1(A_180), k2_relat_1(B_179)) | ~v1_relat_1(B_179) | ~v1_relat_1(A_180))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.07/1.44  tff(c_1256, plain, (![B_179]: (k2_relat_1(k5_relat_1(B_179, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_179)) | ~v1_relat_1(B_179) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_52, c_1250])).
% 3.07/1.44  tff(c_1266, plain, (![B_181]: (k2_relat_1(k5_relat_1(B_181, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_181))), inference(demodulation, [status(thm), theory('equality')], [c_734, c_14, c_50, c_1256])).
% 3.07/1.44  tff(c_1275, plain, (![B_181]: (k3_xboole_0(k5_relat_1(B_181, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(B_181, k1_xboole_0)), k1_xboole_0))=k5_relat_1(B_181, k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_181, k1_xboole_0)) | ~v1_relat_1(B_181))), inference(superposition, [status(thm), theory('equality')], [c_1266, c_44])).
% 3.07/1.44  tff(c_1297, plain, (![B_187]: (k5_relat_1(B_187, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_187, k1_xboole_0)) | ~v1_relat_1(B_187))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_680, c_1275])).
% 3.07/1.44  tff(c_1304, plain, (![A_48]: (k5_relat_1(A_48, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_48))), inference(resolution, [status(thm)], [c_42, c_1297])).
% 3.07/1.44  tff(c_1310, plain, (![A_188]: (k5_relat_1(A_188, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_188))), inference(demodulation, [status(thm), theory('equality')], [c_734, c_1304])).
% 3.07/1.44  tff(c_1319, plain, (k5_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_1310])).
% 3.07/1.44  tff(c_1326, plain, $false, inference(negUnitSimplification, [status(thm)], [c_607, c_1319])).
% 3.07/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.44  
% 3.07/1.44  Inference rules
% 3.07/1.44  ----------------------
% 3.07/1.44  #Ref     : 1
% 3.07/1.44  #Sup     : 291
% 3.07/1.44  #Fact    : 0
% 3.07/1.44  #Define  : 0
% 3.07/1.44  #Split   : 1
% 3.07/1.44  #Chain   : 0
% 3.07/1.44  #Close   : 0
% 3.07/1.44  
% 3.07/1.44  Ordering : KBO
% 3.07/1.44  
% 3.07/1.44  Simplification rules
% 3.07/1.44  ----------------------
% 3.07/1.44  #Subsume      : 5
% 3.07/1.44  #Demod        : 185
% 3.07/1.44  #Tautology    : 240
% 3.07/1.44  #SimpNegUnit  : 2
% 3.07/1.44  #BackRed      : 0
% 3.07/1.44  
% 3.07/1.44  #Partial instantiations: 0
% 3.07/1.44  #Strategies tried      : 1
% 3.07/1.44  
% 3.07/1.44  Timing (in seconds)
% 3.07/1.44  ----------------------
% 3.07/1.44  Preprocessing        : 0.32
% 3.07/1.44  Parsing              : 0.17
% 3.07/1.44  CNF conversion       : 0.02
% 3.07/1.45  Main loop            : 0.36
% 3.07/1.45  Inferencing          : 0.14
% 3.07/1.45  Reduction            : 0.11
% 3.07/1.45  Demodulation         : 0.08
% 3.07/1.45  BG Simplification    : 0.02
% 3.07/1.45  Subsumption          : 0.06
% 3.07/1.45  Abstraction          : 0.02
% 3.07/1.45  MUC search           : 0.00
% 3.07/1.45  Cooper               : 0.00
% 3.07/1.45  Total                : 0.72
% 3.07/1.45  Index Insertion      : 0.00
% 3.07/1.45  Index Deletion       : 0.00
% 3.07/1.45  Index Matching       : 0.00
% 3.07/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
