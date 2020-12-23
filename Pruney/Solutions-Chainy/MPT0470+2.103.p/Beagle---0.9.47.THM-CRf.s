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
% DateTime   : Thu Dec  3 09:59:15 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 133 expanded)
%              Number of leaves         :   43 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  128 ( 200 expanded)
%              Number of equality atoms :   38 (  58 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_42,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_85,axiom,(
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

tff(f_62,axiom,(
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

tff(f_96,axiom,(
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

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_103,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(c_56,plain,
    ( k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_84,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_58,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_42,plain,(
    ! [A_43] :
      ( r2_hidden('#skF_1'(A_43),A_43)
      | v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_16,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_176,plain,(
    ! [A_95,C_96,B_97] :
      ( ~ r2_hidden(A_95,C_96)
      | ~ r1_xboole_0(k2_tarski(A_95,B_97),C_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_182,plain,(
    ! [A_98] : ~ r2_hidden(A_98,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_176])).

tff(c_187,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_42,c_182])).

tff(c_44,plain,(
    ! [A_61,B_62] :
      ( v1_relat_1(k5_relat_1(A_61,B_62))
      | ~ v1_relat_1(B_62)
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_12,plain,(
    ! [A_4] : k3_xboole_0(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_91,plain,(
    ! [A_78,B_79] :
      ( v1_xboole_0(k2_zfmisc_1(A_78,B_79))
      | ~ v1_xboole_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_131,plain,(
    ! [A_85,B_86] :
      ( k2_zfmisc_1(A_85,B_86) = k1_xboole_0
      | ~ v1_xboole_0(A_85) ) ),
    inference(resolution,[status(thm)],[c_91,c_4])).

tff(c_140,plain,(
    ! [B_86] : k2_zfmisc_1(k1_xboole_0,B_86) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_131])).

tff(c_54,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_503,plain,(
    ! [A_118,B_119] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_118,B_119)),k1_relat_1(A_118))
      | ~ v1_relat_1(B_119)
      | ~ v1_relat_1(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_508,plain,(
    ! [B_119] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_119)),k1_xboole_0)
      | ~ v1_relat_1(B_119)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_503])).

tff(c_512,plain,(
    ! [B_120] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_120)),k1_xboole_0)
      | ~ v1_relat_1(B_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_508])).

tff(c_14,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_188,plain,(
    ! [B_99,A_100] :
      ( B_99 = A_100
      | ~ r1_tarski(B_99,A_100)
      | ~ r1_tarski(A_100,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_197,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_188])).

tff(c_531,plain,(
    ! [B_123] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_123)) = k1_xboole_0
      | ~ v1_relat_1(B_123) ) ),
    inference(resolution,[status(thm)],[c_512,c_197])).

tff(c_46,plain,(
    ! [A_63] :
      ( k3_xboole_0(A_63,k2_zfmisc_1(k1_relat_1(A_63),k2_relat_1(A_63))) = A_63
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_546,plain,(
    ! [B_123] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_123),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_123)))) = k5_relat_1(k1_xboole_0,B_123)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_123))
      | ~ v1_relat_1(B_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_531,c_46])).

tff(c_600,plain,(
    ! [B_130] :
      ( k5_relat_1(k1_xboole_0,B_130) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_130))
      | ~ v1_relat_1(B_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_140,c_546])).

tff(c_604,plain,(
    ! [B_62] :
      ( k5_relat_1(k1_xboole_0,B_62) = k1_xboole_0
      | ~ v1_relat_1(B_62)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_44,c_600])).

tff(c_608,plain,(
    ! [B_131] :
      ( k5_relat_1(k1_xboole_0,B_131) = k1_xboole_0
      | ~ v1_relat_1(B_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_604])).

tff(c_617,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_608])).

tff(c_623,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_617])).

tff(c_624,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_720,plain,(
    ! [A_150,C_151,B_152] :
      ( ~ r2_hidden(A_150,C_151)
      | ~ r1_xboole_0(k2_tarski(A_150,B_152),C_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_726,plain,(
    ! [A_153] : ~ r2_hidden(A_153,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_720])).

tff(c_731,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_42,c_726])).

tff(c_636,plain,(
    ! [A_135,B_136] :
      ( v1_xboole_0(k2_zfmisc_1(A_135,B_136))
      | ~ v1_xboole_0(B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_676,plain,(
    ! [A_142,B_143] :
      ( k2_zfmisc_1(A_142,B_143) = k1_xboole_0
      | ~ v1_xboole_0(B_143) ) ),
    inference(resolution,[status(thm)],[c_636,c_4])).

tff(c_685,plain,(
    ! [A_142] : k2_zfmisc_1(A_142,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_676])).

tff(c_52,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1053,plain,(
    ! [A_175,B_176] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_175,B_176)),k2_relat_1(B_176))
      | ~ v1_relat_1(B_176)
      | ~ v1_relat_1(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1061,plain,(
    ! [A_175] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_175,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_175) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1053])).

tff(c_1076,plain,(
    ! [A_181] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_181,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_181) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_1061])).

tff(c_738,plain,(
    ! [B_156,A_157] :
      ( B_156 = A_157
      | ~ r1_tarski(B_156,A_157)
      | ~ r1_tarski(A_157,B_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_747,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_738])).

tff(c_1086,plain,(
    ! [A_182] :
      ( k2_relat_1(k5_relat_1(A_182,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_182) ) ),
    inference(resolution,[status(thm)],[c_1076,c_747])).

tff(c_1101,plain,(
    ! [A_182] :
      ( k3_xboole_0(k5_relat_1(A_182,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(A_182,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(A_182,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_182,k1_xboole_0))
      | ~ v1_relat_1(A_182) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1086,c_46])).

tff(c_1111,plain,(
    ! [A_183] :
      ( k5_relat_1(A_183,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_183,k1_xboole_0))
      | ~ v1_relat_1(A_183) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_685,c_1101])).

tff(c_1115,plain,(
    ! [A_61] :
      ( k5_relat_1(A_61,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_61) ) ),
    inference(resolution,[status(thm)],[c_44,c_1111])).

tff(c_1119,plain,(
    ! [A_184] :
      ( k5_relat_1(A_184,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_1115])).

tff(c_1128,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_1119])).

tff(c_1134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_624,c_1128])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:35:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.44  
% 2.73/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.44  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.73/1.44  
% 2.73/1.44  %Foreground sorts:
% 2.73/1.44  
% 2.73/1.44  
% 2.73/1.44  %Background operators:
% 2.73/1.44  
% 2.73/1.44  
% 2.73/1.44  %Foreground operators:
% 2.73/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.44  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.73/1.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.73/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.73/1.44  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.73/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.73/1.44  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.73/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.73/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.73/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.73/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.73/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.73/1.44  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.73/1.44  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.73/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.73/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.73/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.73/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.73/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.73/1.44  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.73/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.73/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.73/1.44  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.73/1.44  
% 3.06/1.46  tff(f_113, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 3.06/1.46  tff(f_79, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 3.06/1.46  tff(f_42, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.06/1.46  tff(f_67, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 3.06/1.46  tff(f_85, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.06/1.46  tff(f_38, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.06/1.46  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.06/1.46  tff(f_62, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 3.06/1.46  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.06/1.46  tff(f_106, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.06/1.46  tff(f_96, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 3.06/1.46  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.06/1.46  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.06/1.46  tff(f_89, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 3.06/1.46  tff(f_58, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 3.06/1.46  tff(f_103, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 3.06/1.46  tff(c_56, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.06/1.46  tff(c_84, plain, (k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_56])).
% 3.06/1.46  tff(c_58, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.06/1.46  tff(c_42, plain, (![A_43]: (r2_hidden('#skF_1'(A_43), A_43) | v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.06/1.46  tff(c_16, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.06/1.46  tff(c_176, plain, (![A_95, C_96, B_97]: (~r2_hidden(A_95, C_96) | ~r1_xboole_0(k2_tarski(A_95, B_97), C_96))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.06/1.46  tff(c_182, plain, (![A_98]: (~r2_hidden(A_98, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_176])).
% 3.06/1.46  tff(c_187, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_182])).
% 3.06/1.46  tff(c_44, plain, (![A_61, B_62]: (v1_relat_1(k5_relat_1(A_61, B_62)) | ~v1_relat_1(B_62) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.06/1.46  tff(c_12, plain, (![A_4]: (k3_xboole_0(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.06/1.46  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.06/1.46  tff(c_91, plain, (![A_78, B_79]: (v1_xboole_0(k2_zfmisc_1(A_78, B_79)) | ~v1_xboole_0(A_78))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.06/1.46  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.06/1.46  tff(c_131, plain, (![A_85, B_86]: (k2_zfmisc_1(A_85, B_86)=k1_xboole_0 | ~v1_xboole_0(A_85))), inference(resolution, [status(thm)], [c_91, c_4])).
% 3.06/1.46  tff(c_140, plain, (![B_86]: (k2_zfmisc_1(k1_xboole_0, B_86)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_131])).
% 3.06/1.46  tff(c_54, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.06/1.46  tff(c_503, plain, (![A_118, B_119]: (r1_tarski(k1_relat_1(k5_relat_1(A_118, B_119)), k1_relat_1(A_118)) | ~v1_relat_1(B_119) | ~v1_relat_1(A_118))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.06/1.46  tff(c_508, plain, (![B_119]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_119)), k1_xboole_0) | ~v1_relat_1(B_119) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_54, c_503])).
% 3.06/1.46  tff(c_512, plain, (![B_120]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_120)), k1_xboole_0) | ~v1_relat_1(B_120))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_508])).
% 3.06/1.46  tff(c_14, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.06/1.46  tff(c_188, plain, (![B_99, A_100]: (B_99=A_100 | ~r1_tarski(B_99, A_100) | ~r1_tarski(A_100, B_99))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.06/1.46  tff(c_197, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_188])).
% 3.06/1.46  tff(c_531, plain, (![B_123]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_123))=k1_xboole_0 | ~v1_relat_1(B_123))), inference(resolution, [status(thm)], [c_512, c_197])).
% 3.06/1.46  tff(c_46, plain, (![A_63]: (k3_xboole_0(A_63, k2_zfmisc_1(k1_relat_1(A_63), k2_relat_1(A_63)))=A_63 | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.06/1.46  tff(c_546, plain, (![B_123]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_123), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_123))))=k5_relat_1(k1_xboole_0, B_123) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_123)) | ~v1_relat_1(B_123))), inference(superposition, [status(thm), theory('equality')], [c_531, c_46])).
% 3.06/1.46  tff(c_600, plain, (![B_130]: (k5_relat_1(k1_xboole_0, B_130)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_130)) | ~v1_relat_1(B_130))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_140, c_546])).
% 3.06/1.46  tff(c_604, plain, (![B_62]: (k5_relat_1(k1_xboole_0, B_62)=k1_xboole_0 | ~v1_relat_1(B_62) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_44, c_600])).
% 3.06/1.46  tff(c_608, plain, (![B_131]: (k5_relat_1(k1_xboole_0, B_131)=k1_xboole_0 | ~v1_relat_1(B_131))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_604])).
% 3.06/1.46  tff(c_617, plain, (k5_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_608])).
% 3.06/1.46  tff(c_623, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_617])).
% 3.06/1.46  tff(c_624, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 3.06/1.46  tff(c_720, plain, (![A_150, C_151, B_152]: (~r2_hidden(A_150, C_151) | ~r1_xboole_0(k2_tarski(A_150, B_152), C_151))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.06/1.46  tff(c_726, plain, (![A_153]: (~r2_hidden(A_153, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_720])).
% 3.06/1.46  tff(c_731, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_726])).
% 3.06/1.46  tff(c_636, plain, (![A_135, B_136]: (v1_xboole_0(k2_zfmisc_1(A_135, B_136)) | ~v1_xboole_0(B_136))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.06/1.46  tff(c_676, plain, (![A_142, B_143]: (k2_zfmisc_1(A_142, B_143)=k1_xboole_0 | ~v1_xboole_0(B_143))), inference(resolution, [status(thm)], [c_636, c_4])).
% 3.06/1.46  tff(c_685, plain, (![A_142]: (k2_zfmisc_1(A_142, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_676])).
% 3.06/1.46  tff(c_52, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.06/1.46  tff(c_1053, plain, (![A_175, B_176]: (r1_tarski(k2_relat_1(k5_relat_1(A_175, B_176)), k2_relat_1(B_176)) | ~v1_relat_1(B_176) | ~v1_relat_1(A_175))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.06/1.46  tff(c_1061, plain, (![A_175]: (r1_tarski(k2_relat_1(k5_relat_1(A_175, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_175))), inference(superposition, [status(thm), theory('equality')], [c_52, c_1053])).
% 3.06/1.46  tff(c_1076, plain, (![A_181]: (r1_tarski(k2_relat_1(k5_relat_1(A_181, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_181))), inference(demodulation, [status(thm), theory('equality')], [c_731, c_1061])).
% 3.06/1.46  tff(c_738, plain, (![B_156, A_157]: (B_156=A_157 | ~r1_tarski(B_156, A_157) | ~r1_tarski(A_157, B_156))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.06/1.46  tff(c_747, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_738])).
% 3.06/1.46  tff(c_1086, plain, (![A_182]: (k2_relat_1(k5_relat_1(A_182, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_182))), inference(resolution, [status(thm)], [c_1076, c_747])).
% 3.06/1.46  tff(c_1101, plain, (![A_182]: (k3_xboole_0(k5_relat_1(A_182, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(A_182, k1_xboole_0)), k1_xboole_0))=k5_relat_1(A_182, k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_182, k1_xboole_0)) | ~v1_relat_1(A_182))), inference(superposition, [status(thm), theory('equality')], [c_1086, c_46])).
% 3.06/1.46  tff(c_1111, plain, (![A_183]: (k5_relat_1(A_183, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_183, k1_xboole_0)) | ~v1_relat_1(A_183))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_685, c_1101])).
% 3.06/1.46  tff(c_1115, plain, (![A_61]: (k5_relat_1(A_61, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_61))), inference(resolution, [status(thm)], [c_44, c_1111])).
% 3.06/1.46  tff(c_1119, plain, (![A_184]: (k5_relat_1(A_184, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_184))), inference(demodulation, [status(thm), theory('equality')], [c_731, c_1115])).
% 3.06/1.46  tff(c_1128, plain, (k5_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_1119])).
% 3.06/1.46  tff(c_1134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_624, c_1128])).
% 3.06/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.46  
% 3.06/1.46  Inference rules
% 3.06/1.46  ----------------------
% 3.06/1.46  #Ref     : 0
% 3.06/1.46  #Sup     : 249
% 3.06/1.46  #Fact    : 0
% 3.06/1.46  #Define  : 0
% 3.06/1.46  #Split   : 1
% 3.06/1.46  #Chain   : 0
% 3.06/1.46  #Close   : 0
% 3.06/1.46  
% 3.06/1.46  Ordering : KBO
% 3.06/1.46  
% 3.06/1.46  Simplification rules
% 3.06/1.46  ----------------------
% 3.06/1.46  #Subsume      : 5
% 3.06/1.46  #Demod        : 142
% 3.06/1.46  #Tautology    : 202
% 3.06/1.46  #SimpNegUnit  : 2
% 3.06/1.46  #BackRed      : 0
% 3.06/1.46  
% 3.06/1.46  #Partial instantiations: 0
% 3.06/1.46  #Strategies tried      : 1
% 3.06/1.46  
% 3.06/1.46  Timing (in seconds)
% 3.06/1.46  ----------------------
% 3.06/1.46  Preprocessing        : 0.34
% 3.06/1.46  Parsing              : 0.18
% 3.06/1.46  CNF conversion       : 0.02
% 3.06/1.46  Main loop            : 0.34
% 3.06/1.46  Inferencing          : 0.13
% 3.06/1.46  Reduction            : 0.10
% 3.06/1.46  Demodulation         : 0.07
% 3.06/1.46  BG Simplification    : 0.02
% 3.06/1.46  Subsumption          : 0.06
% 3.06/1.46  Abstraction          : 0.02
% 3.06/1.46  MUC search           : 0.00
% 3.06/1.46  Cooper               : 0.00
% 3.06/1.46  Total                : 0.71
% 3.06/1.46  Index Insertion      : 0.00
% 3.06/1.46  Index Deletion       : 0.00
% 3.06/1.46  Index Matching       : 0.00
% 3.06/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
