%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:15 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 129 expanded)
%              Number of leaves         :   41 (  61 expanded)
%              Depth                    :   11
%              Number of atoms          :  124 ( 196 expanded)
%              Number of equality atoms :   39 (  61 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_42,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_81,axiom,(
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

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_40,axiom,(
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

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

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

tff(c_52,plain,
    ( k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_80,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_54,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_38,plain,(
    ! [A_30] :
      ( r2_hidden('#skF_1'(A_30),A_30)
      | v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_16,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_195,plain,(
    ! [A_85,C_86,B_87] :
      ( ~ r2_hidden(A_85,C_86)
      | ~ r1_xboole_0(k2_tarski(A_85,B_87),C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_210,plain,(
    ! [A_91] : ~ r2_hidden(A_91,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_195])).

tff(c_215,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_38,c_210])).

tff(c_40,plain,(
    ! [A_48,B_49] :
      ( v1_relat_1(k5_relat_1(A_48,B_49))
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_12,plain,(
    ! [A_4] : k3_xboole_0(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_87,plain,(
    ! [A_65,B_66] :
      ( v1_xboole_0(k2_zfmisc_1(A_65,B_66))
      | ~ v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_127,plain,(
    ! [A_72,B_73] :
      ( k2_zfmisc_1(A_72,B_73) = k1_xboole_0
      | ~ v1_xboole_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_87,c_4])).

tff(c_136,plain,(
    ! [B_73] : k2_zfmisc_1(k1_xboole_0,B_73) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_127])).

tff(c_14,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_50,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_48,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_626,plain,(
    ! [A_127,B_128] :
      ( k1_relat_1(k5_relat_1(A_127,B_128)) = k1_relat_1(A_127)
      | ~ r1_tarski(k2_relat_1(A_127),k1_relat_1(B_128))
      | ~ v1_relat_1(B_128)
      | ~ v1_relat_1(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_635,plain,(
    ! [B_128] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_128)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_128))
      | ~ v1_relat_1(B_128)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_626])).

tff(c_666,plain,(
    ! [B_129] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_129)) = k1_xboole_0
      | ~ v1_relat_1(B_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_14,c_50,c_635])).

tff(c_42,plain,(
    ! [A_50] :
      ( k3_xboole_0(A_50,k2_zfmisc_1(k1_relat_1(A_50),k2_relat_1(A_50))) = A_50
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_675,plain,(
    ! [B_129] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_129),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_129)))) = k5_relat_1(k1_xboole_0,B_129)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_129))
      | ~ v1_relat_1(B_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_666,c_42])).

tff(c_687,plain,(
    ! [B_130] :
      ( k5_relat_1(k1_xboole_0,B_130) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_130))
      | ~ v1_relat_1(B_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_136,c_675])).

tff(c_694,plain,(
    ! [B_49] :
      ( k5_relat_1(k1_xboole_0,B_49) = k1_xboole_0
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_40,c_687])).

tff(c_747,plain,(
    ! [B_133] :
      ( k5_relat_1(k1_xboole_0,B_133) = k1_xboole_0
      | ~ v1_relat_1(B_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_694])).

tff(c_756,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_747])).

tff(c_763,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_756])).

tff(c_764,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_876,plain,(
    ! [A_156,C_157,B_158] :
      ( ~ r2_hidden(A_156,C_157)
      | ~ r1_xboole_0(k2_tarski(A_156,B_158),C_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_882,plain,(
    ! [A_159] : ~ r2_hidden(A_159,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_876])).

tff(c_887,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_38,c_882])).

tff(c_771,plain,(
    ! [A_135,B_136] :
      ( v1_xboole_0(k2_zfmisc_1(A_135,B_136))
      | ~ v1_xboole_0(B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_781,plain,(
    ! [A_139,B_140] :
      ( k2_zfmisc_1(A_139,B_140) = k1_xboole_0
      | ~ v1_xboole_0(B_140) ) ),
    inference(resolution,[status(thm)],[c_771,c_4])).

tff(c_790,plain,(
    ! [A_139] : k2_zfmisc_1(A_139,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_781])).

tff(c_1202,plain,(
    ! [A_181,B_182] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_181,B_182)),k2_relat_1(B_182))
      | ~ v1_relat_1(B_182)
      | ~ v1_relat_1(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1210,plain,(
    ! [A_181] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_181,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_181) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1202])).

tff(c_1216,plain,(
    ! [A_183] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_183,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_183) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_887,c_1210])).

tff(c_866,plain,(
    ! [B_154,A_155] :
      ( B_154 = A_155
      | ~ r1_tarski(B_154,A_155)
      | ~ r1_tarski(A_155,B_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_875,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_866])).

tff(c_1226,plain,(
    ! [A_184] :
      ( k2_relat_1(k5_relat_1(A_184,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_184) ) ),
    inference(resolution,[status(thm)],[c_1216,c_875])).

tff(c_1241,plain,(
    ! [A_184] :
      ( k3_xboole_0(k5_relat_1(A_184,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(A_184,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(A_184,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_184,k1_xboole_0))
      | ~ v1_relat_1(A_184) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1226,c_42])).

tff(c_1260,plain,(
    ! [A_190] :
      ( k5_relat_1(A_190,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_190,k1_xboole_0))
      | ~ v1_relat_1(A_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_790,c_1241])).

tff(c_1264,plain,(
    ! [A_48] :
      ( k5_relat_1(A_48,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_48) ) ),
    inference(resolution,[status(thm)],[c_40,c_1260])).

tff(c_1268,plain,(
    ! [A_191] :
      ( k5_relat_1(A_191,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_191) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_887,c_1264])).

tff(c_1277,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_1268])).

tff(c_1283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_764,c_1277])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:56:10 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.37/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.56  
% 3.37/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.56  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.37/1.56  
% 3.37/1.56  %Foreground sorts:
% 3.37/1.56  
% 3.37/1.56  
% 3.37/1.56  %Background operators:
% 3.37/1.56  
% 3.37/1.56  
% 3.37/1.56  %Foreground operators:
% 3.37/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.37/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.37/1.56  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.37/1.56  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.37/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.37/1.56  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.37/1.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.37/1.56  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.37/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.37/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.37/1.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.37/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.37/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.37/1.56  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.37/1.56  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.37/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.37/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.37/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.37/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.37/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.37/1.56  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.37/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.37/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.37/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.37/1.56  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.37/1.56  
% 3.37/1.58  tff(f_111, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 3.37/1.58  tff(f_75, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 3.37/1.58  tff(f_42, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.37/1.58  tff(f_63, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 3.37/1.58  tff(f_81, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.37/1.58  tff(f_38, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.37/1.58  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.37/1.58  tff(f_58, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 3.37/1.58  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.37/1.58  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.37/1.58  tff(f_104, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.37/1.58  tff(f_101, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 3.37/1.58  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 3.37/1.58  tff(f_54, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 3.37/1.58  tff(f_92, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 3.37/1.58  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.37/1.58  tff(c_52, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.37/1.58  tff(c_80, plain, (k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_52])).
% 3.37/1.58  tff(c_54, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.37/1.58  tff(c_38, plain, (![A_30]: (r2_hidden('#skF_1'(A_30), A_30) | v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.37/1.58  tff(c_16, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.37/1.58  tff(c_195, plain, (![A_85, C_86, B_87]: (~r2_hidden(A_85, C_86) | ~r1_xboole_0(k2_tarski(A_85, B_87), C_86))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.37/1.58  tff(c_210, plain, (![A_91]: (~r2_hidden(A_91, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_195])).
% 3.37/1.58  tff(c_215, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_210])).
% 3.37/1.58  tff(c_40, plain, (![A_48, B_49]: (v1_relat_1(k5_relat_1(A_48, B_49)) | ~v1_relat_1(B_49) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.37/1.58  tff(c_12, plain, (![A_4]: (k3_xboole_0(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.37/1.58  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.37/1.58  tff(c_87, plain, (![A_65, B_66]: (v1_xboole_0(k2_zfmisc_1(A_65, B_66)) | ~v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.37/1.58  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.37/1.58  tff(c_127, plain, (![A_72, B_73]: (k2_zfmisc_1(A_72, B_73)=k1_xboole_0 | ~v1_xboole_0(A_72))), inference(resolution, [status(thm)], [c_87, c_4])).
% 3.37/1.58  tff(c_136, plain, (![B_73]: (k2_zfmisc_1(k1_xboole_0, B_73)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_127])).
% 3.37/1.58  tff(c_14, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.37/1.58  tff(c_50, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.37/1.58  tff(c_48, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.37/1.58  tff(c_626, plain, (![A_127, B_128]: (k1_relat_1(k5_relat_1(A_127, B_128))=k1_relat_1(A_127) | ~r1_tarski(k2_relat_1(A_127), k1_relat_1(B_128)) | ~v1_relat_1(B_128) | ~v1_relat_1(A_127))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.37/1.58  tff(c_635, plain, (![B_128]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_128))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_128)) | ~v1_relat_1(B_128) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_48, c_626])).
% 3.37/1.58  tff(c_666, plain, (![B_129]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_129))=k1_xboole_0 | ~v1_relat_1(B_129))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_14, c_50, c_635])).
% 3.37/1.58  tff(c_42, plain, (![A_50]: (k3_xboole_0(A_50, k2_zfmisc_1(k1_relat_1(A_50), k2_relat_1(A_50)))=A_50 | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.37/1.58  tff(c_675, plain, (![B_129]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_129), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_129))))=k5_relat_1(k1_xboole_0, B_129) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_129)) | ~v1_relat_1(B_129))), inference(superposition, [status(thm), theory('equality')], [c_666, c_42])).
% 3.37/1.58  tff(c_687, plain, (![B_130]: (k5_relat_1(k1_xboole_0, B_130)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_130)) | ~v1_relat_1(B_130))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_136, c_675])).
% 3.37/1.58  tff(c_694, plain, (![B_49]: (k5_relat_1(k1_xboole_0, B_49)=k1_xboole_0 | ~v1_relat_1(B_49) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_40, c_687])).
% 3.37/1.58  tff(c_747, plain, (![B_133]: (k5_relat_1(k1_xboole_0, B_133)=k1_xboole_0 | ~v1_relat_1(B_133))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_694])).
% 3.37/1.58  tff(c_756, plain, (k5_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_747])).
% 3.37/1.58  tff(c_763, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_756])).
% 3.37/1.58  tff(c_764, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 3.37/1.58  tff(c_876, plain, (![A_156, C_157, B_158]: (~r2_hidden(A_156, C_157) | ~r1_xboole_0(k2_tarski(A_156, B_158), C_157))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.37/1.58  tff(c_882, plain, (![A_159]: (~r2_hidden(A_159, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_876])).
% 3.37/1.58  tff(c_887, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_882])).
% 3.37/1.58  tff(c_771, plain, (![A_135, B_136]: (v1_xboole_0(k2_zfmisc_1(A_135, B_136)) | ~v1_xboole_0(B_136))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.37/1.58  tff(c_781, plain, (![A_139, B_140]: (k2_zfmisc_1(A_139, B_140)=k1_xboole_0 | ~v1_xboole_0(B_140))), inference(resolution, [status(thm)], [c_771, c_4])).
% 3.37/1.58  tff(c_790, plain, (![A_139]: (k2_zfmisc_1(A_139, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_781])).
% 3.37/1.58  tff(c_1202, plain, (![A_181, B_182]: (r1_tarski(k2_relat_1(k5_relat_1(A_181, B_182)), k2_relat_1(B_182)) | ~v1_relat_1(B_182) | ~v1_relat_1(A_181))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.37/1.58  tff(c_1210, plain, (![A_181]: (r1_tarski(k2_relat_1(k5_relat_1(A_181, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_181))), inference(superposition, [status(thm), theory('equality')], [c_48, c_1202])).
% 3.37/1.58  tff(c_1216, plain, (![A_183]: (r1_tarski(k2_relat_1(k5_relat_1(A_183, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_183))), inference(demodulation, [status(thm), theory('equality')], [c_887, c_1210])).
% 3.37/1.58  tff(c_866, plain, (![B_154, A_155]: (B_154=A_155 | ~r1_tarski(B_154, A_155) | ~r1_tarski(A_155, B_154))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.37/1.58  tff(c_875, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_866])).
% 3.37/1.58  tff(c_1226, plain, (![A_184]: (k2_relat_1(k5_relat_1(A_184, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_184))), inference(resolution, [status(thm)], [c_1216, c_875])).
% 3.37/1.58  tff(c_1241, plain, (![A_184]: (k3_xboole_0(k5_relat_1(A_184, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(A_184, k1_xboole_0)), k1_xboole_0))=k5_relat_1(A_184, k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_184, k1_xboole_0)) | ~v1_relat_1(A_184))), inference(superposition, [status(thm), theory('equality')], [c_1226, c_42])).
% 3.37/1.58  tff(c_1260, plain, (![A_190]: (k5_relat_1(A_190, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_190, k1_xboole_0)) | ~v1_relat_1(A_190))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_790, c_1241])).
% 3.37/1.58  tff(c_1264, plain, (![A_48]: (k5_relat_1(A_48, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_48))), inference(resolution, [status(thm)], [c_40, c_1260])).
% 3.37/1.58  tff(c_1268, plain, (![A_191]: (k5_relat_1(A_191, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_191))), inference(demodulation, [status(thm), theory('equality')], [c_887, c_1264])).
% 3.37/1.58  tff(c_1277, plain, (k5_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_1268])).
% 3.37/1.58  tff(c_1283, plain, $false, inference(negUnitSimplification, [status(thm)], [c_764, c_1277])).
% 3.37/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.58  
% 3.37/1.58  Inference rules
% 3.37/1.58  ----------------------
% 3.37/1.58  #Ref     : 1
% 3.37/1.58  #Sup     : 282
% 3.37/1.58  #Fact    : 0
% 3.37/1.58  #Define  : 0
% 3.37/1.58  #Split   : 1
% 3.37/1.58  #Chain   : 0
% 3.37/1.58  #Close   : 0
% 3.37/1.58  
% 3.37/1.58  Ordering : KBO
% 3.37/1.58  
% 3.37/1.58  Simplification rules
% 3.37/1.58  ----------------------
% 3.37/1.58  #Subsume      : 5
% 3.37/1.58  #Demod        : 192
% 3.37/1.58  #Tautology    : 232
% 3.37/1.58  #SimpNegUnit  : 2
% 3.37/1.58  #BackRed      : 0
% 3.37/1.58  
% 3.37/1.58  #Partial instantiations: 0
% 3.37/1.58  #Strategies tried      : 1
% 3.37/1.58  
% 3.37/1.58  Timing (in seconds)
% 3.37/1.58  ----------------------
% 3.37/1.58  Preprocessing        : 0.35
% 3.37/1.58  Parsing              : 0.19
% 3.37/1.58  CNF conversion       : 0.02
% 3.37/1.59  Main loop            : 0.44
% 3.37/1.59  Inferencing          : 0.17
% 3.37/1.59  Reduction            : 0.13
% 3.37/1.59  Demodulation         : 0.09
% 3.37/1.59  BG Simplification    : 0.02
% 3.37/1.59  Subsumption          : 0.08
% 3.37/1.59  Abstraction          : 0.02
% 3.37/1.59  MUC search           : 0.00
% 3.37/1.59  Cooper               : 0.00
% 3.37/1.59  Total                : 0.84
% 3.37/1.59  Index Insertion      : 0.00
% 3.37/1.59  Index Deletion       : 0.00
% 3.37/1.59  Index Matching       : 0.00
% 3.37/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
