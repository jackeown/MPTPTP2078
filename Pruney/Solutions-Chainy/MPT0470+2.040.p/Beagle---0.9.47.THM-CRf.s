%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:06 EST 2020

% Result     : Theorem 6.83s
% Output     : CNFRefutation 6.83s
% Verified   : 
% Statistics : Number of formulae       :  123 (1028 expanded)
%              Number of leaves         :   39 ( 377 expanded)
%              Depth                    :   21
%              Number of atoms          :  206 (1781 expanded)
%              Number of equality atoms :   78 ( 679 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_38,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_42,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_28,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k4_xboole_0(A,B),C) = k4_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k4_xboole_0(A,B)) = k4_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_103,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_100,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_54,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_101,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_56,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_102,plain,(
    ! [A_64] :
      ( v1_relat_1(A_64)
      | ~ v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_106,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_102])).

tff(c_40,plain,(
    ! [A_43,B_44] :
      ( v1_relat_1(k5_relat_1(A_43,B_44))
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_18,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_148,plain,(
    ! [A_72,B_73] : k5_xboole_0(A_72,k3_xboole_0(A_72,B_73)) = k4_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_160,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_148])).

tff(c_163,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_160])).

tff(c_310,plain,(
    ! [A_91,C_92,B_93] : k4_xboole_0(k2_zfmisc_1(A_91,C_92),k2_zfmisc_1(B_93,C_92)) = k2_zfmisc_1(k4_xboole_0(A_91,B_93),C_92) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_317,plain,(
    ! [B_93,C_92] : k2_zfmisc_1(k4_xboole_0(B_93,B_93),C_92) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_163])).

tff(c_326,plain,(
    ! [C_92] : k2_zfmisc_1(k1_xboole_0,C_92) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_317])).

tff(c_16,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_52,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_50,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_782,plain,(
    ! [A_125,B_126] :
      ( k1_relat_1(k5_relat_1(A_125,B_126)) = k1_relat_1(A_125)
      | ~ r1_tarski(k2_relat_1(A_125),k1_relat_1(B_126))
      | ~ v1_relat_1(B_126)
      | ~ v1_relat_1(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_791,plain,(
    ! [B_126] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_126)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_126))
      | ~ v1_relat_1(B_126)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_782])).

tff(c_798,plain,(
    ! [B_127] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_127)) = k1_xboole_0
      | ~ v1_relat_1(B_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_16,c_52,c_791])).

tff(c_42,plain,(
    ! [A_45] :
      ( k3_xboole_0(A_45,k2_zfmisc_1(k1_relat_1(A_45),k2_relat_1(A_45))) = A_45
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_810,plain,(
    ! [B_127] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_127),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_127)))) = k5_relat_1(k1_xboole_0,B_127)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_127))
      | ~ v1_relat_1(B_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_798,c_42])).

tff(c_818,plain,(
    ! [B_128] :
      ( k5_relat_1(k1_xboole_0,B_128) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_128))
      | ~ v1_relat_1(B_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_326,c_810])).

tff(c_822,plain,(
    ! [B_44] :
      ( k5_relat_1(k1_xboole_0,B_44) = k1_xboole_0
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_40,c_818])).

tff(c_826,plain,(
    ! [B_129] :
      ( k5_relat_1(k1_xboole_0,B_129) = k1_xboole_0
      | ~ v1_relat_1(B_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_822])).

tff(c_835,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_826])).

tff(c_841,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_835])).

tff(c_842,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_844,plain,(
    ! [A_130] :
      ( v1_relat_1(A_130)
      | ~ v1_xboole_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_848,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_844])).

tff(c_900,plain,(
    ! [A_140,B_141] : k5_xboole_0(A_140,k3_xboole_0(A_140,B_141)) = k4_xboole_0(A_140,B_141) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_912,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_900])).

tff(c_915,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_912])).

tff(c_1066,plain,(
    ! [A_157,C_158,B_159] : k4_xboole_0(k2_zfmisc_1(A_157,C_158),k2_zfmisc_1(B_159,C_158)) = k2_zfmisc_1(k4_xboole_0(A_157,B_159),C_158) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1073,plain,(
    ! [B_159,C_158] : k2_zfmisc_1(k4_xboole_0(B_159,B_159),C_158) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1066,c_915])).

tff(c_1082,plain,(
    ! [C_158] : k2_zfmisc_1(k1_xboole_0,C_158) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_915,c_1073])).

tff(c_1301,plain,(
    ! [A_178,B_179] :
      ( k1_relat_1(k5_relat_1(A_178,B_179)) = k1_relat_1(A_178)
      | ~ r1_tarski(k2_relat_1(A_178),k1_relat_1(B_179))
      | ~ v1_relat_1(B_179)
      | ~ v1_relat_1(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1310,plain,(
    ! [B_179] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_179)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_179))
      | ~ v1_relat_1(B_179)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_1301])).

tff(c_1317,plain,(
    ! [B_180] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_180)) = k1_xboole_0
      | ~ v1_relat_1(B_180) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_848,c_16,c_52,c_1310])).

tff(c_1329,plain,(
    ! [B_180] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_180),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_180)))) = k5_relat_1(k1_xboole_0,B_180)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_180))
      | ~ v1_relat_1(B_180) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1317,c_42])).

tff(c_1342,plain,(
    ! [B_181] :
      ( k5_relat_1(k1_xboole_0,B_181) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_181))
      | ~ v1_relat_1(B_181) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1082,c_1329])).

tff(c_1346,plain,(
    ! [B_44] :
      ( k5_relat_1(k1_xboole_0,B_44) = k1_xboole_0
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_40,c_1342])).

tff(c_1355,plain,(
    ! [B_182] :
      ( k5_relat_1(k1_xboole_0,B_182) = k1_xboole_0
      | ~ v1_relat_1(B_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_848,c_1346])).

tff(c_1366,plain,(
    k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_848,c_1355])).

tff(c_843,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1547,plain,(
    ! [A_195,B_196,C_197] :
      ( k5_relat_1(k5_relat_1(A_195,B_196),C_197) = k5_relat_1(A_195,k5_relat_1(B_196,C_197))
      | ~ v1_relat_1(C_197)
      | ~ v1_relat_1(B_196)
      | ~ v1_relat_1(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1585,plain,(
    ! [C_197] :
      ( k5_relat_1(k1_xboole_0,k5_relat_1('#skF_1',C_197)) = k5_relat_1(k1_xboole_0,C_197)
      | ~ v1_relat_1(C_197)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_843,c_1547])).

tff(c_1597,plain,(
    ! [C_197] :
      ( k5_relat_1(k1_xboole_0,k5_relat_1('#skF_1',C_197)) = k5_relat_1(k1_xboole_0,C_197)
      | ~ v1_relat_1(C_197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_848,c_56,c_1585])).

tff(c_1582,plain,(
    ! [C_197] :
      ( k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,C_197)) = k5_relat_1(k1_xboole_0,C_197)
      | ~ v1_relat_1(C_197)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1366,c_1547])).

tff(c_1752,plain,(
    ! [C_203] :
      ( k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,C_203)) = k5_relat_1(k1_xboole_0,C_203)
      | ~ v1_relat_1(C_203) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_848,c_848,c_1582])).

tff(c_2023,plain,(
    ! [C_216] :
      ( k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,C_216)) = k5_relat_1(k1_xboole_0,k5_relat_1('#skF_1',C_216))
      | ~ v1_relat_1(k5_relat_1('#skF_1',C_216))
      | ~ v1_relat_1(C_216) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1597,c_1752])).

tff(c_2027,plain,(
    ! [B_44] :
      ( k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,B_44)) = k5_relat_1(k1_xboole_0,k5_relat_1('#skF_1',B_44))
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_2023])).

tff(c_2098,plain,(
    ! [B_219] :
      ( k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,B_219)) = k5_relat_1(k1_xboole_0,k5_relat_1('#skF_1',B_219))
      | ~ v1_relat_1(B_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2027])).

tff(c_2180,plain,
    ( k5_relat_1(k1_xboole_0,k5_relat_1('#skF_1',k1_xboole_0)) = k5_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1366,c_2098])).

tff(c_2201,plain,(
    k5_relat_1(k1_xboole_0,k5_relat_1('#skF_1',k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_848,c_1366,c_2180])).

tff(c_1015,plain,(
    ! [A_153,B_154] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_153,B_154)),k2_relat_1(B_154))
      | ~ v1_relat_1(B_154)
      | ~ v1_relat_1(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1023,plain,(
    ! [A_153] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_153,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_153) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_1015])).

tff(c_1029,plain,(
    ! [A_155] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_155,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_848,c_1023])).

tff(c_871,plain,(
    ! [B_135,A_136] :
      ( B_135 = A_136
      | ~ r1_tarski(B_135,A_136)
      | ~ r1_tarski(A_136,B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_880,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_871])).

tff(c_1035,plain,(
    ! [A_155] :
      ( k2_relat_1(k5_relat_1(A_155,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_155) ) ),
    inference(resolution,[status(thm)],[c_1029,c_880])).

tff(c_44,plain,(
    ! [A_46,B_48] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_46,B_48)),k2_relat_1(B_48))
      | ~ v1_relat_1(B_48)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3362,plain,(
    ! [A_239,B_240,C_241] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_239,k5_relat_1(B_240,C_241))),k2_relat_1(C_241))
      | ~ v1_relat_1(C_241)
      | ~ v1_relat_1(k5_relat_1(A_239,B_240))
      | ~ v1_relat_1(C_241)
      | ~ v1_relat_1(B_240)
      | ~ v1_relat_1(A_239) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1547,c_44])).

tff(c_3418,plain,(
    ! [C_197] :
      ( r1_tarski(k2_relat_1(k5_relat_1(k1_xboole_0,C_197)),k2_relat_1(C_197))
      | ~ v1_relat_1(C_197)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,'#skF_1'))
      | ~ v1_relat_1(C_197)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(C_197) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1597,c_3362])).

tff(c_3491,plain,(
    ! [C_242] :
      ( r1_tarski(k2_relat_1(k5_relat_1(k1_xboole_0,C_242)),k2_relat_1(C_242))
      | ~ v1_relat_1(C_242) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_848,c_56,c_848,c_843,c_3418])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_7837,plain,(
    ! [C_312] :
      ( k2_relat_1(k5_relat_1(k1_xboole_0,C_312)) = k2_relat_1(C_312)
      | ~ r1_tarski(k2_relat_1(C_312),k2_relat_1(k5_relat_1(k1_xboole_0,C_312)))
      | ~ v1_relat_1(C_312) ) ),
    inference(resolution,[status(thm)],[c_3491,c_6])).

tff(c_8767,plain,(
    ! [C_324] :
      ( k2_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1('#skF_1',C_324))) = k2_relat_1(k5_relat_1('#skF_1',C_324))
      | ~ r1_tarski(k2_relat_1(k5_relat_1('#skF_1',C_324)),k2_relat_1(k5_relat_1(k1_xboole_0,C_324)))
      | ~ v1_relat_1(k5_relat_1('#skF_1',C_324))
      | ~ v1_relat_1(C_324) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1597,c_7837])).

tff(c_8835,plain,
    ( k2_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1('#skF_1',k1_xboole_0))) = k2_relat_1(k5_relat_1('#skF_1',k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_relat_1(k5_relat_1('#skF_1',k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1035,c_8767])).

tff(c_8861,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k1_xboole_0)) = k1_xboole_0
    | ~ v1_relat_1(k5_relat_1('#skF_1',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_848,c_16,c_50,c_2201,c_8835])).

tff(c_8866,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_1',k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_8861])).

tff(c_8869,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_8866])).

tff(c_8873,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_848,c_8869])).

tff(c_8875,plain,(
    v1_relat_1(k5_relat_1('#skF_1',k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_8861])).

tff(c_1103,plain,(
    ! [C_161,A_162,B_163] : k4_xboole_0(k2_zfmisc_1(C_161,A_162),k2_zfmisc_1(C_161,B_163)) = k2_zfmisc_1(C_161,k4_xboole_0(A_162,B_163)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_32,plain,(
    ! [A_37,C_39,B_38] : k4_xboole_0(k2_zfmisc_1(A_37,C_39),k2_zfmisc_1(B_38,C_39)) = k2_zfmisc_1(k4_xboole_0(A_37,B_38),C_39) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1110,plain,(
    ! [C_161,B_163] : k2_zfmisc_1(k4_xboole_0(C_161,C_161),B_163) = k2_zfmisc_1(C_161,k4_xboole_0(B_163,B_163)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1103,c_32])).

tff(c_1133,plain,(
    ! [C_161] : k2_zfmisc_1(C_161,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1082,c_915,c_915,c_1110])).

tff(c_8874,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k1_xboole_0)) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8861])).

tff(c_8938,plain,
    ( k3_xboole_0(k5_relat_1('#skF_1',k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1('#skF_1',k1_xboole_0)),k1_xboole_0)) = k5_relat_1('#skF_1',k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1('#skF_1',k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8874,c_42])).

tff(c_8982,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8875,c_14,c_1133,c_8938])).

tff(c_8984,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_842,c_8982])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:31:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.83/2.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.83/2.46  
% 6.83/2.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.83/2.47  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 6.83/2.47  
% 6.83/2.47  %Foreground sorts:
% 6.83/2.47  
% 6.83/2.47  
% 6.83/2.47  %Background operators:
% 6.83/2.47  
% 6.83/2.47  
% 6.83/2.47  %Foreground operators:
% 6.83/2.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.83/2.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.83/2.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.83/2.47  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.83/2.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.83/2.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.83/2.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.83/2.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.83/2.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.83/2.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.83/2.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.83/2.47  tff('#skF_1', type, '#skF_1': $i).
% 6.83/2.47  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.83/2.47  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.83/2.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.83/2.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.83/2.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.83/2.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.83/2.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.83/2.47  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.83/2.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.83/2.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.83/2.47  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.83/2.47  
% 6.83/2.48  tff(f_110, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 6.83/2.48  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.83/2.48  tff(f_64, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 6.83/2.48  tff(f_70, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 6.83/2.48  tff(f_38, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 6.83/2.48  tff(f_42, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.83/2.48  tff(f_28, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 6.83/2.48  tff(f_36, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.83/2.48  tff(f_58, axiom, (![A, B, C]: ((k2_zfmisc_1(k4_xboole_0(A, B), C) = k4_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k4_xboole_0(A, B)) = k4_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 6.83/2.48  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.83/2.48  tff(f_103, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 6.83/2.48  tff(f_90, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 6.83/2.48  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 6.83/2.48  tff(f_100, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 6.83/2.48  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 6.83/2.48  tff(f_34, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.83/2.48  tff(c_54, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.83/2.48  tff(c_101, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_54])).
% 6.83/2.48  tff(c_56, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.83/2.48  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.83/2.48  tff(c_102, plain, (![A_64]: (v1_relat_1(A_64) | ~v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.83/2.48  tff(c_106, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_102])).
% 6.83/2.48  tff(c_40, plain, (![A_43, B_44]: (v1_relat_1(k5_relat_1(A_43, B_44)) | ~v1_relat_1(B_44) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.83/2.48  tff(c_14, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.83/2.48  tff(c_18, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.83/2.48  tff(c_4, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 6.83/2.48  tff(c_148, plain, (![A_72, B_73]: (k5_xboole_0(A_72, k3_xboole_0(A_72, B_73))=k4_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.83/2.48  tff(c_160, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_4, c_148])).
% 6.83/2.48  tff(c_163, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_160])).
% 6.83/2.48  tff(c_310, plain, (![A_91, C_92, B_93]: (k4_xboole_0(k2_zfmisc_1(A_91, C_92), k2_zfmisc_1(B_93, C_92))=k2_zfmisc_1(k4_xboole_0(A_91, B_93), C_92))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.83/2.48  tff(c_317, plain, (![B_93, C_92]: (k2_zfmisc_1(k4_xboole_0(B_93, B_93), C_92)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_310, c_163])).
% 6.83/2.48  tff(c_326, plain, (![C_92]: (k2_zfmisc_1(k1_xboole_0, C_92)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_163, c_317])).
% 6.83/2.48  tff(c_16, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.83/2.48  tff(c_52, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.83/2.48  tff(c_50, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.83/2.48  tff(c_782, plain, (![A_125, B_126]: (k1_relat_1(k5_relat_1(A_125, B_126))=k1_relat_1(A_125) | ~r1_tarski(k2_relat_1(A_125), k1_relat_1(B_126)) | ~v1_relat_1(B_126) | ~v1_relat_1(A_125))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.83/2.48  tff(c_791, plain, (![B_126]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_126))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_126)) | ~v1_relat_1(B_126) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_50, c_782])).
% 6.83/2.48  tff(c_798, plain, (![B_127]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_127))=k1_xboole_0 | ~v1_relat_1(B_127))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_16, c_52, c_791])).
% 6.83/2.48  tff(c_42, plain, (![A_45]: (k3_xboole_0(A_45, k2_zfmisc_1(k1_relat_1(A_45), k2_relat_1(A_45)))=A_45 | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.83/2.48  tff(c_810, plain, (![B_127]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_127), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_127))))=k5_relat_1(k1_xboole_0, B_127) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_127)) | ~v1_relat_1(B_127))), inference(superposition, [status(thm), theory('equality')], [c_798, c_42])).
% 6.83/2.48  tff(c_818, plain, (![B_128]: (k5_relat_1(k1_xboole_0, B_128)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_128)) | ~v1_relat_1(B_128))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_326, c_810])).
% 6.83/2.48  tff(c_822, plain, (![B_44]: (k5_relat_1(k1_xboole_0, B_44)=k1_xboole_0 | ~v1_relat_1(B_44) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_40, c_818])).
% 6.83/2.48  tff(c_826, plain, (![B_129]: (k5_relat_1(k1_xboole_0, B_129)=k1_xboole_0 | ~v1_relat_1(B_129))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_822])).
% 6.83/2.48  tff(c_835, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_826])).
% 6.83/2.48  tff(c_841, plain, $false, inference(negUnitSimplification, [status(thm)], [c_101, c_835])).
% 6.83/2.48  tff(c_842, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 6.83/2.48  tff(c_844, plain, (![A_130]: (v1_relat_1(A_130) | ~v1_xboole_0(A_130))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.83/2.48  tff(c_848, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_844])).
% 6.83/2.48  tff(c_900, plain, (![A_140, B_141]: (k5_xboole_0(A_140, k3_xboole_0(A_140, B_141))=k4_xboole_0(A_140, B_141))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.83/2.48  tff(c_912, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_4, c_900])).
% 6.83/2.48  tff(c_915, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_912])).
% 6.83/2.48  tff(c_1066, plain, (![A_157, C_158, B_159]: (k4_xboole_0(k2_zfmisc_1(A_157, C_158), k2_zfmisc_1(B_159, C_158))=k2_zfmisc_1(k4_xboole_0(A_157, B_159), C_158))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.83/2.49  tff(c_1073, plain, (![B_159, C_158]: (k2_zfmisc_1(k4_xboole_0(B_159, B_159), C_158)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1066, c_915])).
% 6.83/2.49  tff(c_1082, plain, (![C_158]: (k2_zfmisc_1(k1_xboole_0, C_158)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_915, c_1073])).
% 6.83/2.49  tff(c_1301, plain, (![A_178, B_179]: (k1_relat_1(k5_relat_1(A_178, B_179))=k1_relat_1(A_178) | ~r1_tarski(k2_relat_1(A_178), k1_relat_1(B_179)) | ~v1_relat_1(B_179) | ~v1_relat_1(A_178))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.83/2.49  tff(c_1310, plain, (![B_179]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_179))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_179)) | ~v1_relat_1(B_179) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_50, c_1301])).
% 6.83/2.49  tff(c_1317, plain, (![B_180]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_180))=k1_xboole_0 | ~v1_relat_1(B_180))), inference(demodulation, [status(thm), theory('equality')], [c_848, c_16, c_52, c_1310])).
% 6.83/2.49  tff(c_1329, plain, (![B_180]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_180), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_180))))=k5_relat_1(k1_xboole_0, B_180) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_180)) | ~v1_relat_1(B_180))), inference(superposition, [status(thm), theory('equality')], [c_1317, c_42])).
% 6.83/2.49  tff(c_1342, plain, (![B_181]: (k5_relat_1(k1_xboole_0, B_181)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_181)) | ~v1_relat_1(B_181))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1082, c_1329])).
% 6.83/2.49  tff(c_1346, plain, (![B_44]: (k5_relat_1(k1_xboole_0, B_44)=k1_xboole_0 | ~v1_relat_1(B_44) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_40, c_1342])).
% 6.83/2.49  tff(c_1355, plain, (![B_182]: (k5_relat_1(k1_xboole_0, B_182)=k1_xboole_0 | ~v1_relat_1(B_182))), inference(demodulation, [status(thm), theory('equality')], [c_848, c_1346])).
% 6.83/2.49  tff(c_1366, plain, (k5_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_848, c_1355])).
% 6.83/2.49  tff(c_843, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 6.83/2.49  tff(c_1547, plain, (![A_195, B_196, C_197]: (k5_relat_1(k5_relat_1(A_195, B_196), C_197)=k5_relat_1(A_195, k5_relat_1(B_196, C_197)) | ~v1_relat_1(C_197) | ~v1_relat_1(B_196) | ~v1_relat_1(A_195))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.83/2.49  tff(c_1585, plain, (![C_197]: (k5_relat_1(k1_xboole_0, k5_relat_1('#skF_1', C_197))=k5_relat_1(k1_xboole_0, C_197) | ~v1_relat_1(C_197) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_843, c_1547])).
% 6.83/2.49  tff(c_1597, plain, (![C_197]: (k5_relat_1(k1_xboole_0, k5_relat_1('#skF_1', C_197))=k5_relat_1(k1_xboole_0, C_197) | ~v1_relat_1(C_197))), inference(demodulation, [status(thm), theory('equality')], [c_848, c_56, c_1585])).
% 6.83/2.49  tff(c_1582, plain, (![C_197]: (k5_relat_1(k1_xboole_0, k5_relat_1(k1_xboole_0, C_197))=k5_relat_1(k1_xboole_0, C_197) | ~v1_relat_1(C_197) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1366, c_1547])).
% 6.83/2.49  tff(c_1752, plain, (![C_203]: (k5_relat_1(k1_xboole_0, k5_relat_1(k1_xboole_0, C_203))=k5_relat_1(k1_xboole_0, C_203) | ~v1_relat_1(C_203))), inference(demodulation, [status(thm), theory('equality')], [c_848, c_848, c_1582])).
% 6.83/2.49  tff(c_2023, plain, (![C_216]: (k5_relat_1(k1_xboole_0, k5_relat_1(k1_xboole_0, C_216))=k5_relat_1(k1_xboole_0, k5_relat_1('#skF_1', C_216)) | ~v1_relat_1(k5_relat_1('#skF_1', C_216)) | ~v1_relat_1(C_216))), inference(superposition, [status(thm), theory('equality')], [c_1597, c_1752])).
% 6.83/2.49  tff(c_2027, plain, (![B_44]: (k5_relat_1(k1_xboole_0, k5_relat_1(k1_xboole_0, B_44))=k5_relat_1(k1_xboole_0, k5_relat_1('#skF_1', B_44)) | ~v1_relat_1(B_44) | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_2023])).
% 6.83/2.49  tff(c_2098, plain, (![B_219]: (k5_relat_1(k1_xboole_0, k5_relat_1(k1_xboole_0, B_219))=k5_relat_1(k1_xboole_0, k5_relat_1('#skF_1', B_219)) | ~v1_relat_1(B_219))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2027])).
% 6.83/2.49  tff(c_2180, plain, (k5_relat_1(k1_xboole_0, k5_relat_1('#skF_1', k1_xboole_0))=k5_relat_1(k1_xboole_0, k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1366, c_2098])).
% 6.83/2.49  tff(c_2201, plain, (k5_relat_1(k1_xboole_0, k5_relat_1('#skF_1', k1_xboole_0))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_848, c_1366, c_2180])).
% 6.83/2.49  tff(c_1015, plain, (![A_153, B_154]: (r1_tarski(k2_relat_1(k5_relat_1(A_153, B_154)), k2_relat_1(B_154)) | ~v1_relat_1(B_154) | ~v1_relat_1(A_153))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.83/2.49  tff(c_1023, plain, (![A_153]: (r1_tarski(k2_relat_1(k5_relat_1(A_153, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_153))), inference(superposition, [status(thm), theory('equality')], [c_50, c_1015])).
% 6.83/2.49  tff(c_1029, plain, (![A_155]: (r1_tarski(k2_relat_1(k5_relat_1(A_155, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_155))), inference(demodulation, [status(thm), theory('equality')], [c_848, c_1023])).
% 6.83/2.49  tff(c_871, plain, (![B_135, A_136]: (B_135=A_136 | ~r1_tarski(B_135, A_136) | ~r1_tarski(A_136, B_135))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.83/2.49  tff(c_880, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_871])).
% 6.83/2.49  tff(c_1035, plain, (![A_155]: (k2_relat_1(k5_relat_1(A_155, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_155))), inference(resolution, [status(thm)], [c_1029, c_880])).
% 6.83/2.49  tff(c_44, plain, (![A_46, B_48]: (r1_tarski(k2_relat_1(k5_relat_1(A_46, B_48)), k2_relat_1(B_48)) | ~v1_relat_1(B_48) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.83/2.49  tff(c_3362, plain, (![A_239, B_240, C_241]: (r1_tarski(k2_relat_1(k5_relat_1(A_239, k5_relat_1(B_240, C_241))), k2_relat_1(C_241)) | ~v1_relat_1(C_241) | ~v1_relat_1(k5_relat_1(A_239, B_240)) | ~v1_relat_1(C_241) | ~v1_relat_1(B_240) | ~v1_relat_1(A_239))), inference(superposition, [status(thm), theory('equality')], [c_1547, c_44])).
% 6.83/2.49  tff(c_3418, plain, (![C_197]: (r1_tarski(k2_relat_1(k5_relat_1(k1_xboole_0, C_197)), k2_relat_1(C_197)) | ~v1_relat_1(C_197) | ~v1_relat_1(k5_relat_1(k1_xboole_0, '#skF_1')) | ~v1_relat_1(C_197) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(C_197))), inference(superposition, [status(thm), theory('equality')], [c_1597, c_3362])).
% 6.83/2.49  tff(c_3491, plain, (![C_242]: (r1_tarski(k2_relat_1(k5_relat_1(k1_xboole_0, C_242)), k2_relat_1(C_242)) | ~v1_relat_1(C_242))), inference(demodulation, [status(thm), theory('equality')], [c_848, c_56, c_848, c_843, c_3418])).
% 6.83/2.49  tff(c_6, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.83/2.49  tff(c_7837, plain, (![C_312]: (k2_relat_1(k5_relat_1(k1_xboole_0, C_312))=k2_relat_1(C_312) | ~r1_tarski(k2_relat_1(C_312), k2_relat_1(k5_relat_1(k1_xboole_0, C_312))) | ~v1_relat_1(C_312))), inference(resolution, [status(thm)], [c_3491, c_6])).
% 6.83/2.49  tff(c_8767, plain, (![C_324]: (k2_relat_1(k5_relat_1(k1_xboole_0, k5_relat_1('#skF_1', C_324)))=k2_relat_1(k5_relat_1('#skF_1', C_324)) | ~r1_tarski(k2_relat_1(k5_relat_1('#skF_1', C_324)), k2_relat_1(k5_relat_1(k1_xboole_0, C_324))) | ~v1_relat_1(k5_relat_1('#skF_1', C_324)) | ~v1_relat_1(C_324))), inference(superposition, [status(thm), theory('equality')], [c_1597, c_7837])).
% 6.83/2.49  tff(c_8835, plain, (k2_relat_1(k5_relat_1(k1_xboole_0, k5_relat_1('#skF_1', k1_xboole_0)))=k2_relat_1(k5_relat_1('#skF_1', k1_xboole_0)) | ~r1_tarski(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, k1_xboole_0))) | ~v1_relat_1(k5_relat_1('#skF_1', k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1035, c_8767])).
% 6.83/2.49  tff(c_8861, plain, (k2_relat_1(k5_relat_1('#skF_1', k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(k5_relat_1('#skF_1', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_848, c_16, c_50, c_2201, c_8835])).
% 6.83/2.49  tff(c_8866, plain, (~v1_relat_1(k5_relat_1('#skF_1', k1_xboole_0))), inference(splitLeft, [status(thm)], [c_8861])).
% 6.83/2.49  tff(c_8869, plain, (~v1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_40, c_8866])).
% 6.83/2.49  tff(c_8873, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_848, c_8869])).
% 6.83/2.49  tff(c_8875, plain, (v1_relat_1(k5_relat_1('#skF_1', k1_xboole_0))), inference(splitRight, [status(thm)], [c_8861])).
% 6.83/2.49  tff(c_1103, plain, (![C_161, A_162, B_163]: (k4_xboole_0(k2_zfmisc_1(C_161, A_162), k2_zfmisc_1(C_161, B_163))=k2_zfmisc_1(C_161, k4_xboole_0(A_162, B_163)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.83/2.49  tff(c_32, plain, (![A_37, C_39, B_38]: (k4_xboole_0(k2_zfmisc_1(A_37, C_39), k2_zfmisc_1(B_38, C_39))=k2_zfmisc_1(k4_xboole_0(A_37, B_38), C_39))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.83/2.49  tff(c_1110, plain, (![C_161, B_163]: (k2_zfmisc_1(k4_xboole_0(C_161, C_161), B_163)=k2_zfmisc_1(C_161, k4_xboole_0(B_163, B_163)))), inference(superposition, [status(thm), theory('equality')], [c_1103, c_32])).
% 6.83/2.49  tff(c_1133, plain, (![C_161]: (k2_zfmisc_1(C_161, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1082, c_915, c_915, c_1110])).
% 6.83/2.49  tff(c_8874, plain, (k2_relat_1(k5_relat_1('#skF_1', k1_xboole_0))=k1_xboole_0), inference(splitRight, [status(thm)], [c_8861])).
% 6.83/2.49  tff(c_8938, plain, (k3_xboole_0(k5_relat_1('#skF_1', k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1('#skF_1', k1_xboole_0)), k1_xboole_0))=k5_relat_1('#skF_1', k1_xboole_0) | ~v1_relat_1(k5_relat_1('#skF_1', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8874, c_42])).
% 6.83/2.49  tff(c_8982, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8875, c_14, c_1133, c_8938])).
% 6.83/2.49  tff(c_8984, plain, $false, inference(negUnitSimplification, [status(thm)], [c_842, c_8982])).
% 6.83/2.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.83/2.49  
% 6.83/2.49  Inference rules
% 6.83/2.49  ----------------------
% 6.83/2.49  #Ref     : 0
% 6.83/2.49  #Sup     : 2061
% 6.83/2.49  #Fact    : 0
% 6.83/2.49  #Define  : 0
% 6.83/2.49  #Split   : 2
% 6.83/2.49  #Chain   : 0
% 6.83/2.49  #Close   : 0
% 6.83/2.49  
% 6.83/2.49  Ordering : KBO
% 6.83/2.49  
% 6.83/2.49  Simplification rules
% 6.83/2.49  ----------------------
% 6.83/2.49  #Subsume      : 299
% 6.83/2.49  #Demod        : 2857
% 6.83/2.49  #Tautology    : 1031
% 6.83/2.49  #SimpNegUnit  : 2
% 6.83/2.49  #BackRed      : 6
% 6.83/2.49  
% 6.83/2.49  #Partial instantiations: 0
% 6.83/2.49  #Strategies tried      : 1
% 6.83/2.49  
% 6.83/2.49  Timing (in seconds)
% 6.83/2.49  ----------------------
% 6.83/2.50  Preprocessing        : 0.33
% 6.83/2.50  Parsing              : 0.18
% 6.83/2.50  CNF conversion       : 0.02
% 6.83/2.50  Main loop            : 1.37
% 6.83/2.50  Inferencing          : 0.42
% 6.83/2.50  Reduction            : 0.54
% 6.83/2.50  Demodulation         : 0.41
% 6.83/2.50  BG Simplification    : 0.06
% 6.83/2.50  Subsumption          : 0.29
% 6.83/2.50  Abstraction          : 0.09
% 6.83/2.50  MUC search           : 0.00
% 6.83/2.50  Cooper               : 0.00
% 6.83/2.50  Total                : 1.75
% 6.83/2.50  Index Insertion      : 0.00
% 6.83/2.50  Index Deletion       : 0.00
% 6.83/2.50  Index Matching       : 0.00
% 6.83/2.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
