%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:13 EST 2020

% Result     : Theorem 9.48s
% Output     : CNFRefutation 9.69s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 206 expanded)
%              Number of leaves         :   35 (  87 expanded)
%              Depth                    :   16
%              Number of atoms          :  128 ( 479 expanded)
%              Number of equality atoms :   31 (  87 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B)
        & ! [D] :
            ( ( r1_tarski(A,D)
              & r1_tarski(C,D) )
           => r1_tarski(B,D) ) )
     => B = k2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_xboole_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_44,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_52,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_46,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_11,B_12,C_13] :
      ( r1_tarski(A_11,'#skF_1'(A_11,B_12,C_13))
      | k2_xboole_0(A_11,C_13) = B_12
      | ~ r1_tarski(C_13,B_12)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4562,plain,(
    ! [B_260,A_261,C_262] :
      ( ~ r1_tarski(B_260,'#skF_1'(A_261,B_260,C_262))
      | k2_xboole_0(A_261,C_262) = B_260
      | ~ r1_tarski(C_262,B_260)
      | ~ r1_tarski(A_261,B_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4566,plain,(
    ! [B_12,C_13] :
      ( k2_xboole_0(B_12,C_13) = B_12
      | ~ r1_tarski(C_13,B_12)
      | ~ r1_tarski(B_12,B_12) ) ),
    inference(resolution,[status(thm)],[c_18,c_4562])).

tff(c_4582,plain,(
    ! [B_263,C_264] :
      ( k2_xboole_0(B_263,C_264) = B_263
      | ~ r1_tarski(C_264,B_263) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4566])).

tff(c_4741,plain,(
    k2_xboole_0(k2_relat_1('#skF_4'),'#skF_2') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_4582])).

tff(c_36,plain,(
    ! [A_46] :
      ( k9_relat_1(A_46,k1_relat_1(A_46)) = k2_relat_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1484,plain,(
    ! [C_142,A_143,B_144] :
      ( r1_tarski(k9_relat_1(C_142,A_143),k9_relat_1(C_142,B_144))
      | ~ r1_tarski(A_143,B_144)
      | ~ v1_relat_1(C_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_11005,plain,(
    ! [A_349,B_350] :
      ( r1_tarski(k2_relat_1(A_349),k9_relat_1(A_349,B_350))
      | ~ r1_tarski(k1_relat_1(A_349),B_350)
      | ~ v1_relat_1(A_349)
      | ~ v1_relat_1(A_349) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1484])).

tff(c_64,plain,(
    ! [A_57,B_58] :
      ( k2_xboole_0(A_57,B_58) = B_58
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_75,plain,(
    k2_xboole_0('#skF_2',k2_relat_1('#skF_4')) = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_64])).

tff(c_170,plain,(
    ! [A_71,C_72,B_73] :
      ( r1_tarski(A_71,C_72)
      | ~ r1_tarski(k2_xboole_0(A_71,B_73),C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_177,plain,(
    ! [C_72] :
      ( r1_tarski('#skF_2',C_72)
      | ~ r1_tarski(k2_relat_1('#skF_4'),C_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_170])).

tff(c_11022,plain,(
    ! [B_350] :
      ( r1_tarski('#skF_2',k9_relat_1('#skF_4',B_350))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_350)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_11005,c_177])).

tff(c_11052,plain,(
    ! [B_351] :
      ( r1_tarski('#skF_2',k9_relat_1('#skF_4',B_351))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_351) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_11022])).

tff(c_11182,plain,(
    r1_tarski('#skF_2',k9_relat_1('#skF_4',k1_relat_1('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_6,c_11052])).

tff(c_4577,plain,(
    ! [B_12,C_13] :
      ( k2_xboole_0(B_12,C_13) = B_12
      | ~ r1_tarski(C_13,B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4566])).

tff(c_11197,plain,(
    k2_xboole_0(k9_relat_1('#skF_4',k1_relat_1('#skF_4')),'#skF_2') = k9_relat_1('#skF_4',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_11182,c_4577])).

tff(c_13970,plain,
    ( k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_xboole_0(k2_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_11197])).

tff(c_14000,plain,(
    k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4741,c_13970])).

tff(c_42,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,k9_relat_1(B_53,k1_relat_1(B_53))) = k9_relat_1(B_53,k10_relat_1(B_53,A_52))
      | ~ v1_funct_1(B_53)
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_14028,plain,(
    ! [A_52] :
      ( k9_relat_1('#skF_4',k10_relat_1('#skF_4',A_52)) = k3_xboole_0(A_52,k2_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14000,c_42])).

tff(c_14056,plain,(
    ! [A_52] : k9_relat_1('#skF_4',k10_relat_1('#skF_4',A_52)) = k3_xboole_0(A_52,k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_14028])).

tff(c_48,plain,(
    r1_tarski(k10_relat_1('#skF_4','#skF_2'),k10_relat_1('#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( k3_xboole_0(A_15,B_16) = A_15
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_11199,plain,(
    k3_xboole_0('#skF_2',k9_relat_1('#skF_4',k1_relat_1('#skF_4'))) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_11182,c_20])).

tff(c_11206,plain,
    ( k9_relat_1('#skF_4',k10_relat_1('#skF_4','#skF_2')) = '#skF_2'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_11199,c_42])).

tff(c_11216,plain,(
    k9_relat_1('#skF_4',k10_relat_1('#skF_4','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_11206])).

tff(c_38,plain,(
    ! [C_49,A_47,B_48] :
      ( r1_tarski(k9_relat_1(C_49,A_47),k9_relat_1(C_49,B_48))
      | ~ r1_tarski(A_47,B_48)
      | ~ v1_relat_1(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_11234,plain,(
    ! [B_48] :
      ( r1_tarski('#skF_2',k9_relat_1('#skF_4',B_48))
      | ~ r1_tarski(k10_relat_1('#skF_4','#skF_2'),B_48)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11216,c_38])).

tff(c_20066,plain,(
    ! [B_470] :
      ( r1_tarski('#skF_2',k9_relat_1('#skF_4',B_470))
      | ~ r1_tarski(k10_relat_1('#skF_4','#skF_2'),B_470) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_11234])).

tff(c_20212,plain,(
    r1_tarski('#skF_2',k9_relat_1('#skF_4',k10_relat_1('#skF_4','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_48,c_20066])).

tff(c_20260,plain,(
    r1_tarski('#skF_2',k3_xboole_0('#skF_3',k2_relat_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14056,c_20212])).

tff(c_14207,plain,(
    ! [A_397] : k9_relat_1('#skF_4',k10_relat_1('#skF_4',A_397)) = k3_xboole_0(A_397,k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_14028])).

tff(c_606,plain,(
    ! [B_103,A_104] :
      ( r1_tarski(k9_relat_1(B_103,k10_relat_1(B_103,A_104)),A_104)
      | ~ v1_funct_1(B_103)
      | ~ v1_relat_1(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_617,plain,(
    ! [B_103,A_104] :
      ( k2_xboole_0(k9_relat_1(B_103,k10_relat_1(B_103,A_104)),A_104) = A_104
      | ~ v1_funct_1(B_103)
      | ~ v1_relat_1(B_103) ) ),
    inference(resolution,[status(thm)],[c_606,c_12])).

tff(c_14240,plain,(
    ! [A_397] :
      ( k2_xboole_0(k3_xboole_0(A_397,k2_relat_1('#skF_4')),A_397) = A_397
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14207,c_617])).

tff(c_14462,plain,(
    ! [A_401] : k2_xboole_0(k3_xboole_0(A_401,k2_relat_1('#skF_4')),A_401) = A_401 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_14240])).

tff(c_186,plain,(
    ! [A_71,B_73] : r1_tarski(A_71,k2_xboole_0(A_71,B_73)) ),
    inference(resolution,[status(thm)],[c_6,c_170])).

tff(c_5123,plain,(
    ! [A_266,B_267] : k2_xboole_0(k2_xboole_0(A_266,B_267),A_266) = k2_xboole_0(A_266,B_267) ),
    inference(resolution,[status(thm)],[c_186,c_4582])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5482,plain,(
    ! [A_3,A_266,B_267] :
      ( r1_tarski(A_3,k2_xboole_0(A_266,B_267))
      | ~ r1_tarski(A_3,A_266) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5123,c_8])).

tff(c_14594,plain,(
    ! [A_3,A_401] :
      ( r1_tarski(A_3,A_401)
      | ~ r1_tarski(A_3,k3_xboole_0(A_401,k2_relat_1('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14462,c_5482])).

tff(c_20267,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_20260,c_14594])).

tff(c_20288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_20267])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:19:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.48/3.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.48/3.70  
% 9.48/3.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.48/3.70  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 9.48/3.70  
% 9.48/3.70  %Foreground sorts:
% 9.48/3.70  
% 9.48/3.70  
% 9.48/3.70  %Background operators:
% 9.48/3.70  
% 9.48/3.70  
% 9.48/3.70  %Foreground operators:
% 9.48/3.70  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.48/3.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.48/3.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.48/3.70  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.48/3.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.48/3.70  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.48/3.70  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.48/3.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.48/3.70  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.48/3.70  tff('#skF_2', type, '#skF_2': $i).
% 9.48/3.70  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.48/3.70  tff('#skF_3', type, '#skF_3': $i).
% 9.48/3.70  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.48/3.70  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.48/3.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.48/3.70  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 9.48/3.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.48/3.70  tff('#skF_4', type, '#skF_4': $i).
% 9.48/3.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.48/3.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.48/3.70  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.48/3.70  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.48/3.70  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.48/3.70  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.48/3.70  
% 9.69/3.72  tff(f_107, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 9.69/3.72  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.69/3.72  tff(f_56, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(C, B)) & (![D]: ((r1_tarski(A, D) & r1_tarski(C, D)) => r1_tarski(B, D)))) => (B = k2_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_xboole_1)).
% 9.69/3.72  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 9.69/3.72  tff(f_84, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 9.69/3.72  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 9.69/3.72  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 9.69/3.72  tff(f_96, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_1)).
% 9.69/3.72  tff(f_60, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.69/3.72  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 9.69/3.72  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 9.69/3.72  tff(c_44, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 9.69/3.72  tff(c_52, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 9.69/3.72  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 9.69/3.72  tff(c_46, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 9.69/3.72  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.69/3.72  tff(c_18, plain, (![A_11, B_12, C_13]: (r1_tarski(A_11, '#skF_1'(A_11, B_12, C_13)) | k2_xboole_0(A_11, C_13)=B_12 | ~r1_tarski(C_13, B_12) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.69/3.72  tff(c_4562, plain, (![B_260, A_261, C_262]: (~r1_tarski(B_260, '#skF_1'(A_261, B_260, C_262)) | k2_xboole_0(A_261, C_262)=B_260 | ~r1_tarski(C_262, B_260) | ~r1_tarski(A_261, B_260))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.69/3.72  tff(c_4566, plain, (![B_12, C_13]: (k2_xboole_0(B_12, C_13)=B_12 | ~r1_tarski(C_13, B_12) | ~r1_tarski(B_12, B_12))), inference(resolution, [status(thm)], [c_18, c_4562])).
% 9.69/3.72  tff(c_4582, plain, (![B_263, C_264]: (k2_xboole_0(B_263, C_264)=B_263 | ~r1_tarski(C_264, B_263))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4566])).
% 9.69/3.72  tff(c_4741, plain, (k2_xboole_0(k2_relat_1('#skF_4'), '#skF_2')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_4582])).
% 9.69/3.72  tff(c_36, plain, (![A_46]: (k9_relat_1(A_46, k1_relat_1(A_46))=k2_relat_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.69/3.72  tff(c_1484, plain, (![C_142, A_143, B_144]: (r1_tarski(k9_relat_1(C_142, A_143), k9_relat_1(C_142, B_144)) | ~r1_tarski(A_143, B_144) | ~v1_relat_1(C_142))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.69/3.72  tff(c_11005, plain, (![A_349, B_350]: (r1_tarski(k2_relat_1(A_349), k9_relat_1(A_349, B_350)) | ~r1_tarski(k1_relat_1(A_349), B_350) | ~v1_relat_1(A_349) | ~v1_relat_1(A_349))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1484])).
% 9.69/3.72  tff(c_64, plain, (![A_57, B_58]: (k2_xboole_0(A_57, B_58)=B_58 | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.69/3.72  tff(c_75, plain, (k2_xboole_0('#skF_2', k2_relat_1('#skF_4'))=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_64])).
% 9.69/3.72  tff(c_170, plain, (![A_71, C_72, B_73]: (r1_tarski(A_71, C_72) | ~r1_tarski(k2_xboole_0(A_71, B_73), C_72))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.69/3.72  tff(c_177, plain, (![C_72]: (r1_tarski('#skF_2', C_72) | ~r1_tarski(k2_relat_1('#skF_4'), C_72))), inference(superposition, [status(thm), theory('equality')], [c_75, c_170])).
% 9.69/3.72  tff(c_11022, plain, (![B_350]: (r1_tarski('#skF_2', k9_relat_1('#skF_4', B_350)) | ~r1_tarski(k1_relat_1('#skF_4'), B_350) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_11005, c_177])).
% 9.69/3.72  tff(c_11052, plain, (![B_351]: (r1_tarski('#skF_2', k9_relat_1('#skF_4', B_351)) | ~r1_tarski(k1_relat_1('#skF_4'), B_351))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_11022])).
% 9.69/3.72  tff(c_11182, plain, (r1_tarski('#skF_2', k9_relat_1('#skF_4', k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_6, c_11052])).
% 9.69/3.72  tff(c_4577, plain, (![B_12, C_13]: (k2_xboole_0(B_12, C_13)=B_12 | ~r1_tarski(C_13, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4566])).
% 9.69/3.72  tff(c_11197, plain, (k2_xboole_0(k9_relat_1('#skF_4', k1_relat_1('#skF_4')), '#skF_2')=k9_relat_1('#skF_4', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_11182, c_4577])).
% 9.69/3.72  tff(c_13970, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_xboole_0(k2_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_36, c_11197])).
% 9.69/3.72  tff(c_14000, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_4741, c_13970])).
% 9.69/3.72  tff(c_42, plain, (![A_52, B_53]: (k3_xboole_0(A_52, k9_relat_1(B_53, k1_relat_1(B_53)))=k9_relat_1(B_53, k10_relat_1(B_53, A_52)) | ~v1_funct_1(B_53) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.69/3.72  tff(c_14028, plain, (![A_52]: (k9_relat_1('#skF_4', k10_relat_1('#skF_4', A_52))=k3_xboole_0(A_52, k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_14000, c_42])).
% 9.69/3.72  tff(c_14056, plain, (![A_52]: (k9_relat_1('#skF_4', k10_relat_1('#skF_4', A_52))=k3_xboole_0(A_52, k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_14028])).
% 9.69/3.72  tff(c_48, plain, (r1_tarski(k10_relat_1('#skF_4', '#skF_2'), k10_relat_1('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 9.69/3.72  tff(c_20, plain, (![A_15, B_16]: (k3_xboole_0(A_15, B_16)=A_15 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.69/3.72  tff(c_11199, plain, (k3_xboole_0('#skF_2', k9_relat_1('#skF_4', k1_relat_1('#skF_4')))='#skF_2'), inference(resolution, [status(thm)], [c_11182, c_20])).
% 9.69/3.72  tff(c_11206, plain, (k9_relat_1('#skF_4', k10_relat_1('#skF_4', '#skF_2'))='#skF_2' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_11199, c_42])).
% 9.69/3.72  tff(c_11216, plain, (k9_relat_1('#skF_4', k10_relat_1('#skF_4', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_11206])).
% 9.69/3.72  tff(c_38, plain, (![C_49, A_47, B_48]: (r1_tarski(k9_relat_1(C_49, A_47), k9_relat_1(C_49, B_48)) | ~r1_tarski(A_47, B_48) | ~v1_relat_1(C_49))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.69/3.72  tff(c_11234, plain, (![B_48]: (r1_tarski('#skF_2', k9_relat_1('#skF_4', B_48)) | ~r1_tarski(k10_relat_1('#skF_4', '#skF_2'), B_48) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_11216, c_38])).
% 9.69/3.72  tff(c_20066, plain, (![B_470]: (r1_tarski('#skF_2', k9_relat_1('#skF_4', B_470)) | ~r1_tarski(k10_relat_1('#skF_4', '#skF_2'), B_470))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_11234])).
% 9.69/3.72  tff(c_20212, plain, (r1_tarski('#skF_2', k9_relat_1('#skF_4', k10_relat_1('#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_48, c_20066])).
% 9.69/3.72  tff(c_20260, plain, (r1_tarski('#skF_2', k3_xboole_0('#skF_3', k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_14056, c_20212])).
% 9.69/3.72  tff(c_14207, plain, (![A_397]: (k9_relat_1('#skF_4', k10_relat_1('#skF_4', A_397))=k3_xboole_0(A_397, k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_14028])).
% 9.69/3.72  tff(c_606, plain, (![B_103, A_104]: (r1_tarski(k9_relat_1(B_103, k10_relat_1(B_103, A_104)), A_104) | ~v1_funct_1(B_103) | ~v1_relat_1(B_103))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.69/3.72  tff(c_12, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.69/3.72  tff(c_617, plain, (![B_103, A_104]: (k2_xboole_0(k9_relat_1(B_103, k10_relat_1(B_103, A_104)), A_104)=A_104 | ~v1_funct_1(B_103) | ~v1_relat_1(B_103))), inference(resolution, [status(thm)], [c_606, c_12])).
% 9.69/3.72  tff(c_14240, plain, (![A_397]: (k2_xboole_0(k3_xboole_0(A_397, k2_relat_1('#skF_4')), A_397)=A_397 | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_14207, c_617])).
% 9.69/3.72  tff(c_14462, plain, (![A_401]: (k2_xboole_0(k3_xboole_0(A_401, k2_relat_1('#skF_4')), A_401)=A_401)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_14240])).
% 9.69/3.72  tff(c_186, plain, (![A_71, B_73]: (r1_tarski(A_71, k2_xboole_0(A_71, B_73)))), inference(resolution, [status(thm)], [c_6, c_170])).
% 9.69/3.72  tff(c_5123, plain, (![A_266, B_267]: (k2_xboole_0(k2_xboole_0(A_266, B_267), A_266)=k2_xboole_0(A_266, B_267))), inference(resolution, [status(thm)], [c_186, c_4582])).
% 9.69/3.72  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.69/3.72  tff(c_5482, plain, (![A_3, A_266, B_267]: (r1_tarski(A_3, k2_xboole_0(A_266, B_267)) | ~r1_tarski(A_3, A_266))), inference(superposition, [status(thm), theory('equality')], [c_5123, c_8])).
% 9.69/3.72  tff(c_14594, plain, (![A_3, A_401]: (r1_tarski(A_3, A_401) | ~r1_tarski(A_3, k3_xboole_0(A_401, k2_relat_1('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_14462, c_5482])).
% 9.69/3.72  tff(c_20267, plain, (r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_20260, c_14594])).
% 9.69/3.72  tff(c_20288, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_20267])).
% 9.69/3.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.69/3.72  
% 9.69/3.72  Inference rules
% 9.69/3.72  ----------------------
% 9.69/3.72  #Ref     : 0
% 9.69/3.72  #Sup     : 4835
% 9.69/3.72  #Fact    : 0
% 9.69/3.72  #Define  : 0
% 9.69/3.72  #Split   : 4
% 9.69/3.72  #Chain   : 0
% 9.69/3.72  #Close   : 0
% 9.69/3.72  
% 9.69/3.72  Ordering : KBO
% 9.69/3.72  
% 9.69/3.72  Simplification rules
% 9.69/3.72  ----------------------
% 9.69/3.72  #Subsume      : 624
% 9.69/3.72  #Demod        : 2301
% 9.69/3.72  #Tautology    : 2463
% 9.69/3.72  #SimpNegUnit  : 5
% 9.69/3.72  #BackRed      : 3
% 9.69/3.72  
% 9.69/3.72  #Partial instantiations: 0
% 9.69/3.72  #Strategies tried      : 1
% 9.69/3.72  
% 9.69/3.72  Timing (in seconds)
% 9.69/3.72  ----------------------
% 9.69/3.72  Preprocessing        : 0.36
% 9.69/3.72  Parsing              : 0.20
% 9.69/3.72  CNF conversion       : 0.02
% 9.69/3.72  Main loop            : 2.59
% 9.69/3.72  Inferencing          : 0.60
% 9.69/3.72  Reduction            : 1.11
% 9.69/3.72  Demodulation         : 0.92
% 9.69/3.72  BG Simplification    : 0.07
% 9.69/3.72  Subsumption          : 0.66
% 9.69/3.72  Abstraction          : 0.10
% 9.69/3.72  MUC search           : 0.00
% 9.69/3.72  Cooper               : 0.00
% 9.69/3.72  Total                : 2.98
% 9.69/3.72  Index Insertion      : 0.00
% 9.69/3.72  Index Deletion       : 0.00
% 9.69/3.72  Index Matching       : 0.00
% 9.69/3.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
