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
% DateTime   : Thu Dec  3 09:58:57 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 106 expanded)
%              Number of leaves         :   39 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :   71 ( 118 expanded)
%              Number of equality atoms :   32 (  64 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_1 > #skF_3 > #skF_8 > #skF_7 > #skF_9 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_93,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k1_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_50,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_78,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_4,plain,(
    ! [A_3] :
      ( r2_hidden('#skF_1'(A_3),A_3)
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34,plain,(
    ! [A_25] :
      ( r2_hidden('#skF_2'(A_25),A_25)
      | v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_10,plain,(
    ! [A_8] : k5_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_124,plain,(
    ! [A_84,B_85] : k5_xboole_0(A_84,k3_xboole_0(A_84,B_85)) = k4_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_133,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_124])).

tff(c_136,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_133])).

tff(c_24,plain,(
    ! [B_22] : k4_xboole_0(k1_tarski(B_22),k1_tarski(B_22)) != k1_tarski(B_22) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_137,plain,(
    ! [B_22] : k1_tarski(B_22) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_24])).

tff(c_114,plain,(
    ! [A_82,B_83] :
      ( r1_tarski(k1_tarski(A_82),B_83)
      | ~ r2_hidden(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_123,plain,(
    ! [A_82] :
      ( k1_tarski(A_82) = k1_xboole_0
      | ~ r2_hidden(A_82,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_114,c_8])).

tff(c_147,plain,(
    ! [A_88] : ~ r2_hidden(A_88,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_123])).

tff(c_158,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_34,c_147])).

tff(c_48,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_9'(A_62,B_63),k2_relat_1(B_63))
      | ~ r2_hidden(A_62,k1_relat_1(B_63))
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_207,plain,(
    ! [A_105,C_106] :
      ( r2_hidden(k4_tarski('#skF_8'(A_105,k2_relat_1(A_105),C_106),C_106),A_105)
      | ~ r2_hidden(C_106,k2_relat_1(A_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_146,plain,(
    ! [A_82] : ~ r2_hidden(A_82,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_123])).

tff(c_217,plain,(
    ! [C_107] : ~ r2_hidden(C_107,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_207,c_146])).

tff(c_229,plain,(
    ! [A_62] :
      ( ~ r2_hidden(A_62,k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_48,c_217])).

tff(c_275,plain,(
    ! [A_110] : ~ r2_hidden(A_110,k1_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_229])).

tff(c_287,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_275])).

tff(c_297,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_287])).

tff(c_298,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_469,plain,(
    ! [A_154,C_155] :
      ( r2_hidden(k4_tarski('#skF_8'(A_154,k2_relat_1(A_154),C_155),C_155),A_154)
      | ~ r2_hidden(C_155,k2_relat_1(A_154)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_362,plain,(
    ! [A_126,B_127] : k5_xboole_0(A_126,k3_xboole_0(A_126,B_127)) = k4_xboole_0(A_126,B_127) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_371,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_362])).

tff(c_374,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_371])).

tff(c_375,plain,(
    ! [B_22] : k1_tarski(B_22) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_24])).

tff(c_338,plain,(
    ! [A_122,B_123] :
      ( r1_tarski(k1_tarski(A_122),B_123)
      | ~ r2_hidden(A_122,B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_347,plain,(
    ! [A_122] :
      ( k1_tarski(A_122) = k1_xboole_0
      | ~ r2_hidden(A_122,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_338,c_8])).

tff(c_383,plain,(
    ! [A_122] : ~ r2_hidden(A_122,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_375,c_347])).

tff(c_480,plain,(
    ! [C_159] : ~ r2_hidden(C_159,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_469,c_383])).

tff(c_496,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_480])).

tff(c_509,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_298,c_496])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:19:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.31  
% 2.36/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.32  %$ r2_hidden > r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_1 > #skF_3 > #skF_8 > #skF_7 > #skF_9 > #skF_5 > #skF_4
% 2.36/1.32  
% 2.36/1.32  %Foreground sorts:
% 2.36/1.32  
% 2.36/1.32  
% 2.36/1.32  %Background operators:
% 2.36/1.32  
% 2.36/1.32  
% 2.36/1.32  %Foreground operators:
% 2.36/1.32  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.36/1.32  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.36/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.36/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.36/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.36/1.32  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.36/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.36/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.36/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.36/1.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.36/1.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.36/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.36/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.36/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.36/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.36/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.36/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.36/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.36/1.32  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 2.36/1.32  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.36/1.32  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 2.36/1.32  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.36/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.36/1.32  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.36/1.32  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.36/1.32  
% 2.36/1.33  tff(f_93, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.36/1.33  tff(f_35, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.36/1.33  tff(f_72, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.36/1.33  tff(f_43, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.36/1.33  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.36/1.33  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.36/1.33  tff(f_60, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.36/1.33  tff(f_55, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.36/1.33  tff(f_41, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.36/1.33  tff(f_89, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k1_relat_1(B)) & (![C]: ~r2_hidden(C, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_relat_1)).
% 2.36/1.33  tff(f_80, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 2.36/1.33  tff(c_50, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.36/1.33  tff(c_78, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_50])).
% 2.36/1.33  tff(c_4, plain, (![A_3]: (r2_hidden('#skF_1'(A_3), A_3) | k1_xboole_0=A_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.36/1.33  tff(c_34, plain, (![A_25]: (r2_hidden('#skF_2'(A_25), A_25) | v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.36/1.33  tff(c_10, plain, (![A_8]: (k5_xboole_0(A_8, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.36/1.33  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.36/1.33  tff(c_124, plain, (![A_84, B_85]: (k5_xboole_0(A_84, k3_xboole_0(A_84, B_85))=k4_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.36/1.33  tff(c_133, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_124])).
% 2.36/1.33  tff(c_136, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_133])).
% 2.36/1.33  tff(c_24, plain, (![B_22]: (k4_xboole_0(k1_tarski(B_22), k1_tarski(B_22))!=k1_tarski(B_22))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.36/1.33  tff(c_137, plain, (![B_22]: (k1_tarski(B_22)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_136, c_24])).
% 2.36/1.33  tff(c_114, plain, (![A_82, B_83]: (r1_tarski(k1_tarski(A_82), B_83) | ~r2_hidden(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.36/1.33  tff(c_8, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.36/1.33  tff(c_123, plain, (![A_82]: (k1_tarski(A_82)=k1_xboole_0 | ~r2_hidden(A_82, k1_xboole_0))), inference(resolution, [status(thm)], [c_114, c_8])).
% 2.36/1.33  tff(c_147, plain, (![A_88]: (~r2_hidden(A_88, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_137, c_123])).
% 2.36/1.33  tff(c_158, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_147])).
% 2.36/1.33  tff(c_48, plain, (![A_62, B_63]: (r2_hidden('#skF_9'(A_62, B_63), k2_relat_1(B_63)) | ~r2_hidden(A_62, k1_relat_1(B_63)) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.36/1.33  tff(c_207, plain, (![A_105, C_106]: (r2_hidden(k4_tarski('#skF_8'(A_105, k2_relat_1(A_105), C_106), C_106), A_105) | ~r2_hidden(C_106, k2_relat_1(A_105)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.36/1.33  tff(c_146, plain, (![A_82]: (~r2_hidden(A_82, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_137, c_123])).
% 2.36/1.33  tff(c_217, plain, (![C_107]: (~r2_hidden(C_107, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_207, c_146])).
% 2.36/1.33  tff(c_229, plain, (![A_62]: (~r2_hidden(A_62, k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_48, c_217])).
% 2.36/1.33  tff(c_275, plain, (![A_110]: (~r2_hidden(A_110, k1_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_229])).
% 2.36/1.33  tff(c_287, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_275])).
% 2.36/1.33  tff(c_297, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_287])).
% 2.36/1.33  tff(c_298, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 2.36/1.33  tff(c_469, plain, (![A_154, C_155]: (r2_hidden(k4_tarski('#skF_8'(A_154, k2_relat_1(A_154), C_155), C_155), A_154) | ~r2_hidden(C_155, k2_relat_1(A_154)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.36/1.33  tff(c_362, plain, (![A_126, B_127]: (k5_xboole_0(A_126, k3_xboole_0(A_126, B_127))=k4_xboole_0(A_126, B_127))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.36/1.33  tff(c_371, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_362])).
% 2.36/1.33  tff(c_374, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_371])).
% 2.36/1.33  tff(c_375, plain, (![B_22]: (k1_tarski(B_22)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_374, c_24])).
% 2.36/1.33  tff(c_338, plain, (![A_122, B_123]: (r1_tarski(k1_tarski(A_122), B_123) | ~r2_hidden(A_122, B_123))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.36/1.33  tff(c_347, plain, (![A_122]: (k1_tarski(A_122)=k1_xboole_0 | ~r2_hidden(A_122, k1_xboole_0))), inference(resolution, [status(thm)], [c_338, c_8])).
% 2.36/1.33  tff(c_383, plain, (![A_122]: (~r2_hidden(A_122, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_375, c_347])).
% 2.36/1.33  tff(c_480, plain, (![C_159]: (~r2_hidden(C_159, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_469, c_383])).
% 2.36/1.33  tff(c_496, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_480])).
% 2.36/1.33  tff(c_509, plain, $false, inference(negUnitSimplification, [status(thm)], [c_298, c_496])).
% 2.36/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.33  
% 2.36/1.33  Inference rules
% 2.36/1.33  ----------------------
% 2.36/1.33  #Ref     : 1
% 2.36/1.33  #Sup     : 91
% 2.36/1.33  #Fact    : 0
% 2.36/1.33  #Define  : 0
% 2.36/1.33  #Split   : 2
% 2.36/1.33  #Chain   : 0
% 2.36/1.33  #Close   : 0
% 2.36/1.33  
% 2.36/1.33  Ordering : KBO
% 2.36/1.33  
% 2.36/1.33  Simplification rules
% 2.36/1.33  ----------------------
% 2.36/1.33  #Subsume      : 8
% 2.36/1.33  #Demod        : 15
% 2.36/1.33  #Tautology    : 60
% 2.36/1.33  #SimpNegUnit  : 10
% 2.36/1.33  #BackRed      : 4
% 2.36/1.33  
% 2.36/1.33  #Partial instantiations: 0
% 2.36/1.33  #Strategies tried      : 1
% 2.36/1.33  
% 2.36/1.33  Timing (in seconds)
% 2.36/1.33  ----------------------
% 2.36/1.33  Preprocessing        : 0.32
% 2.36/1.33  Parsing              : 0.17
% 2.36/1.33  CNF conversion       : 0.02
% 2.36/1.33  Main loop            : 0.23
% 2.36/1.33  Inferencing          : 0.10
% 2.36/1.33  Reduction            : 0.06
% 2.36/1.33  Demodulation         : 0.04
% 2.36/1.33  BG Simplification    : 0.02
% 2.36/1.33  Subsumption          : 0.03
% 2.36/1.33  Abstraction          : 0.01
% 2.36/1.33  MUC search           : 0.00
% 2.36/1.33  Cooper               : 0.00
% 2.36/1.33  Total                : 0.58
% 2.36/1.33  Index Insertion      : 0.00
% 2.36/1.33  Index Deletion       : 0.00
% 2.36/1.33  Index Matching       : 0.00
% 2.36/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
