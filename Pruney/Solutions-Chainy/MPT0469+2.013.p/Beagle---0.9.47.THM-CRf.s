%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:53 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 138 expanded)
%              Number of leaves         :   40 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :   84 ( 168 expanded)
%              Number of equality atoms :   33 (  75 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_87,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_42,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k6_subset_1(A,B)) = k6_subset_1(k4_relat_1(A),k4_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_52,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_96,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_76,plain,(
    ! [A_69] :
      ( v1_relat_1(A_69)
      | ~ v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_80,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_76])).

tff(c_14,plain,(
    ! [A_10] : k5_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_133,plain,(
    ! [A_81,B_82] : k5_xboole_0(A_81,k3_xboole_0(A_81,B_82)) = k4_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_142,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_133])).

tff(c_145,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_142])).

tff(c_28,plain,(
    ! [A_38,B_39] : k6_subset_1(A_38,B_39) = k4_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_50,plain,(
    ! [A_63,B_65] :
      ( k6_subset_1(k4_relat_1(A_63),k4_relat_1(B_65)) = k4_relat_1(k6_subset_1(A_63,B_65))
      | ~ v1_relat_1(B_65)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_172,plain,(
    ! [A_94,B_95] :
      ( k4_xboole_0(k4_relat_1(A_94),k4_relat_1(B_95)) = k4_relat_1(k4_xboole_0(A_94,B_95))
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1(A_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_50])).

tff(c_179,plain,(
    ! [B_95] :
      ( k4_relat_1(k4_xboole_0(B_95,B_95)) = k1_xboole_0
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1(B_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_145])).

tff(c_188,plain,(
    ! [B_95] :
      ( k4_relat_1(k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1(B_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_179])).

tff(c_192,plain,(
    ! [B_96] :
      ( ~ v1_relat_1(B_96)
      | ~ v1_relat_1(B_96) ) ),
    inference(splitLeft,[status(thm)],[c_188])).

tff(c_194,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_80,c_192])).

tff(c_198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_194])).

tff(c_199,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_48,plain,(
    ! [A_62] :
      ( k1_relat_1(k4_relat_1(A_62)) = k2_relat_1(A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_209,plain,
    ( k2_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_48])).

tff(c_220,plain,(
    k2_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_209])).

tff(c_253,plain,(
    ! [A_103,C_104] :
      ( r2_hidden(k4_tarski('#skF_5'(A_103,k2_relat_1(A_103),C_104),C_104),A_103)
      | ~ r2_hidden(C_104,k2_relat_1(A_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_269,plain,(
    ! [A_105,C_106] :
      ( ~ v1_xboole_0(A_105)
      | ~ r2_hidden(C_106,k2_relat_1(A_105)) ) ),
    inference(resolution,[status(thm)],[c_253,c_2])).

tff(c_276,plain,(
    ! [C_106] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_106,k1_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_269])).

tff(c_288,plain,(
    ! [C_107] : ~ r2_hidden(C_107,k1_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_276])).

tff(c_298,plain,(
    v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_4,c_288])).

tff(c_10,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_304,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_298,c_10])).

tff(c_309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_304])).

tff(c_310,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_401,plain,(
    ! [A_134,C_135] :
      ( r2_hidden(k4_tarski('#skF_5'(A_134,k2_relat_1(A_134),C_135),C_135),A_134)
      | ~ r2_hidden(C_135,k2_relat_1(A_134)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_413,plain,(
    ! [A_136,C_137] :
      ( ~ v1_xboole_0(A_136)
      | ~ r2_hidden(C_137,k2_relat_1(A_136)) ) ),
    inference(resolution,[status(thm)],[c_401,c_2])).

tff(c_427,plain,(
    ! [A_138] :
      ( ~ v1_xboole_0(A_138)
      | v1_xboole_0(k2_relat_1(A_138)) ) ),
    inference(resolution,[status(thm)],[c_4,c_413])).

tff(c_444,plain,(
    ! [A_143] :
      ( k2_relat_1(A_143) = k1_xboole_0
      | ~ v1_xboole_0(A_143) ) ),
    inference(resolution,[status(thm)],[c_427,c_10])).

tff(c_450,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_444])).

tff(c_455,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_310,c_450])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:11:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.45  
% 2.33/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.45  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 2.33/1.45  
% 2.33/1.45  %Foreground sorts:
% 2.33/1.45  
% 2.33/1.45  
% 2.33/1.45  %Background operators:
% 2.33/1.45  
% 2.33/1.45  
% 2.33/1.45  %Foreground operators:
% 2.33/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.33/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.33/1.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.33/1.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.33/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.33/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.33/1.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.33/1.45  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.33/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.33/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.33/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.33/1.45  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.33/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.33/1.45  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.33/1.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.33/1.45  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.33/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.33/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.33/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.33/1.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.33/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.33/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.33/1.45  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.33/1.45  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.33/1.45  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.33/1.45  
% 2.48/1.46  tff(f_87, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.48/1.46  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.48/1.46  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.48/1.46  tff(f_62, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.48/1.46  tff(f_42, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.48/1.46  tff(f_34, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.48/1.46  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.48/1.46  tff(f_56, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.48/1.46  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k6_subset_1(A, B)) = k6_subset_1(k4_relat_1(A), k4_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_relat_1)).
% 2.48/1.46  tff(f_76, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 2.48/1.46  tff(f_70, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 2.48/1.46  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.48/1.46  tff(c_52, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.48/1.46  tff(c_96, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_52])).
% 2.48/1.46  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.48/1.46  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.48/1.46  tff(c_76, plain, (![A_69]: (v1_relat_1(A_69) | ~v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.48/1.46  tff(c_80, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_76])).
% 2.48/1.46  tff(c_14, plain, (![A_10]: (k5_xboole_0(A_10, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.48/1.46  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.48/1.46  tff(c_133, plain, (![A_81, B_82]: (k5_xboole_0(A_81, k3_xboole_0(A_81, B_82))=k4_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.48/1.46  tff(c_142, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_133])).
% 2.48/1.46  tff(c_145, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_142])).
% 2.48/1.46  tff(c_28, plain, (![A_38, B_39]: (k6_subset_1(A_38, B_39)=k4_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.48/1.46  tff(c_50, plain, (![A_63, B_65]: (k6_subset_1(k4_relat_1(A_63), k4_relat_1(B_65))=k4_relat_1(k6_subset_1(A_63, B_65)) | ~v1_relat_1(B_65) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.48/1.46  tff(c_172, plain, (![A_94, B_95]: (k4_xboole_0(k4_relat_1(A_94), k4_relat_1(B_95))=k4_relat_1(k4_xboole_0(A_94, B_95)) | ~v1_relat_1(B_95) | ~v1_relat_1(A_94))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_50])).
% 2.48/1.46  tff(c_179, plain, (![B_95]: (k4_relat_1(k4_xboole_0(B_95, B_95))=k1_xboole_0 | ~v1_relat_1(B_95) | ~v1_relat_1(B_95))), inference(superposition, [status(thm), theory('equality')], [c_172, c_145])).
% 2.48/1.46  tff(c_188, plain, (![B_95]: (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_95) | ~v1_relat_1(B_95))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_179])).
% 2.48/1.46  tff(c_192, plain, (![B_96]: (~v1_relat_1(B_96) | ~v1_relat_1(B_96))), inference(splitLeft, [status(thm)], [c_188])).
% 2.48/1.46  tff(c_194, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_80, c_192])).
% 2.48/1.46  tff(c_198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_194])).
% 2.48/1.46  tff(c_199, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_188])).
% 2.48/1.46  tff(c_48, plain, (![A_62]: (k1_relat_1(k4_relat_1(A_62))=k2_relat_1(A_62) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.48/1.46  tff(c_209, plain, (k2_relat_1(k1_xboole_0)=k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_199, c_48])).
% 2.48/1.46  tff(c_220, plain, (k2_relat_1(k1_xboole_0)=k1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_209])).
% 2.48/1.46  tff(c_253, plain, (![A_103, C_104]: (r2_hidden(k4_tarski('#skF_5'(A_103, k2_relat_1(A_103), C_104), C_104), A_103) | ~r2_hidden(C_104, k2_relat_1(A_103)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.48/1.46  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.48/1.46  tff(c_269, plain, (![A_105, C_106]: (~v1_xboole_0(A_105) | ~r2_hidden(C_106, k2_relat_1(A_105)))), inference(resolution, [status(thm)], [c_253, c_2])).
% 2.48/1.46  tff(c_276, plain, (![C_106]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(C_106, k1_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_220, c_269])).
% 2.48/1.46  tff(c_288, plain, (![C_107]: (~r2_hidden(C_107, k1_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_276])).
% 2.48/1.46  tff(c_298, plain, (v1_xboole_0(k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_288])).
% 2.48/1.46  tff(c_10, plain, (![A_7]: (k1_xboole_0=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.48/1.46  tff(c_304, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_298, c_10])).
% 2.48/1.46  tff(c_309, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_304])).
% 2.48/1.46  tff(c_310, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 2.48/1.46  tff(c_401, plain, (![A_134, C_135]: (r2_hidden(k4_tarski('#skF_5'(A_134, k2_relat_1(A_134), C_135), C_135), A_134) | ~r2_hidden(C_135, k2_relat_1(A_134)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.48/1.46  tff(c_413, plain, (![A_136, C_137]: (~v1_xboole_0(A_136) | ~r2_hidden(C_137, k2_relat_1(A_136)))), inference(resolution, [status(thm)], [c_401, c_2])).
% 2.48/1.46  tff(c_427, plain, (![A_138]: (~v1_xboole_0(A_138) | v1_xboole_0(k2_relat_1(A_138)))), inference(resolution, [status(thm)], [c_4, c_413])).
% 2.48/1.46  tff(c_444, plain, (![A_143]: (k2_relat_1(A_143)=k1_xboole_0 | ~v1_xboole_0(A_143))), inference(resolution, [status(thm)], [c_427, c_10])).
% 2.48/1.46  tff(c_450, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_444])).
% 2.48/1.46  tff(c_455, plain, $false, inference(negUnitSimplification, [status(thm)], [c_310, c_450])).
% 2.48/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.46  
% 2.48/1.46  Inference rules
% 2.48/1.46  ----------------------
% 2.48/1.46  #Ref     : 0
% 2.48/1.46  #Sup     : 89
% 2.48/1.46  #Fact    : 0
% 2.48/1.46  #Define  : 0
% 2.48/1.46  #Split   : 2
% 2.48/1.46  #Chain   : 0
% 2.48/1.46  #Close   : 0
% 2.48/1.46  
% 2.48/1.47  Ordering : KBO
% 2.48/1.47  
% 2.48/1.47  Simplification rules
% 2.48/1.47  ----------------------
% 2.48/1.47  #Subsume      : 0
% 2.48/1.47  #Demod        : 19
% 2.48/1.47  #Tautology    : 59
% 2.48/1.47  #SimpNegUnit  : 2
% 2.48/1.47  #BackRed      : 0
% 2.48/1.47  
% 2.48/1.47  #Partial instantiations: 0
% 2.48/1.47  #Strategies tried      : 1
% 2.48/1.47  
% 2.48/1.47  Timing (in seconds)
% 2.48/1.47  ----------------------
% 2.48/1.47  Preprocessing        : 0.41
% 2.48/1.47  Parsing              : 0.22
% 2.48/1.47  CNF conversion       : 0.02
% 2.48/1.47  Main loop            : 0.22
% 2.48/1.47  Inferencing          : 0.08
% 2.48/1.47  Reduction            : 0.06
% 2.48/1.47  Demodulation         : 0.04
% 2.48/1.47  BG Simplification    : 0.02
% 2.48/1.47  Subsumption          : 0.04
% 2.48/1.47  Abstraction          : 0.02
% 2.48/1.47  MUC search           : 0.00
% 2.48/1.47  Cooper               : 0.00
% 2.48/1.47  Total                : 0.65
% 2.48/1.47  Index Insertion      : 0.00
% 2.48/1.47  Index Deletion       : 0.00
% 2.48/1.47  Index Matching       : 0.00
% 2.48/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
