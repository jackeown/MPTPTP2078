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
% DateTime   : Thu Dec  3 09:58:53 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 126 expanded)
%              Number of leaves         :   40 (  61 expanded)
%              Depth                    :    9
%              Number of atoms          :   76 ( 147 expanded)
%              Number of equality atoms :   33 (  76 expanded)
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

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

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

tff(c_52,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_96,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_253,plain,(
    ! [C_103,A_104] :
      ( r2_hidden(k4_tarski(C_103,'#skF_5'(A_104,k1_relat_1(A_104),C_103)),A_104)
      | ~ r2_hidden(C_103,k1_relat_1(A_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_265,plain,(
    ! [A_105,C_106] :
      ( ~ v1_xboole_0(A_105)
      | ~ r2_hidden(C_106,k1_relat_1(A_105)) ) ),
    inference(resolution,[status(thm)],[c_253,c_2])).

tff(c_279,plain,(
    ! [A_107] :
      ( ~ v1_xboole_0(A_107)
      | v1_xboole_0(k1_relat_1(A_107)) ) ),
    inference(resolution,[status(thm)],[c_4,c_265])).

tff(c_10,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_295,plain,(
    ! [A_109] :
      ( k1_relat_1(A_109) = k1_xboole_0
      | ~ v1_xboole_0(A_109) ) ),
    inference(resolution,[status(thm)],[c_279,c_10])).

tff(c_301,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_295])).

tff(c_306,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_301])).

tff(c_307,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_76,plain,(
    ! [A_69] :
      ( v1_relat_1(A_69)
      | ~ v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_80,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_76])).

tff(c_308,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_14,plain,(
    ! [A_10] : k5_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_349,plain,(
    ! [A_116,B_117] : k5_xboole_0(A_116,k3_xboole_0(A_116,B_117)) = k4_xboole_0(A_116,B_117) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_358,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_349])).

tff(c_361,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_358])).

tff(c_28,plain,(
    ! [A_38,B_39] : k6_subset_1(A_38,B_39) = k4_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_50,plain,(
    ! [A_63,B_65] :
      ( k6_subset_1(k4_relat_1(A_63),k4_relat_1(B_65)) = k4_relat_1(k6_subset_1(A_63,B_65))
      | ~ v1_relat_1(B_65)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_814,plain,(
    ! [A_162,B_163] :
      ( k4_xboole_0(k4_relat_1(A_162),k4_relat_1(B_163)) = k4_relat_1(k4_xboole_0(A_162,B_163))
      | ~ v1_relat_1(B_163)
      | ~ v1_relat_1(A_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_50])).

tff(c_821,plain,(
    ! [B_163] :
      ( k4_relat_1(k4_xboole_0(B_163,B_163)) = k1_xboole_0
      | ~ v1_relat_1(B_163)
      | ~ v1_relat_1(B_163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_814,c_361])).

tff(c_830,plain,(
    ! [B_163] :
      ( k4_relat_1(k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_163)
      | ~ v1_relat_1(B_163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_821])).

tff(c_834,plain,(
    ! [B_164] :
      ( ~ v1_relat_1(B_164)
      | ~ v1_relat_1(B_164) ) ),
    inference(splitLeft,[status(thm)],[c_830])).

tff(c_842,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_80,c_834])).

tff(c_849,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_842])).

tff(c_850,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_830])).

tff(c_46,plain,(
    ! [A_62] :
      ( k2_relat_1(k4_relat_1(A_62)) = k1_relat_1(A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_866,plain,
    ( k2_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_850,c_46])).

tff(c_881,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_308,c_866])).

tff(c_883,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_307,c_881])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:34:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.46  
% 2.66/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.46  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 2.66/1.46  
% 2.66/1.46  %Foreground sorts:
% 2.66/1.46  
% 2.66/1.46  
% 2.66/1.46  %Background operators:
% 2.66/1.46  
% 2.66/1.46  
% 2.66/1.46  %Foreground operators:
% 2.66/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.66/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.66/1.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.66/1.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.66/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.66/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.66/1.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.66/1.46  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.66/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.66/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.66/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.66/1.46  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.66/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.66/1.46  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.66/1.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.66/1.46  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.66/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.66/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.66/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.66/1.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.66/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.66/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.66/1.46  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.66/1.46  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.66/1.46  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.66/1.46  
% 3.08/1.48  tff(f_87, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.08/1.48  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.08/1.48  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.08/1.48  tff(f_70, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.08/1.48  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.08/1.48  tff(f_62, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.08/1.48  tff(f_42, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.08/1.48  tff(f_34, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.08/1.48  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.08/1.48  tff(f_56, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.08/1.48  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k6_subset_1(A, B)) = k6_subset_1(k4_relat_1(A), k4_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_relat_1)).
% 3.08/1.48  tff(f_76, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 3.08/1.48  tff(c_52, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.08/1.48  tff(c_96, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_52])).
% 3.08/1.48  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.08/1.48  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.08/1.48  tff(c_253, plain, (![C_103, A_104]: (r2_hidden(k4_tarski(C_103, '#skF_5'(A_104, k1_relat_1(A_104), C_103)), A_104) | ~r2_hidden(C_103, k1_relat_1(A_104)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.08/1.48  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.08/1.48  tff(c_265, plain, (![A_105, C_106]: (~v1_xboole_0(A_105) | ~r2_hidden(C_106, k1_relat_1(A_105)))), inference(resolution, [status(thm)], [c_253, c_2])).
% 3.08/1.48  tff(c_279, plain, (![A_107]: (~v1_xboole_0(A_107) | v1_xboole_0(k1_relat_1(A_107)))), inference(resolution, [status(thm)], [c_4, c_265])).
% 3.08/1.48  tff(c_10, plain, (![A_7]: (k1_xboole_0=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.08/1.48  tff(c_295, plain, (![A_109]: (k1_relat_1(A_109)=k1_xboole_0 | ~v1_xboole_0(A_109))), inference(resolution, [status(thm)], [c_279, c_10])).
% 3.08/1.48  tff(c_301, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_295])).
% 3.08/1.48  tff(c_306, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_301])).
% 3.08/1.48  tff(c_307, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 3.08/1.48  tff(c_76, plain, (![A_69]: (v1_relat_1(A_69) | ~v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.08/1.48  tff(c_80, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_76])).
% 3.08/1.48  tff(c_308, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 3.08/1.48  tff(c_14, plain, (![A_10]: (k5_xboole_0(A_10, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.08/1.48  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.08/1.48  tff(c_349, plain, (![A_116, B_117]: (k5_xboole_0(A_116, k3_xboole_0(A_116, B_117))=k4_xboole_0(A_116, B_117))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.08/1.48  tff(c_358, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_349])).
% 3.08/1.48  tff(c_361, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_358])).
% 3.08/1.48  tff(c_28, plain, (![A_38, B_39]: (k6_subset_1(A_38, B_39)=k4_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.08/1.48  tff(c_50, plain, (![A_63, B_65]: (k6_subset_1(k4_relat_1(A_63), k4_relat_1(B_65))=k4_relat_1(k6_subset_1(A_63, B_65)) | ~v1_relat_1(B_65) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.08/1.48  tff(c_814, plain, (![A_162, B_163]: (k4_xboole_0(k4_relat_1(A_162), k4_relat_1(B_163))=k4_relat_1(k4_xboole_0(A_162, B_163)) | ~v1_relat_1(B_163) | ~v1_relat_1(A_162))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_50])).
% 3.08/1.48  tff(c_821, plain, (![B_163]: (k4_relat_1(k4_xboole_0(B_163, B_163))=k1_xboole_0 | ~v1_relat_1(B_163) | ~v1_relat_1(B_163))), inference(superposition, [status(thm), theory('equality')], [c_814, c_361])).
% 3.08/1.48  tff(c_830, plain, (![B_163]: (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_163) | ~v1_relat_1(B_163))), inference(demodulation, [status(thm), theory('equality')], [c_361, c_821])).
% 3.08/1.48  tff(c_834, plain, (![B_164]: (~v1_relat_1(B_164) | ~v1_relat_1(B_164))), inference(splitLeft, [status(thm)], [c_830])).
% 3.08/1.48  tff(c_842, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_80, c_834])).
% 3.08/1.48  tff(c_849, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_842])).
% 3.08/1.48  tff(c_850, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_830])).
% 3.08/1.48  tff(c_46, plain, (![A_62]: (k2_relat_1(k4_relat_1(A_62))=k1_relat_1(A_62) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.08/1.48  tff(c_866, plain, (k2_relat_1(k1_xboole_0)=k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_850, c_46])).
% 3.08/1.48  tff(c_881, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_80, c_308, c_866])).
% 3.08/1.48  tff(c_883, plain, $false, inference(negUnitSimplification, [status(thm)], [c_307, c_881])).
% 3.08/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.48  
% 3.08/1.48  Inference rules
% 3.08/1.48  ----------------------
% 3.08/1.48  #Ref     : 0
% 3.08/1.48  #Sup     : 192
% 3.08/1.48  #Fact    : 0
% 3.08/1.48  #Define  : 0
% 3.08/1.48  #Split   : 3
% 3.08/1.48  #Chain   : 0
% 3.08/1.48  #Close   : 0
% 3.08/1.48  
% 3.08/1.48  Ordering : KBO
% 3.08/1.48  
% 3.08/1.48  Simplification rules
% 3.08/1.48  ----------------------
% 3.08/1.48  #Subsume      : 18
% 3.08/1.48  #Demod        : 121
% 3.08/1.48  #Tautology    : 113
% 3.08/1.48  #SimpNegUnit  : 3
% 3.08/1.48  #BackRed      : 0
% 3.08/1.48  
% 3.08/1.48  #Partial instantiations: 0
% 3.08/1.48  #Strategies tried      : 1
% 3.08/1.48  
% 3.08/1.48  Timing (in seconds)
% 3.08/1.48  ----------------------
% 3.08/1.48  Preprocessing        : 0.35
% 3.08/1.48  Parsing              : 0.18
% 3.08/1.48  CNF conversion       : 0.03
% 3.08/1.48  Main loop            : 0.35
% 3.08/1.48  Inferencing          : 0.13
% 3.08/1.48  Reduction            : 0.10
% 3.08/1.48  Demodulation         : 0.07
% 3.08/1.49  BG Simplification    : 0.02
% 3.08/1.49  Subsumption          : 0.07
% 3.08/1.49  Abstraction          : 0.02
% 3.08/1.49  MUC search           : 0.00
% 3.08/1.49  Cooper               : 0.00
% 3.08/1.49  Total                : 0.74
% 3.08/1.49  Index Insertion      : 0.00
% 3.08/1.49  Index Deletion       : 0.00
% 3.08/1.49  Index Matching       : 0.00
% 3.08/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
