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
% DateTime   : Thu Dec  3 10:04:33 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   65 (  86 expanded)
%              Number of leaves         :   29 (  41 expanded)
%              Depth                    :    7
%              Number of atoms          :   82 ( 123 expanded)
%              Number of equality atoms :   43 (  62 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_36,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_151,plain,(
    ~ r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_42,plain,
    ( r2_hidden('#skF_1',k2_relat_1('#skF_2'))
    | k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_258,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_42])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_167,plain,(
    ! [A_38,B_39] :
      ( r1_xboole_0(k1_tarski(A_38),B_39)
      | r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_221,plain,(
    ! [A_44,B_45] :
      ( k3_xboole_0(k1_tarski(A_44),B_45) = k1_xboole_0
      | r2_hidden(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_167,c_4])).

tff(c_244,plain,(
    ! [B_2,A_44] :
      ( k3_xboole_0(B_2,k1_tarski(A_44)) = k1_xboole_0
      | r2_hidden(A_44,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_221])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_412,plain,(
    ! [B_59,A_60] :
      ( k10_relat_1(B_59,A_60) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_59),A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_523,plain,(
    ! [B_85,B_86] :
      ( k10_relat_1(B_85,B_86) = k1_xboole_0
      | ~ v1_relat_1(B_85)
      | k3_xboole_0(k2_relat_1(B_85),B_86) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_412])).

tff(c_794,plain,(
    ! [B_100,A_101] :
      ( k10_relat_1(B_100,k1_tarski(A_101)) = k1_xboole_0
      | ~ v1_relat_1(B_100)
      | r2_hidden(A_101,k2_relat_1(B_100)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_523])).

tff(c_800,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_794,c_151])).

tff(c_804,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_800])).

tff(c_806,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_258,c_804])).

tff(c_807,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_808,plain,(
    r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_12,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_834,plain,(
    ! [A_108,B_109] : k5_xboole_0(A_108,k3_xboole_0(A_108,B_109)) = k4_xboole_0(A_108,B_109) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_852,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = k4_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_834])).

tff(c_855,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_852])).

tff(c_927,plain,(
    ! [B_117,A_118] :
      ( r1_xboole_0(k2_relat_1(B_117),A_118)
      | k10_relat_1(B_117,A_118) != k1_xboole_0
      | ~ v1_relat_1(B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1141,plain,(
    ! [B_150,A_151] :
      ( k3_xboole_0(k2_relat_1(B_150),A_151) = k1_xboole_0
      | k10_relat_1(B_150,A_151) != k1_xboole_0
      | ~ v1_relat_1(B_150) ) ),
    inference(resolution,[status(thm)],[c_927,c_4])).

tff(c_849,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_834])).

tff(c_1151,plain,(
    ! [A_151,B_150] :
      ( k4_xboole_0(A_151,k2_relat_1(B_150)) = k5_xboole_0(A_151,k1_xboole_0)
      | k10_relat_1(B_150,A_151) != k1_xboole_0
      | ~ v1_relat_1(B_150) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1141,c_849])).

tff(c_1361,plain,(
    ! [A_162,B_163] :
      ( k4_xboole_0(A_162,k2_relat_1(B_163)) = A_162
      | k10_relat_1(B_163,A_162) != k1_xboole_0
      | ~ v1_relat_1(B_163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_855,c_1151])).

tff(c_14,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1083,plain,(
    ! [A_129,C_130,B_131] :
      ( ~ r2_hidden(A_129,C_130)
      | k4_xboole_0(k2_tarski(A_129,B_131),C_130) != k2_tarski(A_129,B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1090,plain,(
    ! [A_9,C_130] :
      ( ~ r2_hidden(A_9,C_130)
      | k4_xboole_0(k1_tarski(A_9),C_130) != k2_tarski(A_9,A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1083])).

tff(c_1096,plain,(
    ! [A_9,C_130] :
      ( ~ r2_hidden(A_9,C_130)
      | k4_xboole_0(k1_tarski(A_9),C_130) != k1_tarski(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1090])).

tff(c_1416,plain,(
    ! [A_166,B_167] :
      ( ~ r2_hidden(A_166,k2_relat_1(B_167))
      | k10_relat_1(B_167,k1_tarski(A_166)) != k1_xboole_0
      | ~ v1_relat_1(B_167) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1361,c_1096])).

tff(c_1422,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_808,c_1416])).

tff(c_1427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_807,c_1422])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:06:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.42  
% 2.84/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.42  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.84/1.42  
% 2.84/1.42  %Foreground sorts:
% 2.84/1.42  
% 2.84/1.42  
% 2.84/1.42  %Background operators:
% 2.84/1.42  
% 2.84/1.42  
% 2.84/1.42  %Foreground operators:
% 2.84/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.84/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.84/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.84/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.84/1.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.84/1.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.84/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.84/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.84/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.84/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.84/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.84/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.84/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.84/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.42  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.84/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.84/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.84/1.42  
% 2.84/1.44  tff(f_72, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 2.84/1.44  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.84/1.44  tff(f_50, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.84/1.44  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.84/1.44  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 2.84/1.44  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.84/1.44  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.84/1.44  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.84/1.44  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.84/1.44  tff(f_58, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 2.84/1.44  tff(c_34, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.84/1.44  tff(c_36, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.84/1.44  tff(c_151, plain, (~r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_36])).
% 2.84/1.44  tff(c_42, plain, (r2_hidden('#skF_1', k2_relat_1('#skF_2')) | k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.84/1.44  tff(c_258, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_151, c_42])).
% 2.84/1.44  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.84/1.44  tff(c_167, plain, (![A_38, B_39]: (r1_xboole_0(k1_tarski(A_38), B_39) | r2_hidden(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.84/1.44  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.84/1.44  tff(c_221, plain, (![A_44, B_45]: (k3_xboole_0(k1_tarski(A_44), B_45)=k1_xboole_0 | r2_hidden(A_44, B_45))), inference(resolution, [status(thm)], [c_167, c_4])).
% 2.84/1.44  tff(c_244, plain, (![B_2, A_44]: (k3_xboole_0(B_2, k1_tarski(A_44))=k1_xboole_0 | r2_hidden(A_44, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_221])).
% 2.84/1.44  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.84/1.44  tff(c_412, plain, (![B_59, A_60]: (k10_relat_1(B_59, A_60)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_59), A_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.84/1.44  tff(c_523, plain, (![B_85, B_86]: (k10_relat_1(B_85, B_86)=k1_xboole_0 | ~v1_relat_1(B_85) | k3_xboole_0(k2_relat_1(B_85), B_86)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_412])).
% 2.84/1.44  tff(c_794, plain, (![B_100, A_101]: (k10_relat_1(B_100, k1_tarski(A_101))=k1_xboole_0 | ~v1_relat_1(B_100) | r2_hidden(A_101, k2_relat_1(B_100)))), inference(superposition, [status(thm), theory('equality')], [c_244, c_523])).
% 2.84/1.44  tff(c_800, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_794, c_151])).
% 2.84/1.44  tff(c_804, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_800])).
% 2.84/1.44  tff(c_806, plain, $false, inference(negUnitSimplification, [status(thm)], [c_258, c_804])).
% 2.84/1.44  tff(c_807, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 2.84/1.44  tff(c_808, plain, (r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_36])).
% 2.84/1.44  tff(c_12, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.84/1.44  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.84/1.44  tff(c_834, plain, (![A_108, B_109]: (k5_xboole_0(A_108, k3_xboole_0(A_108, B_109))=k4_xboole_0(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.84/1.44  tff(c_852, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=k4_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_834])).
% 2.84/1.44  tff(c_855, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_852])).
% 2.84/1.44  tff(c_927, plain, (![B_117, A_118]: (r1_xboole_0(k2_relat_1(B_117), A_118) | k10_relat_1(B_117, A_118)!=k1_xboole_0 | ~v1_relat_1(B_117))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.84/1.44  tff(c_1141, plain, (![B_150, A_151]: (k3_xboole_0(k2_relat_1(B_150), A_151)=k1_xboole_0 | k10_relat_1(B_150, A_151)!=k1_xboole_0 | ~v1_relat_1(B_150))), inference(resolution, [status(thm)], [c_927, c_4])).
% 2.84/1.44  tff(c_849, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_834])).
% 2.84/1.44  tff(c_1151, plain, (![A_151, B_150]: (k4_xboole_0(A_151, k2_relat_1(B_150))=k5_xboole_0(A_151, k1_xboole_0) | k10_relat_1(B_150, A_151)!=k1_xboole_0 | ~v1_relat_1(B_150))), inference(superposition, [status(thm), theory('equality')], [c_1141, c_849])).
% 2.84/1.44  tff(c_1361, plain, (![A_162, B_163]: (k4_xboole_0(A_162, k2_relat_1(B_163))=A_162 | k10_relat_1(B_163, A_162)!=k1_xboole_0 | ~v1_relat_1(B_163))), inference(demodulation, [status(thm), theory('equality')], [c_855, c_1151])).
% 2.84/1.44  tff(c_14, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.84/1.44  tff(c_1083, plain, (![A_129, C_130, B_131]: (~r2_hidden(A_129, C_130) | k4_xboole_0(k2_tarski(A_129, B_131), C_130)!=k2_tarski(A_129, B_131))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.84/1.44  tff(c_1090, plain, (![A_9, C_130]: (~r2_hidden(A_9, C_130) | k4_xboole_0(k1_tarski(A_9), C_130)!=k2_tarski(A_9, A_9))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1083])).
% 2.84/1.44  tff(c_1096, plain, (![A_9, C_130]: (~r2_hidden(A_9, C_130) | k4_xboole_0(k1_tarski(A_9), C_130)!=k1_tarski(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1090])).
% 2.84/1.44  tff(c_1416, plain, (![A_166, B_167]: (~r2_hidden(A_166, k2_relat_1(B_167)) | k10_relat_1(B_167, k1_tarski(A_166))!=k1_xboole_0 | ~v1_relat_1(B_167))), inference(superposition, [status(thm), theory('equality')], [c_1361, c_1096])).
% 2.84/1.44  tff(c_1422, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_808, c_1416])).
% 2.84/1.44  tff(c_1427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_807, c_1422])).
% 2.84/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.44  
% 2.84/1.44  Inference rules
% 2.84/1.44  ----------------------
% 2.84/1.44  #Ref     : 0
% 2.84/1.44  #Sup     : 306
% 2.84/1.44  #Fact    : 0
% 2.84/1.44  #Define  : 0
% 2.84/1.44  #Split   : 1
% 2.84/1.44  #Chain   : 0
% 2.84/1.44  #Close   : 0
% 2.84/1.44  
% 2.84/1.44  Ordering : KBO
% 2.84/1.44  
% 2.84/1.44  Simplification rules
% 2.84/1.44  ----------------------
% 2.84/1.44  #Subsume      : 50
% 2.84/1.44  #Demod        : 52
% 2.84/1.44  #Tautology    : 201
% 2.84/1.44  #SimpNegUnit  : 6
% 2.84/1.44  #BackRed      : 0
% 2.84/1.44  
% 2.84/1.44  #Partial instantiations: 0
% 2.84/1.44  #Strategies tried      : 1
% 2.84/1.44  
% 2.84/1.44  Timing (in seconds)
% 2.84/1.44  ----------------------
% 2.84/1.44  Preprocessing        : 0.28
% 2.84/1.44  Parsing              : 0.15
% 2.84/1.44  CNF conversion       : 0.02
% 2.84/1.44  Main loop            : 0.38
% 2.84/1.44  Inferencing          : 0.15
% 2.84/1.44  Reduction            : 0.12
% 2.84/1.44  Demodulation         : 0.08
% 2.84/1.44  BG Simplification    : 0.02
% 2.84/1.44  Subsumption          : 0.06
% 2.84/1.44  Abstraction          : 0.02
% 2.84/1.44  MUC search           : 0.00
% 2.84/1.44  Cooper               : 0.00
% 2.84/1.44  Total                : 0.69
% 2.84/1.44  Index Insertion      : 0.00
% 2.84/1.44  Index Deletion       : 0.00
% 2.84/1.44  Index Matching       : 0.00
% 2.84/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
