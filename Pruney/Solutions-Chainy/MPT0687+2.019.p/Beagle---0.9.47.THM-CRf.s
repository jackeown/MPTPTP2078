%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:35 EST 2020

% Result     : Theorem 5.37s
% Output     : CNFRefutation 5.37s
% Verified   : 
% Statistics : Number of formulae       :   65 (  94 expanded)
%              Number of leaves         :   27 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :   95 ( 175 expanded)
%              Number of equality atoms :   25 (  45 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_59,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_56,plain,
    ( r2_hidden('#skF_4',k2_relat_1('#skF_5'))
    | k10_relat_1('#skF_5',k1_tarski('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_105,plain,(
    k10_relat_1('#skF_5',k1_tarski('#skF_4')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_30,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_247,plain,(
    ! [A_81,B_82,C_83] :
      ( k4_xboole_0(k2_tarski(A_81,B_82),C_83) = k2_tarski(A_81,B_82)
      | r2_hidden(B_82,C_83)
      | r2_hidden(A_81,C_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_83,plain,(
    ! [D_40,B_41,A_42] :
      ( ~ r2_hidden(D_40,B_41)
      | ~ r2_hidden(D_40,k4_xboole_0(A_42,B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_177,plain,(
    ! [A_74,A_75,B_76] :
      ( ~ r2_hidden('#skF_3'(A_74,k4_xboole_0(A_75,B_76)),B_76)
      | r1_xboole_0(A_74,k4_xboole_0(A_75,B_76)) ) ),
    inference(resolution,[status(thm)],[c_22,c_83])).

tff(c_187,plain,(
    ! [A_7,A_75] : r1_xboole_0(A_7,k4_xboole_0(A_75,A_7)) ),
    inference(resolution,[status(thm)],[c_24,c_177])).

tff(c_620,plain,(
    ! [C_128,A_129,B_130] :
      ( r1_xboole_0(C_128,k2_tarski(A_129,B_130))
      | r2_hidden(B_130,C_128)
      | r2_hidden(A_129,C_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_187])).

tff(c_636,plain,(
    ! [C_131,A_132] :
      ( r1_xboole_0(C_131,k1_tarski(A_132))
      | r2_hidden(A_132,C_131)
      | r2_hidden(A_132,C_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_620])).

tff(c_44,plain,(
    ! [B_28,A_27] :
      ( k10_relat_1(B_28,A_27) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_28),A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1040,plain,(
    ! [B_161,A_162] :
      ( k10_relat_1(B_161,k1_tarski(A_162)) = k1_xboole_0
      | ~ v1_relat_1(B_161)
      | r2_hidden(A_162,k2_relat_1(B_161)) ) ),
    inference(resolution,[status(thm)],[c_636,c_44])).

tff(c_50,plain,
    ( k10_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0
    | ~ r2_hidden('#skF_4',k2_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_115,plain,(
    ~ r2_hidden('#skF_4',k2_relat_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_50])).

tff(c_1068,plain,
    ( k10_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1040,c_115])).

tff(c_1080,plain,(
    k10_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1068])).

tff(c_1082,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_1080])).

tff(c_1084,plain,(
    k10_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1083,plain,(
    r2_hidden('#skF_4',k2_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k4_xboole_0(A_1,B_2))
      | r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1200,plain,(
    ! [A_195,A_196,B_197] :
      ( ~ r2_hidden('#skF_3'(A_195,k4_xboole_0(A_196,B_197)),B_197)
      | r1_xboole_0(A_195,k4_xboole_0(A_196,B_197)) ) ),
    inference(resolution,[status(thm)],[c_22,c_83])).

tff(c_1214,plain,(
    ! [A_198,A_199] : r1_xboole_0(A_198,k4_xboole_0(A_199,A_198)) ),
    inference(resolution,[status(thm)],[c_24,c_1200])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = A_12
      | ~ r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1230,plain,(
    ! [A_200,A_201] : k4_xboole_0(A_200,k4_xboole_0(A_201,A_200)) = A_200 ),
    inference(resolution,[status(thm)],[c_1214,c_26])).

tff(c_1133,plain,(
    ! [A_177,C_178,B_179] :
      ( ~ r2_hidden(A_177,C_178)
      | k4_xboole_0(k2_tarski(A_177,B_179),C_178) != k2_tarski(A_177,B_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1136,plain,(
    ! [A_14,C_178] :
      ( ~ r2_hidden(A_14,C_178)
      | k4_xboole_0(k1_tarski(A_14),C_178) != k2_tarski(A_14,A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1133])).

tff(c_1137,plain,(
    ! [A_14,C_178] :
      ( ~ r2_hidden(A_14,C_178)
      | k4_xboole_0(k1_tarski(A_14),C_178) != k1_tarski(A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1136])).

tff(c_1304,plain,(
    ! [A_204,A_205] : ~ r2_hidden(A_204,k4_xboole_0(A_205,k1_tarski(A_204))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1230,c_1137])).

tff(c_1345,plain,(
    ! [D_215,A_216] :
      ( r2_hidden(D_215,k1_tarski(D_215))
      | ~ r2_hidden(D_215,A_216) ) ),
    inference(resolution,[status(thm)],[c_2,c_1304])).

tff(c_1355,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1083,c_1345])).

tff(c_1104,plain,(
    ! [B_169,A_170] :
      ( r1_xboole_0(k2_relat_1(B_169),A_170)
      | k10_relat_1(B_169,A_170) != k1_xboole_0
      | ~ v1_relat_1(B_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_20,plain,(
    ! [A_7,B_8,C_11] :
      ( ~ r1_xboole_0(A_7,B_8)
      | ~ r2_hidden(C_11,B_8)
      | ~ r2_hidden(C_11,A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5671,plain,(
    ! [C_381,A_382,B_383] :
      ( ~ r2_hidden(C_381,A_382)
      | ~ r2_hidden(C_381,k2_relat_1(B_383))
      | k10_relat_1(B_383,A_382) != k1_xboole_0
      | ~ v1_relat_1(B_383) ) ),
    inference(resolution,[status(thm)],[c_1104,c_20])).

tff(c_5737,plain,(
    ! [B_384] :
      ( ~ r2_hidden('#skF_4',k2_relat_1(B_384))
      | k10_relat_1(B_384,k1_tarski('#skF_4')) != k1_xboole_0
      | ~ v1_relat_1(B_384) ) ),
    inference(resolution,[status(thm)],[c_1355,c_5671])).

tff(c_5744,plain,
    ( k10_relat_1('#skF_5',k1_tarski('#skF_4')) != k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1083,c_5737])).

tff(c_5749,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1084,c_5744])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 15:49:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.37/2.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.37/2.02  
% 5.37/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.37/2.02  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 5.37/2.02  
% 5.37/2.02  %Foreground sorts:
% 5.37/2.02  
% 5.37/2.02  
% 5.37/2.02  %Background operators:
% 5.37/2.02  
% 5.37/2.02  
% 5.37/2.02  %Foreground operators:
% 5.37/2.02  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.37/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.37/2.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.37/2.02  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.37/2.02  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.37/2.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.37/2.02  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.37/2.02  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.37/2.02  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.37/2.02  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.37/2.02  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.37/2.02  tff('#skF_5', type, '#skF_5': $i).
% 5.37/2.02  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.37/2.02  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.37/2.02  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.37/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.37/2.02  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.37/2.02  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.37/2.02  tff('#skF_4', type, '#skF_4': $i).
% 5.37/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.37/2.02  
% 5.37/2.03  tff(f_87, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 5.37/2.03  tff(f_59, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.37/2.03  tff(f_73, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 5.37/2.03  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.37/2.03  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.37/2.03  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 5.37/2.03  tff(f_57, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 5.37/2.03  tff(c_48, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.37/2.03  tff(c_56, plain, (r2_hidden('#skF_4', k2_relat_1('#skF_5')) | k10_relat_1('#skF_5', k1_tarski('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.37/2.03  tff(c_105, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_56])).
% 5.37/2.03  tff(c_30, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.37/2.03  tff(c_247, plain, (![A_81, B_82, C_83]: (k4_xboole_0(k2_tarski(A_81, B_82), C_83)=k2_tarski(A_81, B_82) | r2_hidden(B_82, C_83) | r2_hidden(A_81, C_83))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.37/2.03  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.37/2.03  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.37/2.03  tff(c_83, plain, (![D_40, B_41, A_42]: (~r2_hidden(D_40, B_41) | ~r2_hidden(D_40, k4_xboole_0(A_42, B_41)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.37/2.03  tff(c_177, plain, (![A_74, A_75, B_76]: (~r2_hidden('#skF_3'(A_74, k4_xboole_0(A_75, B_76)), B_76) | r1_xboole_0(A_74, k4_xboole_0(A_75, B_76)))), inference(resolution, [status(thm)], [c_22, c_83])).
% 5.37/2.03  tff(c_187, plain, (![A_7, A_75]: (r1_xboole_0(A_7, k4_xboole_0(A_75, A_7)))), inference(resolution, [status(thm)], [c_24, c_177])).
% 5.37/2.03  tff(c_620, plain, (![C_128, A_129, B_130]: (r1_xboole_0(C_128, k2_tarski(A_129, B_130)) | r2_hidden(B_130, C_128) | r2_hidden(A_129, C_128))), inference(superposition, [status(thm), theory('equality')], [c_247, c_187])).
% 5.37/2.03  tff(c_636, plain, (![C_131, A_132]: (r1_xboole_0(C_131, k1_tarski(A_132)) | r2_hidden(A_132, C_131) | r2_hidden(A_132, C_131))), inference(superposition, [status(thm), theory('equality')], [c_30, c_620])).
% 5.37/2.03  tff(c_44, plain, (![B_28, A_27]: (k10_relat_1(B_28, A_27)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_28), A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.37/2.03  tff(c_1040, plain, (![B_161, A_162]: (k10_relat_1(B_161, k1_tarski(A_162))=k1_xboole_0 | ~v1_relat_1(B_161) | r2_hidden(A_162, k2_relat_1(B_161)))), inference(resolution, [status(thm)], [c_636, c_44])).
% 5.37/2.03  tff(c_50, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0 | ~r2_hidden('#skF_4', k2_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.37/2.03  tff(c_115, plain, (~r2_hidden('#skF_4', k2_relat_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_105, c_50])).
% 5.37/2.03  tff(c_1068, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1040, c_115])).
% 5.37/2.03  tff(c_1080, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1068])).
% 5.37/2.03  tff(c_1082, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105, c_1080])).
% 5.37/2.03  tff(c_1084, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 5.37/2.03  tff(c_1083, plain, (r2_hidden('#skF_4', k2_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_56])).
% 5.37/2.03  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k4_xboole_0(A_1, B_2)) | r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.37/2.03  tff(c_1200, plain, (![A_195, A_196, B_197]: (~r2_hidden('#skF_3'(A_195, k4_xboole_0(A_196, B_197)), B_197) | r1_xboole_0(A_195, k4_xboole_0(A_196, B_197)))), inference(resolution, [status(thm)], [c_22, c_83])).
% 5.37/2.03  tff(c_1214, plain, (![A_198, A_199]: (r1_xboole_0(A_198, k4_xboole_0(A_199, A_198)))), inference(resolution, [status(thm)], [c_24, c_1200])).
% 5.37/2.03  tff(c_26, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=A_12 | ~r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.37/2.03  tff(c_1230, plain, (![A_200, A_201]: (k4_xboole_0(A_200, k4_xboole_0(A_201, A_200))=A_200)), inference(resolution, [status(thm)], [c_1214, c_26])).
% 5.37/2.03  tff(c_1133, plain, (![A_177, C_178, B_179]: (~r2_hidden(A_177, C_178) | k4_xboole_0(k2_tarski(A_177, B_179), C_178)!=k2_tarski(A_177, B_179))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.37/2.03  tff(c_1136, plain, (![A_14, C_178]: (~r2_hidden(A_14, C_178) | k4_xboole_0(k1_tarski(A_14), C_178)!=k2_tarski(A_14, A_14))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1133])).
% 5.37/2.03  tff(c_1137, plain, (![A_14, C_178]: (~r2_hidden(A_14, C_178) | k4_xboole_0(k1_tarski(A_14), C_178)!=k1_tarski(A_14))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1136])).
% 5.37/2.03  tff(c_1304, plain, (![A_204, A_205]: (~r2_hidden(A_204, k4_xboole_0(A_205, k1_tarski(A_204))))), inference(superposition, [status(thm), theory('equality')], [c_1230, c_1137])).
% 5.37/2.03  tff(c_1345, plain, (![D_215, A_216]: (r2_hidden(D_215, k1_tarski(D_215)) | ~r2_hidden(D_215, A_216))), inference(resolution, [status(thm)], [c_2, c_1304])).
% 5.37/2.03  tff(c_1355, plain, (r2_hidden('#skF_4', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_1083, c_1345])).
% 5.37/2.03  tff(c_1104, plain, (![B_169, A_170]: (r1_xboole_0(k2_relat_1(B_169), A_170) | k10_relat_1(B_169, A_170)!=k1_xboole_0 | ~v1_relat_1(B_169))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.37/2.03  tff(c_20, plain, (![A_7, B_8, C_11]: (~r1_xboole_0(A_7, B_8) | ~r2_hidden(C_11, B_8) | ~r2_hidden(C_11, A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.37/2.03  tff(c_5671, plain, (![C_381, A_382, B_383]: (~r2_hidden(C_381, A_382) | ~r2_hidden(C_381, k2_relat_1(B_383)) | k10_relat_1(B_383, A_382)!=k1_xboole_0 | ~v1_relat_1(B_383))), inference(resolution, [status(thm)], [c_1104, c_20])).
% 5.37/2.03  tff(c_5737, plain, (![B_384]: (~r2_hidden('#skF_4', k2_relat_1(B_384)) | k10_relat_1(B_384, k1_tarski('#skF_4'))!=k1_xboole_0 | ~v1_relat_1(B_384))), inference(resolution, [status(thm)], [c_1355, c_5671])).
% 5.37/2.03  tff(c_5744, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))!=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1083, c_5737])).
% 5.37/2.03  tff(c_5749, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_1084, c_5744])).
% 5.37/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.37/2.03  
% 5.37/2.03  Inference rules
% 5.37/2.03  ----------------------
% 5.37/2.03  #Ref     : 0
% 5.37/2.03  #Sup     : 1445
% 5.37/2.03  #Fact    : 0
% 5.37/2.03  #Define  : 0
% 5.37/2.03  #Split   : 1
% 5.37/2.03  #Chain   : 0
% 5.37/2.03  #Close   : 0
% 5.37/2.03  
% 5.37/2.03  Ordering : KBO
% 5.37/2.03  
% 5.37/2.03  Simplification rules
% 5.37/2.03  ----------------------
% 5.37/2.03  #Subsume      : 379
% 5.37/2.03  #Demod        : 418
% 5.37/2.03  #Tautology    : 432
% 5.37/2.03  #SimpNegUnit  : 34
% 5.37/2.03  #BackRed      : 1
% 5.37/2.03  
% 5.37/2.03  #Partial instantiations: 0
% 5.37/2.03  #Strategies tried      : 1
% 5.37/2.03  
% 5.37/2.03  Timing (in seconds)
% 5.37/2.03  ----------------------
% 5.37/2.03  Preprocessing        : 0.31
% 5.37/2.03  Parsing              : 0.16
% 5.37/2.03  CNF conversion       : 0.02
% 5.37/2.03  Main loop            : 0.95
% 5.37/2.03  Inferencing          : 0.33
% 5.37/2.03  Reduction            : 0.29
% 5.37/2.03  Demodulation         : 0.20
% 5.37/2.03  BG Simplification    : 0.04
% 5.37/2.03  Subsumption          : 0.21
% 5.37/2.03  Abstraction          : 0.05
% 5.37/2.04  MUC search           : 0.00
% 5.37/2.04  Cooper               : 0.00
% 5.37/2.04  Total                : 1.29
% 5.37/2.04  Index Insertion      : 0.00
% 5.37/2.04  Index Deletion       : 0.00
% 5.37/2.04  Index Matching       : 0.00
% 5.37/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
