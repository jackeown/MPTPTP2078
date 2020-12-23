%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:18 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 131 expanded)
%              Number of leaves         :   41 (  63 expanded)
%              Depth                    :   12
%              Number of atoms          :  125 ( 210 expanded)
%              Number of equality atoms :   31 (  58 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_124,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_50,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_46,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_48,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_117,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_105,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_114,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_50,plain,
    ( k5_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_77,plain,(
    k5_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_52,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_34,plain,(
    ! [A_39] :
      ( r2_hidden('#skF_2'(A_39),A_39)
      | v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_14,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_110,plain,(
    ! [A_83,B_84,C_85] :
      ( ~ r1_xboole_0(A_83,B_84)
      | ~ r2_hidden(C_85,k3_xboole_0(A_83,B_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_117,plain,(
    ! [A_7,C_85] :
      ( ~ r1_xboole_0(A_7,k1_xboole_0)
      | ~ r2_hidden(C_85,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_110])).

tff(c_121,plain,(
    ! [C_86] : ~ r2_hidden(C_86,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_117])).

tff(c_126,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_34,c_121])).

tff(c_36,plain,(
    ! [A_57,B_58] :
      ( v1_relat_1(k5_relat_1(A_57,B_58))
      | ~ v1_relat_1(B_58)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_12,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_48,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_46,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_190,plain,(
    ! [A_110,B_111] :
      ( k1_relat_1(k5_relat_1(A_110,B_111)) = k1_relat_1(A_110)
      | ~ r1_tarski(k2_relat_1(A_110),k1_relat_1(B_111))
      | ~ v1_relat_1(B_111)
      | ~ v1_relat_1(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_196,plain,(
    ! [B_111] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_111)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_111))
      | ~ v1_relat_1(B_111)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_190])).

tff(c_210,plain,(
    ! [B_118] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_118)) = k1_xboole_0
      | ~ v1_relat_1(B_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_12,c_48,c_196])).

tff(c_38,plain,(
    ! [A_59] :
      ( ~ v1_xboole_0(k1_relat_1(A_59))
      | ~ v1_relat_1(A_59)
      | v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_219,plain,(
    ! [B_118] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_118))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_118))
      | ~ v1_relat_1(B_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_38])).

tff(c_227,plain,(
    ! [B_119] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_119))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_119))
      | ~ v1_relat_1(B_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_219])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_232,plain,(
    ! [B_120] :
      ( k5_relat_1(k1_xboole_0,B_120) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_120))
      | ~ v1_relat_1(B_120) ) ),
    inference(resolution,[status(thm)],[c_227,c_4])).

tff(c_236,plain,(
    ! [B_58] :
      ( k5_relat_1(k1_xboole_0,B_58) = k1_xboole_0
      | ~ v1_relat_1(B_58)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_36,c_232])).

tff(c_240,plain,(
    ! [B_121] :
      ( k5_relat_1(k1_xboole_0,B_121) = k1_xboole_0
      | ~ v1_relat_1(B_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_236])).

tff(c_252,plain,(
    k5_relat_1(k1_xboole_0,'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_240])).

tff(c_259,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_252])).

tff(c_260,plain,(
    k5_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_297,plain,(
    ! [A_131,B_132,C_133] :
      ( ~ r1_xboole_0(A_131,B_132)
      | ~ r2_hidden(C_133,k3_xboole_0(A_131,B_132)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_304,plain,(
    ! [A_7,C_133] :
      ( ~ r1_xboole_0(A_7,k1_xboole_0)
      | ~ r2_hidden(C_133,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_297])).

tff(c_308,plain,(
    ! [C_134] : ~ r2_hidden(C_134,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_304])).

tff(c_313,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_34,c_308])).

tff(c_392,plain,(
    ! [B_166,A_167] :
      ( k2_relat_1(k5_relat_1(B_166,A_167)) = k2_relat_1(A_167)
      | ~ r1_tarski(k1_relat_1(A_167),k2_relat_1(B_166))
      | ~ v1_relat_1(B_166)
      | ~ v1_relat_1(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_395,plain,(
    ! [B_166] :
      ( k2_relat_1(k5_relat_1(B_166,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_166))
      | ~ v1_relat_1(B_166)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_392])).

tff(c_414,plain,(
    ! [B_170] :
      ( k2_relat_1(k5_relat_1(B_170,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_12,c_46,c_395])).

tff(c_40,plain,(
    ! [A_60] :
      ( ~ v1_xboole_0(k2_relat_1(A_60))
      | ~ v1_relat_1(A_60)
      | v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_426,plain,(
    ! [B_170] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_170,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(B_170,k1_xboole_0))
      | ~ v1_relat_1(B_170) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_40])).

tff(c_463,plain,(
    ! [B_172] :
      ( ~ v1_relat_1(k5_relat_1(B_172,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(B_172,k1_xboole_0))
      | ~ v1_relat_1(B_172) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_426])).

tff(c_487,plain,(
    ! [B_181] :
      ( k5_relat_1(B_181,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_181,k1_xboole_0))
      | ~ v1_relat_1(B_181) ) ),
    inference(resolution,[status(thm)],[c_463,c_4])).

tff(c_491,plain,(
    ! [A_57] :
      ( k5_relat_1(A_57,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_57) ) ),
    inference(resolution,[status(thm)],[c_36,c_487])).

tff(c_495,plain,(
    ! [A_182] :
      ( k5_relat_1(A_182,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_491])).

tff(c_507,plain,(
    k5_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_495])).

tff(c_514,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_260,c_507])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.09  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.08/0.28  % Computer   : n011.cluster.edu
% 0.08/0.28  % Model      : x86_64 x86_64
% 0.08/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.28  % Memory     : 8042.1875MB
% 0.08/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.28  % CPULimit   : 60
% 0.08/0.28  % DateTime   : Tue Dec  1 19:59:27 EST 2020
% 0.08/0.28  % CPUTime    : 
% 0.08/0.29  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.34  
% 2.60/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.35  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4
% 2.60/1.35  
% 2.60/1.35  %Foreground sorts:
% 2.60/1.35  
% 2.60/1.35  
% 2.60/1.35  %Background operators:
% 2.60/1.35  
% 2.60/1.35  
% 2.60/1.35  %Foreground operators:
% 2.60/1.35  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.60/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.60/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.60/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.60/1.35  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.60/1.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.60/1.35  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.60/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.60/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.60/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.60/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.60/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.60/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.60/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.60/1.35  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.60/1.35  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.60/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.60/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.60/1.35  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.60/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.60/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.60/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.60/1.35  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.60/1.35  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.60/1.35  
% 2.60/1.36  tff(f_124, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 2.60/1.36  tff(f_74, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.60/1.36  tff(f_50, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.60/1.36  tff(f_46, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.60/1.36  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.60/1.36  tff(f_80, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.60/1.36  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.60/1.36  tff(f_48, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.60/1.36  tff(f_117, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.60/1.36  tff(f_105, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 2.60/1.36  tff(f_88, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.60/1.36  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.60/1.36  tff(f_114, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 2.60/1.36  tff(f_96, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.60/1.36  tff(c_50, plain, (k5_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.60/1.36  tff(c_77, plain, (k5_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_50])).
% 2.60/1.36  tff(c_52, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.60/1.36  tff(c_34, plain, (![A_39]: (r2_hidden('#skF_2'(A_39), A_39) | v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.60/1.36  tff(c_14, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.60/1.36  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.60/1.36  tff(c_110, plain, (![A_83, B_84, C_85]: (~r1_xboole_0(A_83, B_84) | ~r2_hidden(C_85, k3_xboole_0(A_83, B_84)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.60/1.36  tff(c_117, plain, (![A_7, C_85]: (~r1_xboole_0(A_7, k1_xboole_0) | ~r2_hidden(C_85, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_110])).
% 2.60/1.36  tff(c_121, plain, (![C_86]: (~r2_hidden(C_86, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_117])).
% 2.60/1.36  tff(c_126, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_121])).
% 2.60/1.36  tff(c_36, plain, (![A_57, B_58]: (v1_relat_1(k5_relat_1(A_57, B_58)) | ~v1_relat_1(B_58) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.60/1.36  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.60/1.36  tff(c_12, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.60/1.36  tff(c_48, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.60/1.36  tff(c_46, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.60/1.36  tff(c_190, plain, (![A_110, B_111]: (k1_relat_1(k5_relat_1(A_110, B_111))=k1_relat_1(A_110) | ~r1_tarski(k2_relat_1(A_110), k1_relat_1(B_111)) | ~v1_relat_1(B_111) | ~v1_relat_1(A_110))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.60/1.36  tff(c_196, plain, (![B_111]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_111))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_111)) | ~v1_relat_1(B_111) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_190])).
% 2.60/1.36  tff(c_210, plain, (![B_118]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_118))=k1_xboole_0 | ~v1_relat_1(B_118))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_12, c_48, c_196])).
% 2.60/1.36  tff(c_38, plain, (![A_59]: (~v1_xboole_0(k1_relat_1(A_59)) | ~v1_relat_1(A_59) | v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.60/1.36  tff(c_219, plain, (![B_118]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_118)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_118)) | ~v1_relat_1(B_118))), inference(superposition, [status(thm), theory('equality')], [c_210, c_38])).
% 2.60/1.36  tff(c_227, plain, (![B_119]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_119)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_119)) | ~v1_relat_1(B_119))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_219])).
% 2.60/1.36  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.60/1.36  tff(c_232, plain, (![B_120]: (k5_relat_1(k1_xboole_0, B_120)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_120)) | ~v1_relat_1(B_120))), inference(resolution, [status(thm)], [c_227, c_4])).
% 2.60/1.36  tff(c_236, plain, (![B_58]: (k5_relat_1(k1_xboole_0, B_58)=k1_xboole_0 | ~v1_relat_1(B_58) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_36, c_232])).
% 2.60/1.36  tff(c_240, plain, (![B_121]: (k5_relat_1(k1_xboole_0, B_121)=k1_xboole_0 | ~v1_relat_1(B_121))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_236])).
% 2.60/1.36  tff(c_252, plain, (k5_relat_1(k1_xboole_0, '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_240])).
% 2.60/1.36  tff(c_259, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_252])).
% 2.60/1.36  tff(c_260, plain, (k5_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 2.60/1.36  tff(c_297, plain, (![A_131, B_132, C_133]: (~r1_xboole_0(A_131, B_132) | ~r2_hidden(C_133, k3_xboole_0(A_131, B_132)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.60/1.36  tff(c_304, plain, (![A_7, C_133]: (~r1_xboole_0(A_7, k1_xboole_0) | ~r2_hidden(C_133, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_297])).
% 2.60/1.36  tff(c_308, plain, (![C_134]: (~r2_hidden(C_134, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_304])).
% 2.60/1.36  tff(c_313, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_308])).
% 2.60/1.36  tff(c_392, plain, (![B_166, A_167]: (k2_relat_1(k5_relat_1(B_166, A_167))=k2_relat_1(A_167) | ~r1_tarski(k1_relat_1(A_167), k2_relat_1(B_166)) | ~v1_relat_1(B_166) | ~v1_relat_1(A_167))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.60/1.36  tff(c_395, plain, (![B_166]: (k2_relat_1(k5_relat_1(B_166, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_166)) | ~v1_relat_1(B_166) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_48, c_392])).
% 2.60/1.36  tff(c_414, plain, (![B_170]: (k2_relat_1(k5_relat_1(B_170, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_170))), inference(demodulation, [status(thm), theory('equality')], [c_313, c_12, c_46, c_395])).
% 2.60/1.36  tff(c_40, plain, (![A_60]: (~v1_xboole_0(k2_relat_1(A_60)) | ~v1_relat_1(A_60) | v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.60/1.36  tff(c_426, plain, (![B_170]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_170, k1_xboole_0)) | v1_xboole_0(k5_relat_1(B_170, k1_xboole_0)) | ~v1_relat_1(B_170))), inference(superposition, [status(thm), theory('equality')], [c_414, c_40])).
% 2.60/1.36  tff(c_463, plain, (![B_172]: (~v1_relat_1(k5_relat_1(B_172, k1_xboole_0)) | v1_xboole_0(k5_relat_1(B_172, k1_xboole_0)) | ~v1_relat_1(B_172))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_426])).
% 2.60/1.36  tff(c_487, plain, (![B_181]: (k5_relat_1(B_181, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_181, k1_xboole_0)) | ~v1_relat_1(B_181))), inference(resolution, [status(thm)], [c_463, c_4])).
% 2.60/1.36  tff(c_491, plain, (![A_57]: (k5_relat_1(A_57, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_57))), inference(resolution, [status(thm)], [c_36, c_487])).
% 2.60/1.36  tff(c_495, plain, (![A_182]: (k5_relat_1(A_182, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_182))), inference(demodulation, [status(thm), theory('equality')], [c_313, c_491])).
% 2.60/1.36  tff(c_507, plain, (k5_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_495])).
% 2.60/1.36  tff(c_514, plain, $false, inference(negUnitSimplification, [status(thm)], [c_260, c_507])).
% 2.60/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.36  
% 2.60/1.36  Inference rules
% 2.60/1.36  ----------------------
% 2.60/1.36  #Ref     : 2
% 2.60/1.36  #Sup     : 95
% 2.60/1.36  #Fact    : 0
% 2.60/1.36  #Define  : 0
% 2.60/1.36  #Split   : 1
% 2.60/1.36  #Chain   : 0
% 2.60/1.36  #Close   : 0
% 2.60/1.36  
% 2.60/1.36  Ordering : KBO
% 2.60/1.36  
% 2.60/1.36  Simplification rules
% 2.60/1.36  ----------------------
% 2.60/1.36  #Subsume      : 2
% 2.60/1.36  #Demod        : 44
% 2.60/1.36  #Tautology    : 60
% 2.60/1.36  #SimpNegUnit  : 4
% 2.60/1.36  #BackRed      : 0
% 2.60/1.36  
% 2.60/1.36  #Partial instantiations: 0
% 2.60/1.36  #Strategies tried      : 1
% 2.60/1.36  
% 2.60/1.36  Timing (in seconds)
% 2.60/1.36  ----------------------
% 2.60/1.37  Preprocessing        : 0.36
% 2.60/1.37  Parsing              : 0.19
% 2.60/1.37  CNF conversion       : 0.03
% 2.60/1.37  Main loop            : 0.31
% 2.60/1.37  Inferencing          : 0.14
% 2.60/1.37  Reduction            : 0.08
% 2.60/1.37  Demodulation         : 0.06
% 2.60/1.37  BG Simplification    : 0.02
% 2.60/1.37  Subsumption          : 0.04
% 2.60/1.37  Abstraction          : 0.02
% 2.60/1.37  MUC search           : 0.00
% 2.60/1.37  Cooper               : 0.00
% 2.60/1.37  Total                : 0.71
% 2.60/1.37  Index Insertion      : 0.00
% 2.60/1.37  Index Deletion       : 0.00
% 2.60/1.37  Index Matching       : 0.00
% 2.60/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
