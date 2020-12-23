%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:17 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 111 expanded)
%              Number of leaves         :   39 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :  129 ( 181 expanded)
%              Number of equality atoms :   47 (  67 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_28,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_30,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_32,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C,D,E,F] : ~ v1_xboole_0(k4_enumset1(A,B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_52,plain,
    ( r2_hidden('#skF_1',k1_relat_1('#skF_2'))
    | k11_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_79,plain,(
    k11_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_18,plain,(
    ! [A_29,B_30] :
      ( r1_xboole_0(k1_tarski(A_29),B_30)
      | r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_104,plain,(
    ! [A_80,B_81] :
      ( k7_relat_1(A_80,B_81) = k1_xboole_0
      | ~ r1_xboole_0(B_81,k1_relat_1(A_80))
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_243,plain,(
    ! [A_131,A_132] :
      ( k7_relat_1(A_131,k1_tarski(A_132)) = k1_xboole_0
      | ~ v1_relat_1(A_131)
      | r2_hidden(A_132,k1_relat_1(A_131)) ) ),
    inference(resolution,[status(thm)],[c_18,c_104])).

tff(c_46,plain,
    ( k11_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_84,plain,(
    ~ r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_46])).

tff(c_246,plain,
    ( k7_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_243,c_84])).

tff(c_249,plain,(
    k7_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_246])).

tff(c_42,plain,(
    ! [B_52,A_51] :
      ( r1_xboole_0(k1_relat_1(B_52),A_51)
      | k7_relat_1(B_52,A_51) != k1_xboole_0
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_130,plain,(
    ! [B_86,A_87] :
      ( k9_relat_1(B_86,A_87) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_86),A_87)
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_142,plain,(
    ! [B_90,A_91] :
      ( k9_relat_1(B_90,A_91) = k1_xboole_0
      | k7_relat_1(B_90,A_91) != k1_xboole_0
      | ~ v1_relat_1(B_90) ) ),
    inference(resolution,[status(thm)],[c_42,c_130])).

tff(c_146,plain,(
    ! [A_92] :
      ( k9_relat_1('#skF_2',A_92) = k1_xboole_0
      | k7_relat_1('#skF_2',A_92) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_44,c_142])).

tff(c_28,plain,(
    ! [A_40,B_42] :
      ( k9_relat_1(A_40,k1_tarski(B_42)) = k11_relat_1(A_40,B_42)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_155,plain,(
    ! [B_42] :
      ( k11_relat_1('#skF_2',B_42) = k1_xboole_0
      | ~ v1_relat_1('#skF_2')
      | k7_relat_1('#skF_2',k1_tarski(B_42)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_28])).

tff(c_168,plain,(
    ! [B_42] :
      ( k11_relat_1('#skF_2',B_42) = k1_xboole_0
      | k7_relat_1('#skF_2',k1_tarski(B_42)) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_155])).

tff(c_253,plain,(
    k11_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_168])).

tff(c_259,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_253])).

tff(c_260,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_263,plain,(
    k11_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_46])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_313,plain,(
    ! [B_149,A_150] :
      ( r1_xboole_0(k1_relat_1(B_149),A_150)
      | k9_relat_1(B_149,A_150) != k1_xboole_0
      | ~ v1_relat_1(B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_40,plain,(
    ! [B_52,A_51] :
      ( k7_relat_1(B_52,A_51) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_52),A_51)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_362,plain,(
    ! [B_159,A_160] :
      ( k7_relat_1(B_159,A_160) = k1_xboole_0
      | k9_relat_1(B_159,A_160) != k1_xboole_0
      | ~ v1_relat_1(B_159) ) ),
    inference(resolution,[status(thm)],[c_313,c_40])).

tff(c_366,plain,(
    ! [A_40,B_42] :
      ( k7_relat_1(A_40,k1_tarski(B_42)) = k1_xboole_0
      | k11_relat_1(A_40,B_42) != k1_xboole_0
      | ~ v1_relat_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_362])).

tff(c_4,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_6,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_8,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9,D_10] : k3_enumset1(A_7,A_7,B_8,C_9,D_10) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_399,plain,(
    ! [D_173,B_172,C_170,E_174,A_171] : k4_enumset1(A_171,A_171,B_172,C_170,D_173,E_174) = k3_enumset1(A_171,B_172,C_170,D_173,E_174) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_26,plain,(
    ! [D_37,A_34,F_39,B_35,C_36,E_38] : ~ v1_xboole_0(k4_enumset1(A_34,B_35,C_36,D_37,E_38,F_39)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_410,plain,(
    ! [A_178,C_177,D_176,B_179,E_175] : ~ v1_xboole_0(k3_enumset1(A_178,B_179,C_177,D_176,E_175)) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_26])).

tff(c_413,plain,(
    ! [A_180,B_181,C_182,D_183] : ~ v1_xboole_0(k2_enumset1(A_180,B_181,C_182,D_183)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_410])).

tff(c_416,plain,(
    ! [A_184,B_185,C_186] : ~ v1_xboole_0(k1_enumset1(A_184,B_185,C_186)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_413])).

tff(c_419,plain,(
    ! [A_187,B_188] : ~ v1_xboole_0(k2_tarski(A_187,B_188)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_416])).

tff(c_421,plain,(
    ! [A_1] : ~ v1_xboole_0(k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_419])).

tff(c_371,plain,(
    ! [A_163,B_164,C_165] :
      ( r1_tarski(k2_tarski(A_163,B_164),C_165)
      | ~ r2_hidden(B_164,C_165)
      | ~ r2_hidden(A_163,C_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_388,plain,(
    ! [A_166,C_167] :
      ( r1_tarski(k1_tarski(A_166),C_167)
      | ~ r2_hidden(A_166,C_167)
      | ~ r2_hidden(A_166,C_167) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_371])).

tff(c_38,plain,(
    ! [B_50,A_49] :
      ( k1_relat_1(k7_relat_1(B_50,A_49)) = A_49
      | ~ r1_tarski(A_49,k1_relat_1(B_50))
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_448,plain,(
    ! [B_198,A_199] :
      ( k1_relat_1(k7_relat_1(B_198,k1_tarski(A_199))) = k1_tarski(A_199)
      | ~ v1_relat_1(B_198)
      | ~ r2_hidden(A_199,k1_relat_1(B_198)) ) ),
    inference(resolution,[status(thm)],[c_388,c_38])).

tff(c_30,plain,(
    ! [A_43] :
      ( v1_xboole_0(k1_relat_1(A_43))
      | ~ v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_475,plain,(
    ! [A_199,B_198] :
      ( v1_xboole_0(k1_tarski(A_199))
      | ~ v1_xboole_0(k7_relat_1(B_198,k1_tarski(A_199)))
      | ~ v1_relat_1(B_198)
      | ~ r2_hidden(A_199,k1_relat_1(B_198)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_448,c_30])).

tff(c_485,plain,(
    ! [B_200,A_201] :
      ( ~ v1_xboole_0(k7_relat_1(B_200,k1_tarski(A_201)))
      | ~ v1_relat_1(B_200)
      | ~ r2_hidden(A_201,k1_relat_1(B_200)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_421,c_475])).

tff(c_488,plain,(
    ! [A_40,B_42] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(A_40)
      | ~ r2_hidden(B_42,k1_relat_1(A_40))
      | k11_relat_1(A_40,B_42) != k1_xboole_0
      | ~ v1_relat_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_366,c_485])).

tff(c_500,plain,(
    ! [B_209,A_210] :
      ( ~ r2_hidden(B_209,k1_relat_1(A_210))
      | k11_relat_1(A_210,B_209) != k1_xboole_0
      | ~ v1_relat_1(A_210) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_488])).

tff(c_509,plain,
    ( k11_relat_1('#skF_2','#skF_1') != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_260,c_500])).

tff(c_514,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_263,c_509])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:28:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.34  
% 2.34/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.34  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.34/1.34  
% 2.34/1.34  %Foreground sorts:
% 2.34/1.34  
% 2.34/1.34  
% 2.34/1.34  %Background operators:
% 2.34/1.34  
% 2.34/1.34  
% 2.34/1.34  %Foreground operators:
% 2.34/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.34/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.34/1.34  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.34/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.34/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.34/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.34/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.34/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.34/1.34  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.34/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.34/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.34/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.34/1.34  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.34/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.34/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.34/1.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.34/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.34/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.34/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.34/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.34/1.34  
% 2.66/1.36  tff(f_96, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 2.66/1.36  tff(f_45, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.66/1.36  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 2.66/1.36  tff(f_88, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 2.66/1.36  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 2.66/1.36  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 2.66/1.36  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.66/1.36  tff(f_28, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.66/1.36  tff(f_30, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.66/1.36  tff(f_32, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.66/1.36  tff(f_34, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.66/1.36  tff(f_36, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.66/1.36  tff(f_54, axiom, (![A, B, C, D, E, F]: ~v1_xboole_0(k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_subset_1)).
% 2.66/1.36  tff(f_51, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.66/1.36  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 2.66/1.36  tff(f_63, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 2.66/1.36  tff(c_44, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.66/1.36  tff(c_52, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_2')) | k11_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.66/1.36  tff(c_79, plain, (k11_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_52])).
% 2.66/1.36  tff(c_18, plain, (![A_29, B_30]: (r1_xboole_0(k1_tarski(A_29), B_30) | r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.66/1.36  tff(c_104, plain, (![A_80, B_81]: (k7_relat_1(A_80, B_81)=k1_xboole_0 | ~r1_xboole_0(B_81, k1_relat_1(A_80)) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.66/1.36  tff(c_243, plain, (![A_131, A_132]: (k7_relat_1(A_131, k1_tarski(A_132))=k1_xboole_0 | ~v1_relat_1(A_131) | r2_hidden(A_132, k1_relat_1(A_131)))), inference(resolution, [status(thm)], [c_18, c_104])).
% 2.66/1.36  tff(c_46, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.66/1.36  tff(c_84, plain, (~r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_79, c_46])).
% 2.66/1.36  tff(c_246, plain, (k7_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_243, c_84])).
% 2.66/1.36  tff(c_249, plain, (k7_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_246])).
% 2.66/1.36  tff(c_42, plain, (![B_52, A_51]: (r1_xboole_0(k1_relat_1(B_52), A_51) | k7_relat_1(B_52, A_51)!=k1_xboole_0 | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.66/1.36  tff(c_130, plain, (![B_86, A_87]: (k9_relat_1(B_86, A_87)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_86), A_87) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.66/1.36  tff(c_142, plain, (![B_90, A_91]: (k9_relat_1(B_90, A_91)=k1_xboole_0 | k7_relat_1(B_90, A_91)!=k1_xboole_0 | ~v1_relat_1(B_90))), inference(resolution, [status(thm)], [c_42, c_130])).
% 2.66/1.36  tff(c_146, plain, (![A_92]: (k9_relat_1('#skF_2', A_92)=k1_xboole_0 | k7_relat_1('#skF_2', A_92)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_142])).
% 2.66/1.36  tff(c_28, plain, (![A_40, B_42]: (k9_relat_1(A_40, k1_tarski(B_42))=k11_relat_1(A_40, B_42) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.66/1.36  tff(c_155, plain, (![B_42]: (k11_relat_1('#skF_2', B_42)=k1_xboole_0 | ~v1_relat_1('#skF_2') | k7_relat_1('#skF_2', k1_tarski(B_42))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_146, c_28])).
% 2.66/1.36  tff(c_168, plain, (![B_42]: (k11_relat_1('#skF_2', B_42)=k1_xboole_0 | k7_relat_1('#skF_2', k1_tarski(B_42))!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_155])).
% 2.66/1.36  tff(c_253, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_249, c_168])).
% 2.66/1.36  tff(c_259, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_253])).
% 2.66/1.36  tff(c_260, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_52])).
% 2.66/1.36  tff(c_263, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_260, c_46])).
% 2.66/1.36  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.66/1.36  tff(c_313, plain, (![B_149, A_150]: (r1_xboole_0(k1_relat_1(B_149), A_150) | k9_relat_1(B_149, A_150)!=k1_xboole_0 | ~v1_relat_1(B_149))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.66/1.36  tff(c_40, plain, (![B_52, A_51]: (k7_relat_1(B_52, A_51)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_52), A_51) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.66/1.36  tff(c_362, plain, (![B_159, A_160]: (k7_relat_1(B_159, A_160)=k1_xboole_0 | k9_relat_1(B_159, A_160)!=k1_xboole_0 | ~v1_relat_1(B_159))), inference(resolution, [status(thm)], [c_313, c_40])).
% 2.66/1.36  tff(c_366, plain, (![A_40, B_42]: (k7_relat_1(A_40, k1_tarski(B_42))=k1_xboole_0 | k11_relat_1(A_40, B_42)!=k1_xboole_0 | ~v1_relat_1(A_40) | ~v1_relat_1(A_40))), inference(superposition, [status(thm), theory('equality')], [c_28, c_362])).
% 2.66/1.36  tff(c_4, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.66/1.36  tff(c_6, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.66/1.36  tff(c_8, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.66/1.36  tff(c_10, plain, (![A_7, B_8, C_9, D_10]: (k3_enumset1(A_7, A_7, B_8, C_9, D_10)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.66/1.36  tff(c_399, plain, (![D_173, B_172, C_170, E_174, A_171]: (k4_enumset1(A_171, A_171, B_172, C_170, D_173, E_174)=k3_enumset1(A_171, B_172, C_170, D_173, E_174))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.66/1.36  tff(c_26, plain, (![D_37, A_34, F_39, B_35, C_36, E_38]: (~v1_xboole_0(k4_enumset1(A_34, B_35, C_36, D_37, E_38, F_39)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.66/1.36  tff(c_410, plain, (![A_178, C_177, D_176, B_179, E_175]: (~v1_xboole_0(k3_enumset1(A_178, B_179, C_177, D_176, E_175)))), inference(superposition, [status(thm), theory('equality')], [c_399, c_26])).
% 2.66/1.36  tff(c_413, plain, (![A_180, B_181, C_182, D_183]: (~v1_xboole_0(k2_enumset1(A_180, B_181, C_182, D_183)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_410])).
% 2.66/1.36  tff(c_416, plain, (![A_184, B_185, C_186]: (~v1_xboole_0(k1_enumset1(A_184, B_185, C_186)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_413])).
% 2.66/1.36  tff(c_419, plain, (![A_187, B_188]: (~v1_xboole_0(k2_tarski(A_187, B_188)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_416])).
% 2.66/1.36  tff(c_421, plain, (![A_1]: (~v1_xboole_0(k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_419])).
% 2.66/1.36  tff(c_371, plain, (![A_163, B_164, C_165]: (r1_tarski(k2_tarski(A_163, B_164), C_165) | ~r2_hidden(B_164, C_165) | ~r2_hidden(A_163, C_165))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.66/1.36  tff(c_388, plain, (![A_166, C_167]: (r1_tarski(k1_tarski(A_166), C_167) | ~r2_hidden(A_166, C_167) | ~r2_hidden(A_166, C_167))), inference(superposition, [status(thm), theory('equality')], [c_4, c_371])).
% 2.66/1.36  tff(c_38, plain, (![B_50, A_49]: (k1_relat_1(k7_relat_1(B_50, A_49))=A_49 | ~r1_tarski(A_49, k1_relat_1(B_50)) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.66/1.36  tff(c_448, plain, (![B_198, A_199]: (k1_relat_1(k7_relat_1(B_198, k1_tarski(A_199)))=k1_tarski(A_199) | ~v1_relat_1(B_198) | ~r2_hidden(A_199, k1_relat_1(B_198)))), inference(resolution, [status(thm)], [c_388, c_38])).
% 2.66/1.36  tff(c_30, plain, (![A_43]: (v1_xboole_0(k1_relat_1(A_43)) | ~v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.66/1.36  tff(c_475, plain, (![A_199, B_198]: (v1_xboole_0(k1_tarski(A_199)) | ~v1_xboole_0(k7_relat_1(B_198, k1_tarski(A_199))) | ~v1_relat_1(B_198) | ~r2_hidden(A_199, k1_relat_1(B_198)))), inference(superposition, [status(thm), theory('equality')], [c_448, c_30])).
% 2.66/1.36  tff(c_485, plain, (![B_200, A_201]: (~v1_xboole_0(k7_relat_1(B_200, k1_tarski(A_201))) | ~v1_relat_1(B_200) | ~r2_hidden(A_201, k1_relat_1(B_200)))), inference(negUnitSimplification, [status(thm)], [c_421, c_475])).
% 2.66/1.36  tff(c_488, plain, (![A_40, B_42]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(A_40) | ~r2_hidden(B_42, k1_relat_1(A_40)) | k11_relat_1(A_40, B_42)!=k1_xboole_0 | ~v1_relat_1(A_40) | ~v1_relat_1(A_40))), inference(superposition, [status(thm), theory('equality')], [c_366, c_485])).
% 2.66/1.36  tff(c_500, plain, (![B_209, A_210]: (~r2_hidden(B_209, k1_relat_1(A_210)) | k11_relat_1(A_210, B_209)!=k1_xboole_0 | ~v1_relat_1(A_210))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_488])).
% 2.66/1.36  tff(c_509, plain, (k11_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_260, c_500])).
% 2.66/1.36  tff(c_514, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_263, c_509])).
% 2.66/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.36  
% 2.66/1.36  Inference rules
% 2.66/1.36  ----------------------
% 2.66/1.36  #Ref     : 0
% 2.66/1.36  #Sup     : 103
% 2.66/1.36  #Fact    : 0
% 2.66/1.36  #Define  : 0
% 2.66/1.36  #Split   : 1
% 2.66/1.36  #Chain   : 0
% 2.66/1.36  #Close   : 0
% 2.66/1.36  
% 2.66/1.36  Ordering : KBO
% 2.66/1.36  
% 2.66/1.36  Simplification rules
% 2.66/1.36  ----------------------
% 2.66/1.36  #Subsume      : 5
% 2.66/1.36  #Demod        : 13
% 2.66/1.36  #Tautology    : 53
% 2.66/1.36  #SimpNegUnit  : 3
% 2.66/1.36  #BackRed      : 0
% 2.66/1.36  
% 2.66/1.36  #Partial instantiations: 0
% 2.66/1.36  #Strategies tried      : 1
% 2.66/1.36  
% 2.66/1.36  Timing (in seconds)
% 2.66/1.36  ----------------------
% 2.66/1.36  Preprocessing        : 0.33
% 2.66/1.36  Parsing              : 0.18
% 2.66/1.36  CNF conversion       : 0.02
% 2.66/1.36  Main loop            : 0.26
% 2.66/1.36  Inferencing          : 0.12
% 2.66/1.36  Reduction            : 0.07
% 2.66/1.36  Demodulation         : 0.04
% 2.66/1.36  BG Simplification    : 0.02
% 2.66/1.36  Subsumption          : 0.04
% 2.66/1.36  Abstraction          : 0.02
% 2.66/1.36  MUC search           : 0.00
% 2.66/1.36  Cooper               : 0.00
% 2.66/1.36  Total                : 0.62
% 2.66/1.36  Index Insertion      : 0.00
% 2.66/1.36  Index Deletion       : 0.00
% 2.66/1.36  Index Matching       : 0.00
% 2.66/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
