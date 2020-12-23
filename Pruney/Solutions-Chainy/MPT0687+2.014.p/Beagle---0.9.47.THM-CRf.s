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
% DateTime   : Thu Dec  3 10:04:35 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   75 (  89 expanded)
%              Number of leaves         :   36 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :   87 ( 120 expanded)
%              Number of equality atoms :   29 (  40 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_40,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_42,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C,D,E,F,G,H] : ~ v1_xboole_0(k6_enumset1(A,B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_subset_1)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(c_8,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_10,plain,(
    ! [A_6,B_7] : k1_enumset1(A_6,A_6,B_7) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] : k2_enumset1(A_8,A_8,B_9,C_10) = k1_enumset1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13,D_14] : k3_enumset1(A_11,A_11,B_12,C_13,D_14) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_16,plain,(
    ! [B_16,A_15,D_18,E_19,C_17] : k4_enumset1(A_15,A_15,B_16,C_17,D_18,E_19) = k3_enumset1(A_15,B_16,C_17,D_18,E_19) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_18,plain,(
    ! [C_22,D_23,A_20,B_21,F_25,E_24] : k5_enumset1(A_20,A_20,B_21,C_22,D_23,E_24,F_25) = k4_enumset1(A_20,B_21,C_22,D_23,E_24,F_25) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_268,plain,(
    ! [E_140,F_138,B_136,A_137,C_139,D_135,G_141] : k6_enumset1(A_137,A_137,B_136,C_139,D_135,E_140,F_138,G_141) = k5_enumset1(A_137,B_136,C_139,D_135,E_140,F_138,G_141) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_28,plain,(
    ! [C_39,B_38,A_37,D_40,F_42,G_43,E_41,H_44] : ~ v1_xboole_0(k6_enumset1(A_37,B_38,C_39,D_40,E_41,F_42,G_43,H_44)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_279,plain,(
    ! [G_144,B_143,F_142,D_145,A_148,E_147,C_146] : ~ v1_xboole_0(k5_enumset1(A_148,B_143,C_146,D_145,E_147,F_142,G_144)) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_28])).

tff(c_282,plain,(
    ! [B_150,E_152,F_154,D_151,A_153,C_149] : ~ v1_xboole_0(k4_enumset1(A_153,B_150,C_149,D_151,E_152,F_154)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_279])).

tff(c_285,plain,(
    ! [A_159,C_155,D_156,B_157,E_158] : ~ v1_xboole_0(k3_enumset1(A_159,B_157,C_155,D_156,E_158)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_282])).

tff(c_288,plain,(
    ! [A_160,B_161,C_162,D_163] : ~ v1_xboole_0(k2_enumset1(A_160,B_161,C_162,D_163)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_285])).

tff(c_291,plain,(
    ! [A_164,B_165,C_166] : ~ v1_xboole_0(k1_enumset1(A_164,B_165,C_166)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_288])).

tff(c_294,plain,(
    ! [A_167,B_168] : ~ v1_xboole_0(k2_tarski(A_167,B_168)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_291])).

tff(c_296,plain,(
    ! [A_5] : ~ v1_xboole_0(k1_tarski(A_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_294])).

tff(c_34,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_42,plain,
    ( r2_hidden('#skF_1',k2_relat_1('#skF_2'))
    | k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_80,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_72,plain,(
    ! [A_56,B_57] :
      ( r1_xboole_0(k1_tarski(A_56),B_57)
      | r2_hidden(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_75,plain,(
    ! [B_57,A_56] :
      ( r1_xboole_0(B_57,k1_tarski(A_56))
      | r2_hidden(A_56,B_57) ) ),
    inference(resolution,[status(thm)],[c_72,c_4])).

tff(c_106,plain,(
    ! [B_67,A_68] :
      ( k10_relat_1(B_67,A_68) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_67),A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_147,plain,(
    ! [B_85,A_86] :
      ( k10_relat_1(B_85,k1_tarski(A_86)) = k1_xboole_0
      | ~ v1_relat_1(B_85)
      | r2_hidden(A_86,k2_relat_1(B_85)) ) ),
    inference(resolution,[status(thm)],[c_75,c_106])).

tff(c_36,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_99,plain,(
    ~ r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_36])).

tff(c_150,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_147,c_99])).

tff(c_153,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_150])).

tff(c_155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_153])).

tff(c_157,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_156,plain,(
    r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_24,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(k1_tarski(A_33),B_34)
      | ~ r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_188,plain,(
    ! [B_94,A_95] :
      ( r1_xboole_0(k2_relat_1(B_94),A_95)
      | k10_relat_1(B_94,A_95) != k1_xboole_0
      | ~ v1_relat_1(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_207,plain,(
    ! [A_106,B_107] :
      ( r1_xboole_0(A_106,k2_relat_1(B_107))
      | k10_relat_1(B_107,A_106) != k1_xboole_0
      | ~ v1_relat_1(B_107) ) ),
    inference(resolution,[status(thm)],[c_188,c_4])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( ~ r1_xboole_0(B_4,A_3)
      | ~ r1_tarski(B_4,A_3)
      | v1_xboole_0(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_231,plain,(
    ! [A_116,B_117] :
      ( ~ r1_tarski(A_116,k2_relat_1(B_117))
      | v1_xboole_0(A_116)
      | k10_relat_1(B_117,A_116) != k1_xboole_0
      | ~ v1_relat_1(B_117) ) ),
    inference(resolution,[status(thm)],[c_207,c_6])).

tff(c_248,plain,(
    ! [A_127,B_128] :
      ( v1_xboole_0(k1_tarski(A_127))
      | k10_relat_1(B_128,k1_tarski(A_127)) != k1_xboole_0
      | ~ v1_relat_1(B_128)
      | ~ r2_hidden(A_127,k2_relat_1(B_128)) ) ),
    inference(resolution,[status(thm)],[c_24,c_231])).

tff(c_254,plain,
    ( v1_xboole_0(k1_tarski('#skF_1'))
    | k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_156,c_248])).

tff(c_258,plain,(
    v1_xboole_0(k1_tarski('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_157,c_254])).

tff(c_300,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_296,c_258])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:43:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.27  
% 2.27/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.28  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_1
% 2.27/1.28  
% 2.27/1.28  %Foreground sorts:
% 2.27/1.28  
% 2.27/1.28  
% 2.27/1.28  %Background operators:
% 2.27/1.28  
% 2.27/1.28  
% 2.27/1.28  %Foreground operators:
% 2.27/1.28  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 2.27/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.27/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.27/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.27/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.27/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.27/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.27/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.27/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.27/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.27/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.27/1.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.27/1.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.27/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.28  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.27/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.27/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.27/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.27/1.28  
% 2.27/1.29  tff(f_40, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.27/1.29  tff(f_42, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.27/1.29  tff(f_44, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.27/1.29  tff(f_46, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.27/1.29  tff(f_48, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.27/1.29  tff(f_50, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 2.27/1.29  tff(f_52, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 2.27/1.29  tff(f_64, axiom, (![A, B, C, D, E, F, G, H]: ~v1_xboole_0(k6_enumset1(A, B, C, D, E, F, G, H))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_subset_1)).
% 2.27/1.29  tff(f_78, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 2.27/1.29  tff(f_61, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.27/1.29  tff(f_30, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.27/1.29  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 2.27/1.29  tff(f_56, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.27/1.29  tff(f_38, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.27/1.29  tff(c_8, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.27/1.29  tff(c_10, plain, (![A_6, B_7]: (k1_enumset1(A_6, A_6, B_7)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.27/1.29  tff(c_12, plain, (![A_8, B_9, C_10]: (k2_enumset1(A_8, A_8, B_9, C_10)=k1_enumset1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.27/1.29  tff(c_14, plain, (![A_11, B_12, C_13, D_14]: (k3_enumset1(A_11, A_11, B_12, C_13, D_14)=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.27/1.29  tff(c_16, plain, (![B_16, A_15, D_18, E_19, C_17]: (k4_enumset1(A_15, A_15, B_16, C_17, D_18, E_19)=k3_enumset1(A_15, B_16, C_17, D_18, E_19))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.27/1.29  tff(c_18, plain, (![C_22, D_23, A_20, B_21, F_25, E_24]: (k5_enumset1(A_20, A_20, B_21, C_22, D_23, E_24, F_25)=k4_enumset1(A_20, B_21, C_22, D_23, E_24, F_25))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.27/1.29  tff(c_268, plain, (![E_140, F_138, B_136, A_137, C_139, D_135, G_141]: (k6_enumset1(A_137, A_137, B_136, C_139, D_135, E_140, F_138, G_141)=k5_enumset1(A_137, B_136, C_139, D_135, E_140, F_138, G_141))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.27/1.29  tff(c_28, plain, (![C_39, B_38, A_37, D_40, F_42, G_43, E_41, H_44]: (~v1_xboole_0(k6_enumset1(A_37, B_38, C_39, D_40, E_41, F_42, G_43, H_44)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.27/1.29  tff(c_279, plain, (![G_144, B_143, F_142, D_145, A_148, E_147, C_146]: (~v1_xboole_0(k5_enumset1(A_148, B_143, C_146, D_145, E_147, F_142, G_144)))), inference(superposition, [status(thm), theory('equality')], [c_268, c_28])).
% 2.27/1.29  tff(c_282, plain, (![B_150, E_152, F_154, D_151, A_153, C_149]: (~v1_xboole_0(k4_enumset1(A_153, B_150, C_149, D_151, E_152, F_154)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_279])).
% 2.27/1.29  tff(c_285, plain, (![A_159, C_155, D_156, B_157, E_158]: (~v1_xboole_0(k3_enumset1(A_159, B_157, C_155, D_156, E_158)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_282])).
% 2.27/1.29  tff(c_288, plain, (![A_160, B_161, C_162, D_163]: (~v1_xboole_0(k2_enumset1(A_160, B_161, C_162, D_163)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_285])).
% 2.27/1.29  tff(c_291, plain, (![A_164, B_165, C_166]: (~v1_xboole_0(k1_enumset1(A_164, B_165, C_166)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_288])).
% 2.27/1.29  tff(c_294, plain, (![A_167, B_168]: (~v1_xboole_0(k2_tarski(A_167, B_168)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_291])).
% 2.27/1.29  tff(c_296, plain, (![A_5]: (~v1_xboole_0(k1_tarski(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_294])).
% 2.27/1.29  tff(c_34, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.27/1.29  tff(c_42, plain, (r2_hidden('#skF_1', k2_relat_1('#skF_2')) | k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.27/1.29  tff(c_80, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_42])).
% 2.27/1.29  tff(c_72, plain, (![A_56, B_57]: (r1_xboole_0(k1_tarski(A_56), B_57) | r2_hidden(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.27/1.29  tff(c_4, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.27/1.29  tff(c_75, plain, (![B_57, A_56]: (r1_xboole_0(B_57, k1_tarski(A_56)) | r2_hidden(A_56, B_57))), inference(resolution, [status(thm)], [c_72, c_4])).
% 2.27/1.29  tff(c_106, plain, (![B_67, A_68]: (k10_relat_1(B_67, A_68)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_67), A_68) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.27/1.29  tff(c_147, plain, (![B_85, A_86]: (k10_relat_1(B_85, k1_tarski(A_86))=k1_xboole_0 | ~v1_relat_1(B_85) | r2_hidden(A_86, k2_relat_1(B_85)))), inference(resolution, [status(thm)], [c_75, c_106])).
% 2.27/1.29  tff(c_36, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.27/1.29  tff(c_99, plain, (~r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_80, c_36])).
% 2.27/1.29  tff(c_150, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_147, c_99])).
% 2.27/1.29  tff(c_153, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_150])).
% 2.27/1.29  tff(c_155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_153])).
% 2.27/1.29  tff(c_157, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 2.27/1.29  tff(c_156, plain, (r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_42])).
% 2.27/1.29  tff(c_24, plain, (![A_33, B_34]: (r1_tarski(k1_tarski(A_33), B_34) | ~r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.27/1.29  tff(c_188, plain, (![B_94, A_95]: (r1_xboole_0(k2_relat_1(B_94), A_95) | k10_relat_1(B_94, A_95)!=k1_xboole_0 | ~v1_relat_1(B_94))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.27/1.29  tff(c_207, plain, (![A_106, B_107]: (r1_xboole_0(A_106, k2_relat_1(B_107)) | k10_relat_1(B_107, A_106)!=k1_xboole_0 | ~v1_relat_1(B_107))), inference(resolution, [status(thm)], [c_188, c_4])).
% 2.27/1.29  tff(c_6, plain, (![B_4, A_3]: (~r1_xboole_0(B_4, A_3) | ~r1_tarski(B_4, A_3) | v1_xboole_0(B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.27/1.29  tff(c_231, plain, (![A_116, B_117]: (~r1_tarski(A_116, k2_relat_1(B_117)) | v1_xboole_0(A_116) | k10_relat_1(B_117, A_116)!=k1_xboole_0 | ~v1_relat_1(B_117))), inference(resolution, [status(thm)], [c_207, c_6])).
% 2.27/1.29  tff(c_248, plain, (![A_127, B_128]: (v1_xboole_0(k1_tarski(A_127)) | k10_relat_1(B_128, k1_tarski(A_127))!=k1_xboole_0 | ~v1_relat_1(B_128) | ~r2_hidden(A_127, k2_relat_1(B_128)))), inference(resolution, [status(thm)], [c_24, c_231])).
% 2.27/1.29  tff(c_254, plain, (v1_xboole_0(k1_tarski('#skF_1')) | k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_156, c_248])).
% 2.27/1.29  tff(c_258, plain, (v1_xboole_0(k1_tarski('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_157, c_254])).
% 2.27/1.29  tff(c_300, plain, $false, inference(negUnitSimplification, [status(thm)], [c_296, c_258])).
% 2.27/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.29  
% 2.27/1.29  Inference rules
% 2.27/1.29  ----------------------
% 2.27/1.29  #Ref     : 0
% 2.27/1.29  #Sup     : 56
% 2.27/1.29  #Fact    : 0
% 2.27/1.29  #Define  : 0
% 2.27/1.29  #Split   : 1
% 2.27/1.29  #Chain   : 0
% 2.27/1.29  #Close   : 0
% 2.27/1.29  
% 2.27/1.29  Ordering : KBO
% 2.27/1.29  
% 2.27/1.29  Simplification rules
% 2.27/1.29  ----------------------
% 2.27/1.29  #Subsume      : 5
% 2.27/1.29  #Demod        : 5
% 2.27/1.29  #Tautology    : 29
% 2.27/1.29  #SimpNegUnit  : 5
% 2.27/1.29  #BackRed      : 3
% 2.27/1.29  
% 2.27/1.29  #Partial instantiations: 0
% 2.27/1.29  #Strategies tried      : 1
% 2.27/1.29  
% 2.27/1.29  Timing (in seconds)
% 2.27/1.29  ----------------------
% 2.27/1.30  Preprocessing        : 0.30
% 2.27/1.30  Parsing              : 0.16
% 2.27/1.30  CNF conversion       : 0.02
% 2.27/1.30  Main loop            : 0.21
% 2.27/1.30  Inferencing          : 0.09
% 2.27/1.30  Reduction            : 0.05
% 2.27/1.30  Demodulation         : 0.03
% 2.27/1.30  BG Simplification    : 0.01
% 2.27/1.30  Subsumption          : 0.03
% 2.27/1.30  Abstraction          : 0.01
% 2.27/1.30  MUC search           : 0.00
% 2.27/1.30  Cooper               : 0.00
% 2.27/1.30  Total                : 0.54
% 2.27/1.30  Index Insertion      : 0.00
% 2.27/1.30  Index Deletion       : 0.00
% 2.27/1.30  Index Matching       : 0.00
% 2.27/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
