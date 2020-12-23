%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:31 EST 2020

% Result     : Theorem 8.51s
% Output     : CNFRefutation 8.62s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 317 expanded)
%              Number of leaves         :   57 ( 132 expanded)
%              Depth                    :   19
%              Number of atoms          :  183 ( 491 expanded)
%              Number of equality atoms :   31 ( 144 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_tarski > r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_11 > #skF_6 > #skF_2 > #skF_15 > #skF_13 > #skF_16 > #skF_12 > #skF_8 > #skF_14 > #skF_3 > #skF_7 > #skF_1 > #skF_9 > #skF_4 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(r2_tarski,type,(
    r2_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_13',type,(
    '#skF_13': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_16',type,(
    '#skF_16': $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_14',type,(
    '#skF_14': ( $i * $i * $i ) > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_194,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_170,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_76,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_158,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_148,axiom,(
    ! [A] :
    ? [B] :
      ( r2_hidden(A,B)
      & ! [C,D] :
          ( ( r2_hidden(C,B)
            & r1_tarski(D,C) )
         => r2_hidden(D,B) )
      & ! [C] :
          ~ ( r2_hidden(C,B)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & ! [E] :
                      ( r1_tarski(E,C)
                     => r2_hidden(E,D) ) ) )
      & ! [C] :
          ~ ( r1_tarski(C,B)
            & ~ r2_tarski(C,B)
            & ~ r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tarski)).

tff(f_166,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(f_88,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_98,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_102,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_90,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_78,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_150,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_177,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k1_relat_1(A),k1_relat_1(B)),k1_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_184,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k2_relat_1(A),k2_relat_1(B)),k2_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relat_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_96,plain,(
    v1_relat_1('#skF_15') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_94,plain,(
    v1_relat_1('#skF_16') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_84,plain,(
    ! [A_125] :
      ( k2_xboole_0(k1_relat_1(A_125),k2_relat_1(A_125)) = k3_relat_1(A_125)
      | ~ v1_relat_1(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_24,plain,(
    ! [A_17] : r1_tarski(k1_xboole_0,A_17) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1758,plain,(
    ! [C_277,A_278] :
      ( r2_hidden(k4_tarski(C_277,'#skF_10'(A_278,k1_relat_1(A_278),C_277)),A_278)
      | ~ r2_hidden(C_277,k1_relat_1(A_278)) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_52,plain,(
    ! [A_44] : r2_hidden(A_44,'#skF_5'(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_393,plain,(
    ! [C_185,A_186,D_187] :
      ( r2_hidden(C_185,k2_relat_1(A_186))
      | ~ r2_hidden(k4_tarski(D_187,C_185),A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_403,plain,(
    ! [C_185,D_187] : r2_hidden(C_185,k2_relat_1('#skF_5'(k4_tarski(D_187,C_185)))) ),
    inference(resolution,[status(thm)],[c_52,c_393])).

tff(c_46,plain,(
    ! [A_37,B_38] :
      ( r2_hidden('#skF_4'(A_37,B_38),B_38)
      | ~ r2_hidden(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_32,plain,(
    ! [A_25] : r1_xboole_0(A_25,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_345,plain,(
    ! [A_176,B_177,C_178] :
      ( ~ r1_xboole_0(A_176,B_177)
      | ~ r2_hidden(C_178,B_177)
      | ~ r2_hidden(C_178,A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_349,plain,(
    ! [C_179,A_180] :
      ( ~ r2_hidden(C_179,k1_xboole_0)
      | ~ r2_hidden(C_179,A_180) ) ),
    inference(resolution,[status(thm)],[c_32,c_345])).

tff(c_465,plain,(
    ! [A_196,A_197] :
      ( ~ r2_hidden('#skF_4'(A_196,k1_xboole_0),A_197)
      | ~ r2_hidden(A_196,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_46,c_349])).

tff(c_479,plain,(
    ! [A_196] : ~ r2_hidden(A_196,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_403,c_465])).

tff(c_1781,plain,(
    ! [C_279] : ~ r2_hidden(C_279,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_1758,c_479])).

tff(c_1811,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_1781])).

tff(c_92,plain,(
    r1_tarski('#skF_15','#skF_16') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_38,plain,(
    ! [B_32,A_31] : k2_tarski(B_32,A_31) = k2_tarski(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_157,plain,(
    ! [A_145,B_146] : k3_tarski(k2_tarski(A_145,B_146)) = k2_xboole_0(A_145,B_146) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_215,plain,(
    ! [B_155,A_156] : k3_tarski(k2_tarski(B_155,A_156)) = k2_xboole_0(A_156,B_155) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_157])).

tff(c_42,plain,(
    ! [A_35,B_36] : k3_tarski(k2_tarski(A_35,B_36)) = k2_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_238,plain,(
    ! [B_157,A_158] : k2_xboole_0(B_157,A_158) = k2_xboole_0(A_158,B_157) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_42])).

tff(c_34,plain,(
    ! [A_26,B_27] : r1_tarski(A_26,k2_xboole_0(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_259,plain,(
    ! [A_158,B_157] : r1_tarski(A_158,k2_xboole_0(B_157,A_158)) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_34])).

tff(c_14,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_26,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_507,plain,(
    ! [A_199,B_200,C_201] :
      ( r1_tarski(k4_xboole_0(A_199,B_200),C_201)
      | ~ r1_tarski(A_199,k2_xboole_0(B_200,C_201)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_523,plain,(
    ! [A_202,C_203] :
      ( r1_tarski(A_202,C_203)
      | ~ r1_tarski(A_202,k2_xboole_0(k1_xboole_0,C_203)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_507])).

tff(c_576,plain,(
    ! [C_204] : r1_tarski(k2_xboole_0(k1_xboole_0,C_204),C_204) ),
    inference(resolution,[status(thm)],[c_14,c_523])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( B_9 = A_8
      | ~ r1_tarski(B_9,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_586,plain,(
    ! [C_204] :
      ( k2_xboole_0(k1_xboole_0,C_204) = C_204
      | ~ r1_tarski(C_204,k2_xboole_0(k1_xboole_0,C_204)) ) ),
    inference(resolution,[status(thm)],[c_576,c_10])).

tff(c_630,plain,(
    ! [C_207] : k2_xboole_0(k1_xboole_0,C_207) = C_207 ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_586])).

tff(c_221,plain,(
    ! [B_155,A_156] : k2_xboole_0(B_155,A_156) = k2_xboole_0(A_156,B_155) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_42])).

tff(c_646,plain,(
    ! [C_207] : k2_xboole_0(C_207,k1_xboole_0) = C_207 ),
    inference(superposition,[status(thm),theory(equality)],[c_630,c_221])).

tff(c_28,plain,(
    ! [A_19,B_20,C_21] :
      ( r1_tarski(k4_xboole_0(A_19,B_20),C_21)
      | ~ r1_tarski(A_19,k2_xboole_0(B_20,C_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_16,plain,(
    ! [A_10,C_12,B_11] :
      ( r1_tarski(A_10,k2_xboole_0(C_12,B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_256,plain,(
    ! [A_10,A_158,B_157] :
      ( r1_tarski(A_10,k2_xboole_0(A_158,B_157))
      | ~ r1_tarski(A_10,A_158) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_16])).

tff(c_749,plain,(
    ! [A_212,C_213] :
      ( r1_tarski(A_212,C_213)
      | ~ r1_tarski(A_212,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_630,c_256])).

tff(c_752,plain,(
    ! [A_19,B_20,C_213] :
      ( r1_tarski(k4_xboole_0(A_19,B_20),C_213)
      | ~ r1_tarski(A_19,k2_xboole_0(B_20,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_28,c_749])).

tff(c_936,plain,(
    ! [A_234,B_235,C_236] :
      ( r1_tarski(k4_xboole_0(A_234,B_235),C_236)
      | ~ r1_tarski(A_234,B_235) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_646,c_752])).

tff(c_181,plain,(
    ! [B_149,A_150] :
      ( B_149 = A_150
      | ~ r1_tarski(B_149,A_150)
      | ~ r1_tarski(A_150,B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_196,plain,(
    ! [A_17] :
      ( k1_xboole_0 = A_17
      | ~ r1_tarski(A_17,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_181])).

tff(c_959,plain,(
    ! [A_237,B_238] :
      ( k4_xboole_0(A_237,B_238) = k1_xboole_0
      | ~ r1_tarski(A_237,B_238) ) ),
    inference(resolution,[status(thm)],[c_936,c_196])).

tff(c_1009,plain,(
    k4_xboole_0('#skF_15','#skF_16') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_92,c_959])).

tff(c_58,plain,(
    ! [A_85,B_86] : k6_subset_1(A_85,B_86) = k4_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_86,plain,(
    ! [A_126,B_128] :
      ( r1_tarski(k6_subset_1(k1_relat_1(A_126),k1_relat_1(B_128)),k1_relat_1(k6_subset_1(A_126,B_128)))
      | ~ v1_relat_1(B_128)
      | ~ v1_relat_1(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_2072,plain,(
    ! [A_289,B_290] :
      ( r1_tarski(k4_xboole_0(k1_relat_1(A_289),k1_relat_1(B_290)),k1_relat_1(k4_xboole_0(A_289,B_290)))
      | ~ v1_relat_1(B_290)
      | ~ v1_relat_1(A_289) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_58,c_86])).

tff(c_2116,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1('#skF_15'),k1_relat_1('#skF_16')),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_16')
    | ~ v1_relat_1('#skF_15') ),
    inference(superposition,[status(thm),theory(equality)],[c_1009,c_2072])).

tff(c_2137,plain,(
    r1_tarski(k4_xboole_0(k1_relat_1('#skF_15'),k1_relat_1('#skF_16')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_1811,c_2116])).

tff(c_2161,plain,(
    k4_xboole_0(k1_relat_1('#skF_15'),k1_relat_1('#skF_16')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2137,c_196])).

tff(c_30,plain,(
    ! [A_22,B_23,C_24] :
      ( r1_tarski(A_22,k2_xboole_0(B_23,C_24))
      | ~ r1_tarski(k4_xboole_0(A_22,B_23),C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2198,plain,(
    ! [C_24] :
      ( r1_tarski(k1_relat_1('#skF_15'),k2_xboole_0(k1_relat_1('#skF_16'),C_24))
      | ~ r1_tarski(k1_xboole_0,C_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2161,c_30])).

tff(c_2215,plain,(
    ! [C_291] : r1_tarski(k1_relat_1('#skF_15'),k2_xboole_0(k1_relat_1('#skF_16'),C_291)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2198])).

tff(c_2230,plain,
    ( r1_tarski(k1_relat_1('#skF_15'),k3_relat_1('#skF_16'))
    | ~ v1_relat_1('#skF_16') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_2215])).

tff(c_2244,plain,(
    r1_tarski(k1_relat_1('#skF_15'),k3_relat_1('#skF_16')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_2230])).

tff(c_1512,plain,(
    ! [A_260,C_261] :
      ( r2_hidden(k4_tarski('#skF_14'(A_260,k2_relat_1(A_260),C_261),C_261),A_260)
      | ~ r2_hidden(C_261,k2_relat_1(A_260)) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1535,plain,(
    ! [C_262] : ~ r2_hidden(C_262,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_1512,c_479])).

tff(c_1560,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_1535])).

tff(c_88,plain,(
    ! [A_129,B_131] :
      ( r1_tarski(k6_subset_1(k2_relat_1(A_129),k2_relat_1(B_131)),k2_relat_1(k6_subset_1(A_129,B_131)))
      | ~ v1_relat_1(B_131)
      | ~ v1_relat_1(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_1873,plain,(
    ! [A_284,B_285] :
      ( r1_tarski(k4_xboole_0(k2_relat_1(A_284),k2_relat_1(B_285)),k2_relat_1(k4_xboole_0(A_284,B_285)))
      | ~ v1_relat_1(B_285)
      | ~ v1_relat_1(A_284) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_58,c_88])).

tff(c_1914,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1('#skF_15'),k2_relat_1('#skF_16')),k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_16')
    | ~ v1_relat_1('#skF_15') ),
    inference(superposition,[status(thm),theory(equality)],[c_1009,c_1873])).

tff(c_1934,plain,(
    r1_tarski(k4_xboole_0(k2_relat_1('#skF_15'),k2_relat_1('#skF_16')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_1560,c_1914])).

tff(c_1958,plain,(
    k4_xboole_0(k2_relat_1('#skF_15'),k2_relat_1('#skF_16')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1934,c_196])).

tff(c_1992,plain,(
    ! [C_24] :
      ( r1_tarski(k2_relat_1('#skF_15'),k2_xboole_0(k2_relat_1('#skF_16'),C_24))
      | ~ r1_tarski(k1_xboole_0,C_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1958,c_30])).

tff(c_2008,plain,(
    ! [C_286] : r1_tarski(k2_relat_1('#skF_15'),k2_xboole_0(k2_relat_1('#skF_16'),C_286)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1992])).

tff(c_2366,plain,(
    ! [B_298] : r1_tarski(k2_relat_1('#skF_15'),k2_xboole_0(B_298,k2_relat_1('#skF_16'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_2008])).

tff(c_2381,plain,
    ( r1_tarski(k2_relat_1('#skF_15'),k3_relat_1('#skF_16'))
    | ~ v1_relat_1('#skF_16') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_2366])).

tff(c_2395,plain,(
    r1_tarski(k2_relat_1('#skF_15'),k3_relat_1('#skF_16')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_2381])).

tff(c_765,plain,(
    ! [A_214,C_215,B_216] :
      ( r1_tarski(k2_xboole_0(A_214,C_215),B_216)
      | ~ r1_tarski(C_215,B_216)
      | ~ r1_tarski(A_214,B_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_15640,plain,(
    ! [A_499,B_500] :
      ( r1_tarski(k3_relat_1(A_499),B_500)
      | ~ r1_tarski(k2_relat_1(A_499),B_500)
      | ~ r1_tarski(k1_relat_1(A_499),B_500)
      | ~ v1_relat_1(A_499) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_765])).

tff(c_90,plain,(
    ~ r1_tarski(k3_relat_1('#skF_15'),k3_relat_1('#skF_16')) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_15698,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_15'),k3_relat_1('#skF_16'))
    | ~ r1_tarski(k1_relat_1('#skF_15'),k3_relat_1('#skF_16'))
    | ~ v1_relat_1('#skF_15') ),
    inference(resolution,[status(thm)],[c_15640,c_90])).

tff(c_15721,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_2244,c_2395,c_15698])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:57:55 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.51/3.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.62/3.20  
% 8.62/3.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.62/3.20  %$ r2_tarski > r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_11 > #skF_6 > #skF_2 > #skF_15 > #skF_13 > #skF_16 > #skF_12 > #skF_8 > #skF_14 > #skF_3 > #skF_7 > #skF_1 > #skF_9 > #skF_4 > #skF_10
% 8.62/3.20  
% 8.62/3.20  %Foreground sorts:
% 8.62/3.20  
% 8.62/3.20  
% 8.62/3.20  %Background operators:
% 8.62/3.20  
% 8.62/3.20  
% 8.62/3.20  %Foreground operators:
% 8.62/3.20  tff('#skF_5', type, '#skF_5': $i > $i).
% 8.62/3.20  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 8.62/3.20  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 8.62/3.20  tff(r2_tarski, type, r2_tarski: ($i * $i) > $o).
% 8.62/3.20  tff('#skF_2', type, '#skF_2': $i > $i).
% 8.62/3.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.62/3.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.62/3.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.62/3.20  tff('#skF_15', type, '#skF_15': $i).
% 8.62/3.20  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.62/3.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.62/3.20  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 8.62/3.20  tff('#skF_13', type, '#skF_13': ($i * $i) > $i).
% 8.62/3.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.62/3.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.62/3.20  tff('#skF_16', type, '#skF_16': $i).
% 8.62/3.20  tff('#skF_12', type, '#skF_12': ($i * $i) > $i).
% 8.62/3.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.62/3.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.62/3.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.62/3.20  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 8.62/3.20  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 8.62/3.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.62/3.20  tff('#skF_14', type, '#skF_14': ($i * $i * $i) > $i).
% 8.62/3.20  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.62/3.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.62/3.20  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.62/3.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.62/3.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.62/3.20  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 8.62/3.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.62/3.20  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 8.62/3.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.62/3.20  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.62/3.20  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 8.62/3.20  
% 8.62/3.22  tff(f_194, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 8.62/3.22  tff(f_170, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 8.62/3.22  tff(f_76, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.62/3.22  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 8.62/3.22  tff(f_158, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 8.62/3.22  tff(f_148, axiom, (![A]: (?[B]: (((r2_hidden(A, B) & (![C, D]: ((r2_hidden(C, B) & r1_tarski(D, C)) => r2_hidden(D, B)))) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & (![E]: (r1_tarski(E, C) => r2_hidden(E, D)))))))) & (![C]: ~((r1_tarski(C, B) & ~r2_tarski(C, B)) & ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_tarski)).
% 8.62/3.22  tff(f_166, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 8.62/3.22  tff(f_115, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 8.62/3.22  tff(f_88, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 8.62/3.22  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 8.62/3.22  tff(f_98, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.62/3.22  tff(f_102, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 8.62/3.22  tff(f_90, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 8.62/3.22  tff(f_57, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.62/3.22  tff(f_78, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 8.62/3.22  tff(f_82, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 8.62/3.22  tff(f_61, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 8.62/3.22  tff(f_150, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 8.62/3.22  tff(f_177, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k1_relat_1(A), k1_relat_1(B)), k1_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_relat_1)).
% 8.62/3.22  tff(f_86, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 8.62/3.22  tff(f_184, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k2_relat_1(A), k2_relat_1(B)), k2_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_relat_1)).
% 8.62/3.22  tff(f_96, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 8.62/3.22  tff(c_96, plain, (v1_relat_1('#skF_15')), inference(cnfTransformation, [status(thm)], [f_194])).
% 8.62/3.22  tff(c_94, plain, (v1_relat_1('#skF_16')), inference(cnfTransformation, [status(thm)], [f_194])).
% 8.62/3.22  tff(c_84, plain, (![A_125]: (k2_xboole_0(k1_relat_1(A_125), k2_relat_1(A_125))=k3_relat_1(A_125) | ~v1_relat_1(A_125))), inference(cnfTransformation, [status(thm)], [f_170])).
% 8.62/3.22  tff(c_24, plain, (![A_17]: (r1_tarski(k1_xboole_0, A_17))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.62/3.22  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.62/3.22  tff(c_1758, plain, (![C_277, A_278]: (r2_hidden(k4_tarski(C_277, '#skF_10'(A_278, k1_relat_1(A_278), C_277)), A_278) | ~r2_hidden(C_277, k1_relat_1(A_278)))), inference(cnfTransformation, [status(thm)], [f_158])).
% 8.62/3.22  tff(c_52, plain, (![A_44]: (r2_hidden(A_44, '#skF_5'(A_44)))), inference(cnfTransformation, [status(thm)], [f_148])).
% 8.62/3.22  tff(c_393, plain, (![C_185, A_186, D_187]: (r2_hidden(C_185, k2_relat_1(A_186)) | ~r2_hidden(k4_tarski(D_187, C_185), A_186))), inference(cnfTransformation, [status(thm)], [f_166])).
% 8.62/3.22  tff(c_403, plain, (![C_185, D_187]: (r2_hidden(C_185, k2_relat_1('#skF_5'(k4_tarski(D_187, C_185)))))), inference(resolution, [status(thm)], [c_52, c_393])).
% 8.62/3.22  tff(c_46, plain, (![A_37, B_38]: (r2_hidden('#skF_4'(A_37, B_38), B_38) | ~r2_hidden(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.62/3.22  tff(c_32, plain, (![A_25]: (r1_xboole_0(A_25, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.62/3.22  tff(c_345, plain, (![A_176, B_177, C_178]: (~r1_xboole_0(A_176, B_177) | ~r2_hidden(C_178, B_177) | ~r2_hidden(C_178, A_176))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.62/3.22  tff(c_349, plain, (![C_179, A_180]: (~r2_hidden(C_179, k1_xboole_0) | ~r2_hidden(C_179, A_180))), inference(resolution, [status(thm)], [c_32, c_345])).
% 8.62/3.22  tff(c_465, plain, (![A_196, A_197]: (~r2_hidden('#skF_4'(A_196, k1_xboole_0), A_197) | ~r2_hidden(A_196, k1_xboole_0))), inference(resolution, [status(thm)], [c_46, c_349])).
% 8.62/3.22  tff(c_479, plain, (![A_196]: (~r2_hidden(A_196, k1_xboole_0))), inference(resolution, [status(thm)], [c_403, c_465])).
% 8.62/3.22  tff(c_1781, plain, (![C_279]: (~r2_hidden(C_279, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_1758, c_479])).
% 8.62/3.22  tff(c_1811, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_1781])).
% 8.62/3.22  tff(c_92, plain, (r1_tarski('#skF_15', '#skF_16')), inference(cnfTransformation, [status(thm)], [f_194])).
% 8.62/3.22  tff(c_38, plain, (![B_32, A_31]: (k2_tarski(B_32, A_31)=k2_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.62/3.22  tff(c_157, plain, (![A_145, B_146]: (k3_tarski(k2_tarski(A_145, B_146))=k2_xboole_0(A_145, B_146))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.62/3.22  tff(c_215, plain, (![B_155, A_156]: (k3_tarski(k2_tarski(B_155, A_156))=k2_xboole_0(A_156, B_155))), inference(superposition, [status(thm), theory('equality')], [c_38, c_157])).
% 8.62/3.22  tff(c_42, plain, (![A_35, B_36]: (k3_tarski(k2_tarski(A_35, B_36))=k2_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.62/3.22  tff(c_238, plain, (![B_157, A_158]: (k2_xboole_0(B_157, A_158)=k2_xboole_0(A_158, B_157))), inference(superposition, [status(thm), theory('equality')], [c_215, c_42])).
% 8.62/3.22  tff(c_34, plain, (![A_26, B_27]: (r1_tarski(A_26, k2_xboole_0(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.62/3.22  tff(c_259, plain, (![A_158, B_157]: (r1_tarski(A_158, k2_xboole_0(B_157, A_158)))), inference(superposition, [status(thm), theory('equality')], [c_238, c_34])).
% 8.62/3.22  tff(c_14, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.62/3.22  tff(c_26, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.62/3.22  tff(c_507, plain, (![A_199, B_200, C_201]: (r1_tarski(k4_xboole_0(A_199, B_200), C_201) | ~r1_tarski(A_199, k2_xboole_0(B_200, C_201)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.62/3.22  tff(c_523, plain, (![A_202, C_203]: (r1_tarski(A_202, C_203) | ~r1_tarski(A_202, k2_xboole_0(k1_xboole_0, C_203)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_507])).
% 8.62/3.22  tff(c_576, plain, (![C_204]: (r1_tarski(k2_xboole_0(k1_xboole_0, C_204), C_204))), inference(resolution, [status(thm)], [c_14, c_523])).
% 8.62/3.22  tff(c_10, plain, (![B_9, A_8]: (B_9=A_8 | ~r1_tarski(B_9, A_8) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.62/3.22  tff(c_586, plain, (![C_204]: (k2_xboole_0(k1_xboole_0, C_204)=C_204 | ~r1_tarski(C_204, k2_xboole_0(k1_xboole_0, C_204)))), inference(resolution, [status(thm)], [c_576, c_10])).
% 8.62/3.22  tff(c_630, plain, (![C_207]: (k2_xboole_0(k1_xboole_0, C_207)=C_207)), inference(demodulation, [status(thm), theory('equality')], [c_259, c_586])).
% 8.62/3.22  tff(c_221, plain, (![B_155, A_156]: (k2_xboole_0(B_155, A_156)=k2_xboole_0(A_156, B_155))), inference(superposition, [status(thm), theory('equality')], [c_215, c_42])).
% 8.62/3.22  tff(c_646, plain, (![C_207]: (k2_xboole_0(C_207, k1_xboole_0)=C_207)), inference(superposition, [status(thm), theory('equality')], [c_630, c_221])).
% 8.62/3.22  tff(c_28, plain, (![A_19, B_20, C_21]: (r1_tarski(k4_xboole_0(A_19, B_20), C_21) | ~r1_tarski(A_19, k2_xboole_0(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.62/3.22  tff(c_16, plain, (![A_10, C_12, B_11]: (r1_tarski(A_10, k2_xboole_0(C_12, B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.62/3.22  tff(c_256, plain, (![A_10, A_158, B_157]: (r1_tarski(A_10, k2_xboole_0(A_158, B_157)) | ~r1_tarski(A_10, A_158))), inference(superposition, [status(thm), theory('equality')], [c_238, c_16])).
% 8.62/3.22  tff(c_749, plain, (![A_212, C_213]: (r1_tarski(A_212, C_213) | ~r1_tarski(A_212, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_630, c_256])).
% 8.62/3.22  tff(c_752, plain, (![A_19, B_20, C_213]: (r1_tarski(k4_xboole_0(A_19, B_20), C_213) | ~r1_tarski(A_19, k2_xboole_0(B_20, k1_xboole_0)))), inference(resolution, [status(thm)], [c_28, c_749])).
% 8.62/3.22  tff(c_936, plain, (![A_234, B_235, C_236]: (r1_tarski(k4_xboole_0(A_234, B_235), C_236) | ~r1_tarski(A_234, B_235))), inference(demodulation, [status(thm), theory('equality')], [c_646, c_752])).
% 8.62/3.22  tff(c_181, plain, (![B_149, A_150]: (B_149=A_150 | ~r1_tarski(B_149, A_150) | ~r1_tarski(A_150, B_149))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.62/3.22  tff(c_196, plain, (![A_17]: (k1_xboole_0=A_17 | ~r1_tarski(A_17, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_181])).
% 8.62/3.22  tff(c_959, plain, (![A_237, B_238]: (k4_xboole_0(A_237, B_238)=k1_xboole_0 | ~r1_tarski(A_237, B_238))), inference(resolution, [status(thm)], [c_936, c_196])).
% 8.62/3.22  tff(c_1009, plain, (k4_xboole_0('#skF_15', '#skF_16')=k1_xboole_0), inference(resolution, [status(thm)], [c_92, c_959])).
% 8.62/3.22  tff(c_58, plain, (![A_85, B_86]: (k6_subset_1(A_85, B_86)=k4_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_150])).
% 8.62/3.22  tff(c_86, plain, (![A_126, B_128]: (r1_tarski(k6_subset_1(k1_relat_1(A_126), k1_relat_1(B_128)), k1_relat_1(k6_subset_1(A_126, B_128))) | ~v1_relat_1(B_128) | ~v1_relat_1(A_126))), inference(cnfTransformation, [status(thm)], [f_177])).
% 8.62/3.22  tff(c_2072, plain, (![A_289, B_290]: (r1_tarski(k4_xboole_0(k1_relat_1(A_289), k1_relat_1(B_290)), k1_relat_1(k4_xboole_0(A_289, B_290))) | ~v1_relat_1(B_290) | ~v1_relat_1(A_289))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_58, c_86])).
% 8.62/3.22  tff(c_2116, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_15'), k1_relat_1('#skF_16')), k1_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_16') | ~v1_relat_1('#skF_15')), inference(superposition, [status(thm), theory('equality')], [c_1009, c_2072])).
% 8.62/3.22  tff(c_2137, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_15'), k1_relat_1('#skF_16')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_1811, c_2116])).
% 8.62/3.22  tff(c_2161, plain, (k4_xboole_0(k1_relat_1('#skF_15'), k1_relat_1('#skF_16'))=k1_xboole_0), inference(resolution, [status(thm)], [c_2137, c_196])).
% 8.62/3.22  tff(c_30, plain, (![A_22, B_23, C_24]: (r1_tarski(A_22, k2_xboole_0(B_23, C_24)) | ~r1_tarski(k4_xboole_0(A_22, B_23), C_24))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.62/3.22  tff(c_2198, plain, (![C_24]: (r1_tarski(k1_relat_1('#skF_15'), k2_xboole_0(k1_relat_1('#skF_16'), C_24)) | ~r1_tarski(k1_xboole_0, C_24))), inference(superposition, [status(thm), theory('equality')], [c_2161, c_30])).
% 8.62/3.22  tff(c_2215, plain, (![C_291]: (r1_tarski(k1_relat_1('#skF_15'), k2_xboole_0(k1_relat_1('#skF_16'), C_291)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2198])).
% 8.62/3.22  tff(c_2230, plain, (r1_tarski(k1_relat_1('#skF_15'), k3_relat_1('#skF_16')) | ~v1_relat_1('#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_84, c_2215])).
% 8.62/3.22  tff(c_2244, plain, (r1_tarski(k1_relat_1('#skF_15'), k3_relat_1('#skF_16'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_2230])).
% 8.62/3.22  tff(c_1512, plain, (![A_260, C_261]: (r2_hidden(k4_tarski('#skF_14'(A_260, k2_relat_1(A_260), C_261), C_261), A_260) | ~r2_hidden(C_261, k2_relat_1(A_260)))), inference(cnfTransformation, [status(thm)], [f_166])).
% 8.62/3.22  tff(c_1535, plain, (![C_262]: (~r2_hidden(C_262, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_1512, c_479])).
% 8.62/3.22  tff(c_1560, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_1535])).
% 8.62/3.22  tff(c_88, plain, (![A_129, B_131]: (r1_tarski(k6_subset_1(k2_relat_1(A_129), k2_relat_1(B_131)), k2_relat_1(k6_subset_1(A_129, B_131))) | ~v1_relat_1(B_131) | ~v1_relat_1(A_129))), inference(cnfTransformation, [status(thm)], [f_184])).
% 8.62/3.22  tff(c_1873, plain, (![A_284, B_285]: (r1_tarski(k4_xboole_0(k2_relat_1(A_284), k2_relat_1(B_285)), k2_relat_1(k4_xboole_0(A_284, B_285))) | ~v1_relat_1(B_285) | ~v1_relat_1(A_284))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_58, c_88])).
% 8.62/3.22  tff(c_1914, plain, (r1_tarski(k4_xboole_0(k2_relat_1('#skF_15'), k2_relat_1('#skF_16')), k2_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_16') | ~v1_relat_1('#skF_15')), inference(superposition, [status(thm), theory('equality')], [c_1009, c_1873])).
% 8.62/3.22  tff(c_1934, plain, (r1_tarski(k4_xboole_0(k2_relat_1('#skF_15'), k2_relat_1('#skF_16')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_1560, c_1914])).
% 8.62/3.22  tff(c_1958, plain, (k4_xboole_0(k2_relat_1('#skF_15'), k2_relat_1('#skF_16'))=k1_xboole_0), inference(resolution, [status(thm)], [c_1934, c_196])).
% 8.62/3.22  tff(c_1992, plain, (![C_24]: (r1_tarski(k2_relat_1('#skF_15'), k2_xboole_0(k2_relat_1('#skF_16'), C_24)) | ~r1_tarski(k1_xboole_0, C_24))), inference(superposition, [status(thm), theory('equality')], [c_1958, c_30])).
% 8.62/3.22  tff(c_2008, plain, (![C_286]: (r1_tarski(k2_relat_1('#skF_15'), k2_xboole_0(k2_relat_1('#skF_16'), C_286)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1992])).
% 8.62/3.22  tff(c_2366, plain, (![B_298]: (r1_tarski(k2_relat_1('#skF_15'), k2_xboole_0(B_298, k2_relat_1('#skF_16'))))), inference(superposition, [status(thm), theory('equality')], [c_221, c_2008])).
% 8.62/3.22  tff(c_2381, plain, (r1_tarski(k2_relat_1('#skF_15'), k3_relat_1('#skF_16')) | ~v1_relat_1('#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_84, c_2366])).
% 8.62/3.22  tff(c_2395, plain, (r1_tarski(k2_relat_1('#skF_15'), k3_relat_1('#skF_16'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_2381])).
% 8.62/3.22  tff(c_765, plain, (![A_214, C_215, B_216]: (r1_tarski(k2_xboole_0(A_214, C_215), B_216) | ~r1_tarski(C_215, B_216) | ~r1_tarski(A_214, B_216))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.62/3.22  tff(c_15640, plain, (![A_499, B_500]: (r1_tarski(k3_relat_1(A_499), B_500) | ~r1_tarski(k2_relat_1(A_499), B_500) | ~r1_tarski(k1_relat_1(A_499), B_500) | ~v1_relat_1(A_499))), inference(superposition, [status(thm), theory('equality')], [c_84, c_765])).
% 8.62/3.22  tff(c_90, plain, (~r1_tarski(k3_relat_1('#skF_15'), k3_relat_1('#skF_16'))), inference(cnfTransformation, [status(thm)], [f_194])).
% 8.62/3.22  tff(c_15698, plain, (~r1_tarski(k2_relat_1('#skF_15'), k3_relat_1('#skF_16')) | ~r1_tarski(k1_relat_1('#skF_15'), k3_relat_1('#skF_16')) | ~v1_relat_1('#skF_15')), inference(resolution, [status(thm)], [c_15640, c_90])).
% 8.62/3.22  tff(c_15721, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_2244, c_2395, c_15698])).
% 8.62/3.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.62/3.22  
% 8.62/3.22  Inference rules
% 8.62/3.22  ----------------------
% 8.62/3.22  #Ref     : 0
% 8.62/3.22  #Sup     : 3790
% 8.62/3.22  #Fact    : 0
% 8.62/3.22  #Define  : 0
% 8.62/3.22  #Split   : 3
% 8.62/3.22  #Chain   : 0
% 8.62/3.22  #Close   : 0
% 8.62/3.22  
% 8.62/3.22  Ordering : KBO
% 8.62/3.22  
% 8.62/3.22  Simplification rules
% 8.62/3.22  ----------------------
% 8.62/3.22  #Subsume      : 422
% 8.62/3.22  #Demod        : 3334
% 8.62/3.22  #Tautology    : 2152
% 8.62/3.22  #SimpNegUnit  : 8
% 8.62/3.22  #BackRed      : 5
% 8.62/3.22  
% 8.62/3.22  #Partial instantiations: 0
% 8.62/3.22  #Strategies tried      : 1
% 8.62/3.22  
% 8.62/3.22  Timing (in seconds)
% 8.62/3.22  ----------------------
% 8.62/3.22  Preprocessing        : 0.36
% 8.62/3.22  Parsing              : 0.19
% 8.62/3.22  CNF conversion       : 0.03
% 8.62/3.22  Main loop            : 2.08
% 8.62/3.22  Inferencing          : 0.48
% 8.62/3.22  Reduction            : 0.99
% 8.62/3.22  Demodulation         : 0.83
% 8.62/3.22  BG Simplification    : 0.05
% 8.62/3.22  Subsumption          : 0.44
% 8.62/3.22  Abstraction          : 0.07
% 8.62/3.22  MUC search           : 0.00
% 8.62/3.22  Cooper               : 0.00
% 8.62/3.22  Total                : 2.48
% 8.62/3.22  Index Insertion      : 0.00
% 8.62/3.23  Index Deletion       : 0.00
% 8.62/3.23  Index Matching       : 0.00
% 8.62/3.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
