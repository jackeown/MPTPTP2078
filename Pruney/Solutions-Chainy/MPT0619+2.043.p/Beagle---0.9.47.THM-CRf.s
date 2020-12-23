%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:57 EST 2020

% Result     : Theorem 11.75s
% Output     : CNFRefutation 11.88s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 299 expanded)
%              Number of leaves         :   39 ( 121 expanded)
%              Depth                    :   25
%              Number of atoms          :  209 ( 741 expanded)
%              Number of equality atoms :  115 ( 411 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_10 > #skF_9 > #skF_3 > #skF_2 > #skF_8 > #skF_7 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_109,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).

tff(f_100,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_34,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_36,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_38,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_79,axiom,(
    ! [A,B,C,D,E,F] :
      ( F = k3_enumset1(A,B,C,D,E)
    <=> ! [G] :
          ( r2_hidden(G,F)
        <=> ~ ( G != A
              & G != B
              & G != C
              & G != D
              & G != E ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_88,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_117,plain,(
    ! [A_85] :
      ( k2_relat_1(A_85) = k1_xboole_0
      | k1_relat_1(A_85) != k1_xboole_0
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_121,plain,
    ( k2_relat_1('#skF_10') = k1_xboole_0
    | k1_relat_1('#skF_10') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_88,c_117])).

tff(c_122,plain,(
    k1_relat_1('#skF_10') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_123,plain,(
    ! [A_86] :
      ( k1_relat_1(A_86) = k1_xboole_0
      | k2_relat_1(A_86) != k1_xboole_0
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_126,plain,
    ( k1_relat_1('#skF_10') = k1_xboole_0
    | k2_relat_1('#skF_10') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_88,c_123])).

tff(c_129,plain,(
    k2_relat_1('#skF_10') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_126])).

tff(c_22,plain,(
    ! [A_26,B_27] :
      ( r2_hidden('#skF_2'(A_26,B_27),A_26)
      | k1_xboole_0 = A_26
      | k1_tarski(B_27) = A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_86,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_68,plain,(
    ! [A_39,C_75] :
      ( r2_hidden('#skF_8'(A_39,k2_relat_1(A_39),C_75),k1_relat_1(A_39))
      | ~ r2_hidden(C_75,k2_relat_1(A_39))
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_64,plain,(
    ! [A_39,D_78] :
      ( r2_hidden(k1_funct_1(A_39,D_78),k2_relat_1(A_39))
      | ~ r2_hidden(D_78,k1_relat_1(A_39))
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_413,plain,(
    ! [A_199,B_200] :
      ( r2_hidden('#skF_6'(A_199,B_200),k1_relat_1(A_199))
      | r2_hidden('#skF_7'(A_199,B_200),B_200)
      | k2_relat_1(A_199) = B_200
      | ~ v1_funct_1(A_199)
      | ~ v1_relat_1(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_435,plain,(
    ! [B_200,A_199] :
      ( ~ v1_xboole_0(B_200)
      | r2_hidden('#skF_6'(A_199,B_200),k1_relat_1(A_199))
      | k2_relat_1(A_199) = B_200
      | ~ v1_funct_1(A_199)
      | ~ v1_relat_1(A_199) ) ),
    inference(resolution,[status(thm)],[c_413,c_2])).

tff(c_84,plain,(
    k1_tarski('#skF_9') = k1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_8,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [A_6,B_7] : k1_enumset1(A_6,A_6,B_7) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] : k2_enumset1(A_8,A_8,B_9,C_10) = k1_enumset1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13,D_14] : k3_enumset1(A_11,A_11,B_12,C_13,D_14) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_451,plain,(
    ! [B_204,E_206,D_203,A_205,C_207,G_208] :
      ( G_208 = E_206
      | G_208 = D_203
      | G_208 = C_207
      | G_208 = B_204
      | G_208 = A_205
      | ~ r2_hidden(G_208,k3_enumset1(A_205,B_204,C_207,D_203,E_206)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_600,plain,(
    ! [D_228,G_225,B_227,C_224,A_226] :
      ( G_225 = D_228
      | G_225 = C_224
      | G_225 = B_227
      | G_225 = A_226
      | G_225 = A_226
      | ~ r2_hidden(G_225,k2_enumset1(A_226,B_227,C_224,D_228)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_451])).

tff(c_662,plain,(
    ! [G_232,C_233,B_234,A_235] :
      ( G_232 = C_233
      | G_232 = B_234
      | G_232 = A_235
      | G_232 = A_235
      | G_232 = A_235
      | ~ r2_hidden(G_232,k1_enumset1(A_235,B_234,C_233)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_600])).

tff(c_718,plain,(
    ! [G_236,B_237,A_238] :
      ( G_236 = B_237
      | G_236 = A_238
      | G_236 = A_238
      | G_236 = A_238
      | G_236 = A_238
      | ~ r2_hidden(G_236,k2_tarski(A_238,B_237)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_662])).

tff(c_867,plain,(
    ! [G_251,A_252] :
      ( G_251 = A_252
      | G_251 = A_252
      | G_251 = A_252
      | G_251 = A_252
      | G_251 = A_252
      | ~ r2_hidden(G_251,k1_tarski(A_252)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_718])).

tff(c_1044,plain,(
    ! [G_265] :
      ( G_265 = '#skF_9'
      | G_265 = '#skF_9'
      | G_265 = '#skF_9'
      | G_265 = '#skF_9'
      | G_265 = '#skF_9'
      | ~ r2_hidden(G_265,k1_relat_1('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_867])).

tff(c_1059,plain,(
    ! [B_200] :
      ( '#skF_6'('#skF_10',B_200) = '#skF_9'
      | ~ v1_xboole_0(B_200)
      | k2_relat_1('#skF_10') = B_200
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_435,c_1044])).

tff(c_1105,plain,(
    ! [B_266] :
      ( '#skF_6'('#skF_10',B_266) = '#skF_9'
      | ~ v1_xboole_0(B_266)
      | k2_relat_1('#skF_10') = B_266 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_1059])).

tff(c_1111,plain,
    ( '#skF_6'('#skF_10',k1_xboole_0) = '#skF_9'
    | k2_relat_1('#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_1105])).

tff(c_1115,plain,(
    '#skF_6'('#skF_10',k1_xboole_0) = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_1111])).

tff(c_529,plain,(
    ! [A_218,B_219] :
      ( k1_funct_1(A_218,'#skF_6'(A_218,B_219)) = '#skF_5'(A_218,B_219)
      | r2_hidden('#skF_7'(A_218,B_219),B_219)
      | k2_relat_1(A_218) = B_219
      | ~ v1_funct_1(A_218)
      | ~ v1_relat_1(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_558,plain,(
    ! [B_219,A_218] :
      ( ~ v1_xboole_0(B_219)
      | k1_funct_1(A_218,'#skF_6'(A_218,B_219)) = '#skF_5'(A_218,B_219)
      | k2_relat_1(A_218) = B_219
      | ~ v1_funct_1(A_218)
      | ~ v1_relat_1(A_218) ) ),
    inference(resolution,[status(thm)],[c_529,c_2])).

tff(c_1119,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_funct_1('#skF_10','#skF_9') = '#skF_5'('#skF_10',k1_xboole_0)
    | k2_relat_1('#skF_10') = k1_xboole_0
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_1115,c_558])).

tff(c_1130,plain,
    ( k1_funct_1('#skF_10','#skF_9') = '#skF_5'('#skF_10',k1_xboole_0)
    | k2_relat_1('#skF_10') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_6,c_1119])).

tff(c_1131,plain,(
    k1_funct_1('#skF_10','#skF_9') = '#skF_5'('#skF_10',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_1130])).

tff(c_1077,plain,(
    ! [C_75] :
      ( '#skF_8'('#skF_10',k2_relat_1('#skF_10'),C_75) = '#skF_9'
      | ~ r2_hidden(C_75,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_68,c_1044])).

tff(c_1173,plain,(
    ! [C_273] :
      ( '#skF_8'('#skF_10',k2_relat_1('#skF_10'),C_273) = '#skF_9'
      | ~ r2_hidden(C_273,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_1077])).

tff(c_1198,plain,(
    ! [D_78] :
      ( '#skF_8'('#skF_10',k2_relat_1('#skF_10'),k1_funct_1('#skF_10',D_78)) = '#skF_9'
      | ~ r2_hidden(D_78,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_64,c_1173])).

tff(c_1305,plain,(
    ! [D_276] :
      ( '#skF_8'('#skF_10',k2_relat_1('#skF_10'),k1_funct_1('#skF_10',D_276)) = '#skF_9'
      | ~ r2_hidden(D_276,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_1198])).

tff(c_66,plain,(
    ! [A_39,C_75] :
      ( k1_funct_1(A_39,'#skF_8'(A_39,k2_relat_1(A_39),C_75)) = C_75
      | ~ r2_hidden(C_75,k2_relat_1(A_39))
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1311,plain,(
    ! [D_276] :
      ( k1_funct_1('#skF_10',D_276) = k1_funct_1('#skF_10','#skF_9')
      | ~ r2_hidden(k1_funct_1('#skF_10',D_276),k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(D_276,k1_relat_1('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1305,c_66])).

tff(c_19078,plain,(
    ! [D_76189] :
      ( k1_funct_1('#skF_10',D_76189) = '#skF_5'('#skF_10',k1_xboole_0)
      | ~ r2_hidden(k1_funct_1('#skF_10',D_76189),k2_relat_1('#skF_10'))
      | ~ r2_hidden(D_76189,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_1131,c_1311])).

tff(c_19109,plain,(
    ! [D_78] :
      ( k1_funct_1('#skF_10',D_78) = '#skF_5'('#skF_10',k1_xboole_0)
      | ~ r2_hidden(D_78,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_64,c_19078])).

tff(c_19122,plain,(
    ! [D_76582] :
      ( k1_funct_1('#skF_10',D_76582) = '#skF_5'('#skF_10',k1_xboole_0)
      | ~ r2_hidden(D_76582,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_19109])).

tff(c_19170,plain,(
    ! [C_75] :
      ( k1_funct_1('#skF_10','#skF_8'('#skF_10',k2_relat_1('#skF_10'),C_75)) = '#skF_5'('#skF_10',k1_xboole_0)
      | ~ r2_hidden(C_75,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_68,c_19122])).

tff(c_19723,plain,(
    ! [C_78941] :
      ( k1_funct_1('#skF_10','#skF_8'('#skF_10',k2_relat_1('#skF_10'),C_78941)) = '#skF_5'('#skF_10',k1_xboole_0)
      | ~ r2_hidden(C_78941,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_19170])).

tff(c_19745,plain,(
    ! [C_78941] :
      ( C_78941 = '#skF_5'('#skF_10',k1_xboole_0)
      | ~ r2_hidden(C_78941,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(C_78941,k2_relat_1('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19723,c_66])).

tff(c_19826,plain,(
    ! [C_79334] :
      ( C_79334 = '#skF_5'('#skF_10',k1_xboole_0)
      | ~ r2_hidden(C_79334,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_19745])).

tff(c_19868,plain,(
    ! [B_27] :
      ( '#skF_2'(k2_relat_1('#skF_10'),B_27) = '#skF_5'('#skF_10',k1_xboole_0)
      | k2_relat_1('#skF_10') = k1_xboole_0
      | k2_relat_1('#skF_10') = k1_tarski(B_27) ) ),
    inference(resolution,[status(thm)],[c_22,c_19826])).

tff(c_19893,plain,(
    ! [B_79727] :
      ( '#skF_2'(k2_relat_1('#skF_10'),B_79727) = '#skF_5'('#skF_10',k1_xboole_0)
      | k2_relat_1('#skF_10') = k1_tarski(B_79727) ) ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_19868])).

tff(c_20,plain,(
    ! [A_26,B_27] :
      ( '#skF_2'(A_26,B_27) != B_27
      | k1_xboole_0 = A_26
      | k1_tarski(B_27) = A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_19907,plain,(
    ! [B_79727] :
      ( B_79727 != '#skF_5'('#skF_10',k1_xboole_0)
      | k2_relat_1('#skF_10') = k1_xboole_0
      | k2_relat_1('#skF_10') = k1_tarski(B_79727)
      | k2_relat_1('#skF_10') = k1_tarski(B_79727) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19893,c_20])).

tff(c_19982,plain,(
    k1_tarski('#skF_5'('#skF_10',k1_xboole_0)) = k2_relat_1('#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_19907])).

tff(c_82,plain,(
    k1_tarski(k1_funct_1('#skF_10','#skF_9')) != k2_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1140,plain,(
    k1_tarski('#skF_5'('#skF_10',k1_xboole_0)) != k2_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1131,c_82])).

tff(c_19986,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19982,c_1140])).

tff(c_19988,plain,(
    k1_relat_1('#skF_10') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_20001,plain,(
    k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_19988,c_84])).

tff(c_20052,plain,(
    ! [A_80158,B_80159,C_80160,D_80161] : k3_enumset1(A_80158,A_80158,B_80159,C_80160,D_80161) = k2_enumset1(A_80158,B_80159,C_80160,D_80161) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_20011,plain,(
    ! [B_80122,E_80123,C_80124,D_80121,G_80125] : r2_hidden(G_80125,k3_enumset1(G_80125,B_80122,C_80124,D_80121,E_80123)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_20015,plain,(
    ! [B_80122,E_80123,C_80124,D_80121,G_80125] : ~ v1_xboole_0(k3_enumset1(G_80125,B_80122,C_80124,D_80121,E_80123)) ),
    inference(resolution,[status(thm)],[c_20011,c_2])).

tff(c_20078,plain,(
    ! [A_80162,B_80163,C_80164,D_80165] : ~ v1_xboole_0(k2_enumset1(A_80162,B_80163,C_80164,D_80165)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20052,c_20015])).

tff(c_20081,plain,(
    ! [A_80166,B_80167,C_80168] : ~ v1_xboole_0(k1_enumset1(A_80166,B_80167,C_80168)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_20078])).

tff(c_20084,plain,(
    ! [A_80169,B_80170] : ~ v1_xboole_0(k2_tarski(A_80169,B_80170)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_20081])).

tff(c_20087,plain,(
    ! [A_80171] : ~ v1_xboole_0(k1_tarski(A_80171)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_20084])).

tff(c_20089,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20001,c_20087])).

tff(c_20092,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_20089])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:11:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.75/4.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.75/4.42  
% 11.75/4.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.75/4.42  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_10 > #skF_9 > #skF_3 > #skF_2 > #skF_8 > #skF_7 > #skF_5 > #skF_4
% 11.75/4.42  
% 11.75/4.42  %Foreground sorts:
% 11.75/4.42  
% 11.75/4.42  
% 11.75/4.42  %Background operators:
% 11.75/4.42  
% 11.75/4.42  
% 11.75/4.42  %Foreground operators:
% 11.75/4.42  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 11.75/4.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.75/4.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.75/4.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.75/4.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.75/4.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 11.75/4.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.75/4.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.75/4.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.75/4.42  tff('#skF_10', type, '#skF_10': $i).
% 11.75/4.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.75/4.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.75/4.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.75/4.42  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.75/4.42  tff('#skF_9', type, '#skF_9': $i).
% 11.75/4.42  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 11.75/4.42  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i) > $i).
% 11.75/4.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.75/4.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.75/4.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.75/4.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.75/4.42  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 11.75/4.42  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 11.75/4.42  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 11.75/4.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.75/4.42  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 11.75/4.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.75/4.42  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i) > $i).
% 11.75/4.42  
% 11.88/4.44  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 11.88/4.44  tff(f_109, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 11.88/4.44  tff(f_85, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 11.88/4.44  tff(f_58, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 11.88/4.44  tff(f_100, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 11.88/4.44  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 11.88/4.44  tff(f_34, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 11.88/4.44  tff(f_36, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 11.88/4.44  tff(f_38, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 11.88/4.44  tff(f_40, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 11.88/4.44  tff(f_79, axiom, (![A, B, C, D, E, F]: ((F = k3_enumset1(A, B, C, D, E)) <=> (![G]: (r2_hidden(G, F) <=> ~((((~(G = A) & ~(G = B)) & ~(G = C)) & ~(G = D)) & ~(G = E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_enumset1)).
% 11.88/4.44  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.88/4.44  tff(c_88, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.88/4.44  tff(c_117, plain, (![A_85]: (k2_relat_1(A_85)=k1_xboole_0 | k1_relat_1(A_85)!=k1_xboole_0 | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.88/4.44  tff(c_121, plain, (k2_relat_1('#skF_10')=k1_xboole_0 | k1_relat_1('#skF_10')!=k1_xboole_0), inference(resolution, [status(thm)], [c_88, c_117])).
% 11.88/4.44  tff(c_122, plain, (k1_relat_1('#skF_10')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_121])).
% 11.88/4.44  tff(c_123, plain, (![A_86]: (k1_relat_1(A_86)=k1_xboole_0 | k2_relat_1(A_86)!=k1_xboole_0 | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.88/4.44  tff(c_126, plain, (k1_relat_1('#skF_10')=k1_xboole_0 | k2_relat_1('#skF_10')!=k1_xboole_0), inference(resolution, [status(thm)], [c_88, c_123])).
% 11.88/4.44  tff(c_129, plain, (k2_relat_1('#skF_10')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_122, c_126])).
% 11.88/4.44  tff(c_22, plain, (![A_26, B_27]: (r2_hidden('#skF_2'(A_26, B_27), A_26) | k1_xboole_0=A_26 | k1_tarski(B_27)=A_26)), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.88/4.44  tff(c_86, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.88/4.44  tff(c_68, plain, (![A_39, C_75]: (r2_hidden('#skF_8'(A_39, k2_relat_1(A_39), C_75), k1_relat_1(A_39)) | ~r2_hidden(C_75, k2_relat_1(A_39)) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.88/4.44  tff(c_64, plain, (![A_39, D_78]: (r2_hidden(k1_funct_1(A_39, D_78), k2_relat_1(A_39)) | ~r2_hidden(D_78, k1_relat_1(A_39)) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.88/4.44  tff(c_413, plain, (![A_199, B_200]: (r2_hidden('#skF_6'(A_199, B_200), k1_relat_1(A_199)) | r2_hidden('#skF_7'(A_199, B_200), B_200) | k2_relat_1(A_199)=B_200 | ~v1_funct_1(A_199) | ~v1_relat_1(A_199))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.88/4.44  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.88/4.44  tff(c_435, plain, (![B_200, A_199]: (~v1_xboole_0(B_200) | r2_hidden('#skF_6'(A_199, B_200), k1_relat_1(A_199)) | k2_relat_1(A_199)=B_200 | ~v1_funct_1(A_199) | ~v1_relat_1(A_199))), inference(resolution, [status(thm)], [c_413, c_2])).
% 11.88/4.44  tff(c_84, plain, (k1_tarski('#skF_9')=k1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.88/4.44  tff(c_8, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.88/4.44  tff(c_10, plain, (![A_6, B_7]: (k1_enumset1(A_6, A_6, B_7)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.88/4.44  tff(c_12, plain, (![A_8, B_9, C_10]: (k2_enumset1(A_8, A_8, B_9, C_10)=k1_enumset1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.88/4.44  tff(c_14, plain, (![A_11, B_12, C_13, D_14]: (k3_enumset1(A_11, A_11, B_12, C_13, D_14)=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.88/4.44  tff(c_451, plain, (![B_204, E_206, D_203, A_205, C_207, G_208]: (G_208=E_206 | G_208=D_203 | G_208=C_207 | G_208=B_204 | G_208=A_205 | ~r2_hidden(G_208, k3_enumset1(A_205, B_204, C_207, D_203, E_206)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.88/4.44  tff(c_600, plain, (![D_228, G_225, B_227, C_224, A_226]: (G_225=D_228 | G_225=C_224 | G_225=B_227 | G_225=A_226 | G_225=A_226 | ~r2_hidden(G_225, k2_enumset1(A_226, B_227, C_224, D_228)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_451])).
% 11.88/4.44  tff(c_662, plain, (![G_232, C_233, B_234, A_235]: (G_232=C_233 | G_232=B_234 | G_232=A_235 | G_232=A_235 | G_232=A_235 | ~r2_hidden(G_232, k1_enumset1(A_235, B_234, C_233)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_600])).
% 11.88/4.44  tff(c_718, plain, (![G_236, B_237, A_238]: (G_236=B_237 | G_236=A_238 | G_236=A_238 | G_236=A_238 | G_236=A_238 | ~r2_hidden(G_236, k2_tarski(A_238, B_237)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_662])).
% 11.88/4.44  tff(c_867, plain, (![G_251, A_252]: (G_251=A_252 | G_251=A_252 | G_251=A_252 | G_251=A_252 | G_251=A_252 | ~r2_hidden(G_251, k1_tarski(A_252)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_718])).
% 11.88/4.44  tff(c_1044, plain, (![G_265]: (G_265='#skF_9' | G_265='#skF_9' | G_265='#skF_9' | G_265='#skF_9' | G_265='#skF_9' | ~r2_hidden(G_265, k1_relat_1('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_84, c_867])).
% 11.88/4.44  tff(c_1059, plain, (![B_200]: ('#skF_6'('#skF_10', B_200)='#skF_9' | ~v1_xboole_0(B_200) | k2_relat_1('#skF_10')=B_200 | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_435, c_1044])).
% 11.88/4.44  tff(c_1105, plain, (![B_266]: ('#skF_6'('#skF_10', B_266)='#skF_9' | ~v1_xboole_0(B_266) | k2_relat_1('#skF_10')=B_266)), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_1059])).
% 11.88/4.44  tff(c_1111, plain, ('#skF_6'('#skF_10', k1_xboole_0)='#skF_9' | k2_relat_1('#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_1105])).
% 11.88/4.44  tff(c_1115, plain, ('#skF_6'('#skF_10', k1_xboole_0)='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_129, c_1111])).
% 11.88/4.44  tff(c_529, plain, (![A_218, B_219]: (k1_funct_1(A_218, '#skF_6'(A_218, B_219))='#skF_5'(A_218, B_219) | r2_hidden('#skF_7'(A_218, B_219), B_219) | k2_relat_1(A_218)=B_219 | ~v1_funct_1(A_218) | ~v1_relat_1(A_218))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.88/4.44  tff(c_558, plain, (![B_219, A_218]: (~v1_xboole_0(B_219) | k1_funct_1(A_218, '#skF_6'(A_218, B_219))='#skF_5'(A_218, B_219) | k2_relat_1(A_218)=B_219 | ~v1_funct_1(A_218) | ~v1_relat_1(A_218))), inference(resolution, [status(thm)], [c_529, c_2])).
% 11.88/4.44  tff(c_1119, plain, (~v1_xboole_0(k1_xboole_0) | k1_funct_1('#skF_10', '#skF_9')='#skF_5'('#skF_10', k1_xboole_0) | k2_relat_1('#skF_10')=k1_xboole_0 | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_1115, c_558])).
% 11.88/4.44  tff(c_1130, plain, (k1_funct_1('#skF_10', '#skF_9')='#skF_5'('#skF_10', k1_xboole_0) | k2_relat_1('#skF_10')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_6, c_1119])).
% 11.88/4.44  tff(c_1131, plain, (k1_funct_1('#skF_10', '#skF_9')='#skF_5'('#skF_10', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_129, c_1130])).
% 11.88/4.44  tff(c_1077, plain, (![C_75]: ('#skF_8'('#skF_10', k2_relat_1('#skF_10'), C_75)='#skF_9' | ~r2_hidden(C_75, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_68, c_1044])).
% 11.88/4.44  tff(c_1173, plain, (![C_273]: ('#skF_8'('#skF_10', k2_relat_1('#skF_10'), C_273)='#skF_9' | ~r2_hidden(C_273, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_1077])).
% 11.88/4.44  tff(c_1198, plain, (![D_78]: ('#skF_8'('#skF_10', k2_relat_1('#skF_10'), k1_funct_1('#skF_10', D_78))='#skF_9' | ~r2_hidden(D_78, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_64, c_1173])).
% 11.88/4.44  tff(c_1305, plain, (![D_276]: ('#skF_8'('#skF_10', k2_relat_1('#skF_10'), k1_funct_1('#skF_10', D_276))='#skF_9' | ~r2_hidden(D_276, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_1198])).
% 11.88/4.44  tff(c_66, plain, (![A_39, C_75]: (k1_funct_1(A_39, '#skF_8'(A_39, k2_relat_1(A_39), C_75))=C_75 | ~r2_hidden(C_75, k2_relat_1(A_39)) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.88/4.44  tff(c_1311, plain, (![D_276]: (k1_funct_1('#skF_10', D_276)=k1_funct_1('#skF_10', '#skF_9') | ~r2_hidden(k1_funct_1('#skF_10', D_276), k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(D_276, k1_relat_1('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_1305, c_66])).
% 11.88/4.44  tff(c_19078, plain, (![D_76189]: (k1_funct_1('#skF_10', D_76189)='#skF_5'('#skF_10', k1_xboole_0) | ~r2_hidden(k1_funct_1('#skF_10', D_76189), k2_relat_1('#skF_10')) | ~r2_hidden(D_76189, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_1131, c_1311])).
% 11.88/4.44  tff(c_19109, plain, (![D_78]: (k1_funct_1('#skF_10', D_78)='#skF_5'('#skF_10', k1_xboole_0) | ~r2_hidden(D_78, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_64, c_19078])).
% 11.88/4.44  tff(c_19122, plain, (![D_76582]: (k1_funct_1('#skF_10', D_76582)='#skF_5'('#skF_10', k1_xboole_0) | ~r2_hidden(D_76582, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_19109])).
% 11.88/4.44  tff(c_19170, plain, (![C_75]: (k1_funct_1('#skF_10', '#skF_8'('#skF_10', k2_relat_1('#skF_10'), C_75))='#skF_5'('#skF_10', k1_xboole_0) | ~r2_hidden(C_75, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_68, c_19122])).
% 11.88/4.44  tff(c_19723, plain, (![C_78941]: (k1_funct_1('#skF_10', '#skF_8'('#skF_10', k2_relat_1('#skF_10'), C_78941))='#skF_5'('#skF_10', k1_xboole_0) | ~r2_hidden(C_78941, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_19170])).
% 11.88/4.44  tff(c_19745, plain, (![C_78941]: (C_78941='#skF_5'('#skF_10', k1_xboole_0) | ~r2_hidden(C_78941, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(C_78941, k2_relat_1('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_19723, c_66])).
% 11.88/4.44  tff(c_19826, plain, (![C_79334]: (C_79334='#skF_5'('#skF_10', k1_xboole_0) | ~r2_hidden(C_79334, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_19745])).
% 11.88/4.44  tff(c_19868, plain, (![B_27]: ('#skF_2'(k2_relat_1('#skF_10'), B_27)='#skF_5'('#skF_10', k1_xboole_0) | k2_relat_1('#skF_10')=k1_xboole_0 | k2_relat_1('#skF_10')=k1_tarski(B_27))), inference(resolution, [status(thm)], [c_22, c_19826])).
% 11.88/4.44  tff(c_19893, plain, (![B_79727]: ('#skF_2'(k2_relat_1('#skF_10'), B_79727)='#skF_5'('#skF_10', k1_xboole_0) | k2_relat_1('#skF_10')=k1_tarski(B_79727))), inference(negUnitSimplification, [status(thm)], [c_129, c_19868])).
% 11.88/4.44  tff(c_20, plain, (![A_26, B_27]: ('#skF_2'(A_26, B_27)!=B_27 | k1_xboole_0=A_26 | k1_tarski(B_27)=A_26)), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.88/4.44  tff(c_19907, plain, (![B_79727]: (B_79727!='#skF_5'('#skF_10', k1_xboole_0) | k2_relat_1('#skF_10')=k1_xboole_0 | k2_relat_1('#skF_10')=k1_tarski(B_79727) | k2_relat_1('#skF_10')=k1_tarski(B_79727))), inference(superposition, [status(thm), theory('equality')], [c_19893, c_20])).
% 11.88/4.44  tff(c_19982, plain, (k1_tarski('#skF_5'('#skF_10', k1_xboole_0))=k2_relat_1('#skF_10')), inference(negUnitSimplification, [status(thm)], [c_129, c_19907])).
% 11.88/4.44  tff(c_82, plain, (k1_tarski(k1_funct_1('#skF_10', '#skF_9'))!=k2_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.88/4.44  tff(c_1140, plain, (k1_tarski('#skF_5'('#skF_10', k1_xboole_0))!=k2_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1131, c_82])).
% 11.88/4.44  tff(c_19986, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19982, c_1140])).
% 11.88/4.44  tff(c_19988, plain, (k1_relat_1('#skF_10')=k1_xboole_0), inference(splitRight, [status(thm)], [c_121])).
% 11.88/4.44  tff(c_20001, plain, (k1_tarski('#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_19988, c_84])).
% 11.88/4.44  tff(c_20052, plain, (![A_80158, B_80159, C_80160, D_80161]: (k3_enumset1(A_80158, A_80158, B_80159, C_80160, D_80161)=k2_enumset1(A_80158, B_80159, C_80160, D_80161))), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.88/4.44  tff(c_20011, plain, (![B_80122, E_80123, C_80124, D_80121, G_80125]: (r2_hidden(G_80125, k3_enumset1(G_80125, B_80122, C_80124, D_80121, E_80123)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.88/4.44  tff(c_20015, plain, (![B_80122, E_80123, C_80124, D_80121, G_80125]: (~v1_xboole_0(k3_enumset1(G_80125, B_80122, C_80124, D_80121, E_80123)))), inference(resolution, [status(thm)], [c_20011, c_2])).
% 11.88/4.44  tff(c_20078, plain, (![A_80162, B_80163, C_80164, D_80165]: (~v1_xboole_0(k2_enumset1(A_80162, B_80163, C_80164, D_80165)))), inference(superposition, [status(thm), theory('equality')], [c_20052, c_20015])).
% 11.88/4.44  tff(c_20081, plain, (![A_80166, B_80167, C_80168]: (~v1_xboole_0(k1_enumset1(A_80166, B_80167, C_80168)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_20078])).
% 11.88/4.44  tff(c_20084, plain, (![A_80169, B_80170]: (~v1_xboole_0(k2_tarski(A_80169, B_80170)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_20081])).
% 11.88/4.44  tff(c_20087, plain, (![A_80171]: (~v1_xboole_0(k1_tarski(A_80171)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_20084])).
% 11.88/4.44  tff(c_20089, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20001, c_20087])).
% 11.88/4.44  tff(c_20092, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_20089])).
% 11.88/4.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.88/4.44  
% 11.88/4.44  Inference rules
% 11.88/4.44  ----------------------
% 11.88/4.44  #Ref     : 4
% 11.88/4.44  #Sup     : 3390
% 11.88/4.44  #Fact    : 127
% 11.88/4.44  #Define  : 0
% 11.88/4.44  #Split   : 12
% 11.88/4.44  #Chain   : 0
% 11.88/4.44  #Close   : 0
% 11.88/4.44  
% 11.88/4.44  Ordering : KBO
% 11.88/4.44  
% 11.88/4.44  Simplification rules
% 11.88/4.44  ----------------------
% 11.88/4.44  #Subsume      : 1199
% 11.88/4.44  #Demod        : 659
% 11.88/4.44  #Tautology    : 721
% 11.88/4.44  #SimpNegUnit  : 201
% 11.88/4.44  #BackRed      : 18
% 11.88/4.44  
% 11.88/4.44  #Partial instantiations: 28749
% 11.88/4.44  #Strategies tried      : 1
% 11.88/4.44  
% 11.88/4.44  Timing (in seconds)
% 11.88/4.44  ----------------------
% 11.88/4.44  Preprocessing        : 0.34
% 11.88/4.44  Parsing              : 0.17
% 11.88/4.44  CNF conversion       : 0.03
% 11.88/4.45  Main loop            : 3.31
% 11.88/4.45  Inferencing          : 1.59
% 11.88/4.45  Reduction            : 0.73
% 11.88/4.45  Demodulation         : 0.52
% 11.88/4.45  BG Simplification    : 0.13
% 11.88/4.45  Subsumption          : 0.71
% 11.88/4.45  Abstraction          : 0.25
% 11.88/4.45  MUC search           : 0.00
% 11.88/4.45  Cooper               : 0.00
% 11.88/4.45  Total                : 3.69
% 11.88/4.45  Index Insertion      : 0.00
% 11.88/4.45  Index Deletion       : 0.00
% 11.88/4.45  Index Matching       : 0.00
% 11.88/4.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
