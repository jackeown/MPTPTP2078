%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:57 EST 2020

% Result     : Theorem 6.34s
% Output     : CNFRefutation 6.34s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 265 expanded)
%              Number of leaves         :   38 ( 108 expanded)
%              Depth                    :   25
%              Number of atoms          :  199 ( 650 expanded)
%              Number of equality atoms :  114 ( 376 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_43,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_111,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_102,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_81,axiom,(
    ! [A,B,C,D,E,F] :
      ( F = k3_enumset1(A,B,C,D,E)
    <=> ! [G] :
          ( r2_hidden(G,F)
        <=> ~ ( G != A
              & G != B
              & G != C
              & G != D
              & G != E ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

tff(c_16,plain,(
    ! [A_22] : k2_zfmisc_1(A_22,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_117,plain,(
    ! [A_81,B_82] : ~ r2_hidden(A_81,k2_zfmisc_1(A_81,B_82)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_120,plain,(
    ! [A_22] : ~ r2_hidden(A_22,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_117])).

tff(c_90,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_143,plain,(
    ! [A_87] :
      ( k1_relat_1(A_87) = k1_xboole_0
      | k2_relat_1(A_87) != k1_xboole_0
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_147,plain,
    ( k1_relat_1('#skF_9') = k1_xboole_0
    | k2_relat_1('#skF_9') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_90,c_143])).

tff(c_148,plain,(
    k2_relat_1('#skF_9') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_24,plain,(
    ! [A_26,B_27] :
      ( r2_hidden('#skF_1'(A_26,B_27),A_26)
      | k1_xboole_0 = A_26
      | k1_tarski(B_27) = A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_88,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_70,plain,(
    ! [A_39,C_75] :
      ( r2_hidden('#skF_7'(A_39,k2_relat_1(A_39),C_75),k1_relat_1(A_39))
      | ~ r2_hidden(C_75,k2_relat_1(A_39))
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_66,plain,(
    ! [A_39,D_78] :
      ( r2_hidden(k1_funct_1(A_39,D_78),k2_relat_1(A_39))
      | ~ r2_hidden(D_78,k1_relat_1(A_39))
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_82,plain,(
    ! [A_39,B_61] :
      ( r2_hidden('#skF_5'(A_39,B_61),k1_relat_1(A_39))
      | r2_hidden('#skF_6'(A_39,B_61),B_61)
      | k2_relat_1(A_39) = B_61
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_86,plain,(
    k1_tarski('#skF_8') = k1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9,D_10] : k3_enumset1(A_7,A_7,B_8,C_9,D_10) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_295,plain,(
    ! [B_177,A_178,D_176,C_180,G_181,E_179] :
      ( G_181 = E_179
      | G_181 = D_176
      | G_181 = C_180
      | G_181 = B_177
      | G_181 = A_178
      | ~ r2_hidden(G_181,k3_enumset1(A_178,B_177,C_180,D_176,E_179)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_342,plain,(
    ! [C_187,D_184,A_188,B_186,G_185] :
      ( G_185 = D_184
      | G_185 = C_187
      | G_185 = B_186
      | G_185 = A_188
      | G_185 = A_188
      | ~ r2_hidden(G_185,k2_enumset1(A_188,B_186,C_187,D_184)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_295])).

tff(c_381,plain,(
    ! [G_189,C_190,B_191,A_192] :
      ( G_189 = C_190
      | G_189 = B_191
      | G_189 = A_192
      | G_189 = A_192
      | G_189 = A_192
      | ~ r2_hidden(G_189,k1_enumset1(A_192,B_191,C_190)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_342])).

tff(c_415,plain,(
    ! [G_193,B_194,A_195] :
      ( G_193 = B_194
      | G_193 = A_195
      | G_193 = A_195
      | G_193 = A_195
      | G_193 = A_195
      | ~ r2_hidden(G_193,k2_tarski(A_195,B_194)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_381])).

tff(c_481,plain,(
    ! [G_198,A_199] :
      ( G_198 = A_199
      | G_198 = A_199
      | G_198 = A_199
      | G_198 = A_199
      | G_198 = A_199
      | ~ r2_hidden(G_198,k1_tarski(A_199)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_415])).

tff(c_611,plain,(
    ! [G_209] :
      ( G_209 = '#skF_8'
      | G_209 = '#skF_8'
      | G_209 = '#skF_8'
      | G_209 = '#skF_8'
      | G_209 = '#skF_8'
      | ~ r2_hidden(G_209,k1_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_481])).

tff(c_622,plain,(
    ! [B_61] :
      ( '#skF_5'('#skF_9',B_61) = '#skF_8'
      | r2_hidden('#skF_6'('#skF_9',B_61),B_61)
      | k2_relat_1('#skF_9') = B_61
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_82,c_611])).

tff(c_681,plain,(
    ! [B_211] :
      ( '#skF_5'('#skF_9',B_211) = '#skF_8'
      | r2_hidden('#skF_6'('#skF_9',B_211),B_211)
      | k2_relat_1('#skF_9') = B_211 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_622])).

tff(c_713,plain,
    ( '#skF_5'('#skF_9',k1_xboole_0) = '#skF_8'
    | k2_relat_1('#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_681,c_120])).

tff(c_724,plain,(
    '#skF_5'('#skF_9',k1_xboole_0) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_713])).

tff(c_444,plain,(
    ! [A_196,B_197] :
      ( k1_funct_1(A_196,'#skF_5'(A_196,B_197)) = '#skF_4'(A_196,B_197)
      | r2_hidden('#skF_6'(A_196,B_197),B_197)
      | k2_relat_1(A_196) = B_197
      | ~ v1_funct_1(A_196)
      | ~ v1_relat_1(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_4813,plain,(
    ! [A_12936] :
      ( k1_funct_1(A_12936,'#skF_5'(A_12936,k1_xboole_0)) = '#skF_4'(A_12936,k1_xboole_0)
      | k2_relat_1(A_12936) = k1_xboole_0
      | ~ v1_funct_1(A_12936)
      | ~ v1_relat_1(A_12936) ) ),
    inference(resolution,[status(thm)],[c_444,c_120])).

tff(c_4840,plain,
    ( k1_funct_1('#skF_9','#skF_8') = '#skF_4'('#skF_9',k1_xboole_0)
    | k2_relat_1('#skF_9') = k1_xboole_0
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_724,c_4813])).

tff(c_4853,plain,
    ( k1_funct_1('#skF_9','#skF_8') = '#skF_4'('#skF_9',k1_xboole_0)
    | k2_relat_1('#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_4840])).

tff(c_4854,plain,(
    k1_funct_1('#skF_9','#skF_8') = '#skF_4'('#skF_9',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_4853])).

tff(c_634,plain,(
    ! [C_75] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_75) = '#skF_8'
      | ~ r2_hidden(C_75,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_70,c_611])).

tff(c_651,plain,(
    ! [C_210] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_210) = '#skF_8'
      | ~ r2_hidden(C_210,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_634])).

tff(c_667,plain,(
    ! [D_78] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),k1_funct_1('#skF_9',D_78)) = '#skF_8'
      | ~ r2_hidden(D_78,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_66,c_651])).

tff(c_736,plain,(
    ! [D_212] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),k1_funct_1('#skF_9',D_212)) = '#skF_8'
      | ~ r2_hidden(D_212,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_667])).

tff(c_68,plain,(
    ! [A_39,C_75] :
      ( k1_funct_1(A_39,'#skF_7'(A_39,k2_relat_1(A_39),C_75)) = C_75
      | ~ r2_hidden(C_75,k2_relat_1(A_39))
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_742,plain,(
    ! [D_212] :
      ( k1_funct_1('#skF_9',D_212) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(k1_funct_1('#skF_9',D_212),k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(D_212,k1_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_736,c_68])).

tff(c_757,plain,(
    ! [D_212] :
      ( k1_funct_1('#skF_9',D_212) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(k1_funct_1('#skF_9',D_212),k2_relat_1('#skF_9'))
      | ~ r2_hidden(D_212,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_742])).

tff(c_5287,plain,(
    ! [D_14100] :
      ( k1_funct_1('#skF_9',D_14100) = '#skF_4'('#skF_9',k1_xboole_0)
      | ~ r2_hidden(k1_funct_1('#skF_9',D_14100),k2_relat_1('#skF_9'))
      | ~ r2_hidden(D_14100,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4854,c_757])).

tff(c_5307,plain,(
    ! [D_78] :
      ( k1_funct_1('#skF_9',D_78) = '#skF_4'('#skF_9',k1_xboole_0)
      | ~ r2_hidden(D_78,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_66,c_5287])).

tff(c_5318,plain,(
    ! [D_14158] :
      ( k1_funct_1('#skF_9',D_14158) = '#skF_4'('#skF_9',k1_xboole_0)
      | ~ r2_hidden(D_14158,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_5307])).

tff(c_5352,plain,(
    ! [C_75] :
      ( k1_funct_1('#skF_9','#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_75)) = '#skF_4'('#skF_9',k1_xboole_0)
      | ~ r2_hidden(C_75,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_70,c_5318])).

tff(c_5628,plain,(
    ! [C_14395] :
      ( k1_funct_1('#skF_9','#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_14395)) = '#skF_4'('#skF_9',k1_xboole_0)
      | ~ r2_hidden(C_14395,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_5352])).

tff(c_5648,plain,(
    ! [C_14395] :
      ( C_14395 = '#skF_4'('#skF_9',k1_xboole_0)
      | ~ r2_hidden(C_14395,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(C_14395,k2_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5628,c_68])).

tff(c_5726,plain,(
    ! [C_14511] :
      ( C_14511 = '#skF_4'('#skF_9',k1_xboole_0)
      | ~ r2_hidden(C_14511,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_5648])).

tff(c_5757,plain,(
    ! [B_27] :
      ( '#skF_1'(k2_relat_1('#skF_9'),B_27) = '#skF_4'('#skF_9',k1_xboole_0)
      | k2_relat_1('#skF_9') = k1_xboole_0
      | k2_relat_1('#skF_9') = k1_tarski(B_27) ) ),
    inference(resolution,[status(thm)],[c_24,c_5726])).

tff(c_5773,plain,(
    ! [B_14569] :
      ( '#skF_1'(k2_relat_1('#skF_9'),B_14569) = '#skF_4'('#skF_9',k1_xboole_0)
      | k2_relat_1('#skF_9') = k1_tarski(B_14569) ) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_5757])).

tff(c_22,plain,(
    ! [A_26,B_27] :
      ( '#skF_1'(A_26,B_27) != B_27
      | k1_xboole_0 = A_26
      | k1_tarski(B_27) = A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_5787,plain,(
    ! [B_14569] :
      ( B_14569 != '#skF_4'('#skF_9',k1_xboole_0)
      | k2_relat_1('#skF_9') = k1_xboole_0
      | k2_relat_1('#skF_9') = k1_tarski(B_14569)
      | k2_relat_1('#skF_9') = k1_tarski(B_14569) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5773,c_22])).

tff(c_5821,plain,(
    k1_tarski('#skF_4'('#skF_9',k1_xboole_0)) = k2_relat_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_5787])).

tff(c_84,plain,(
    k1_tarski(k1_funct_1('#skF_9','#skF_8')) != k2_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_4860,plain,(
    k1_tarski('#skF_4'('#skF_9',k1_xboole_0)) != k2_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4854,c_84])).

tff(c_5825,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5821,c_4860])).

tff(c_5826,plain,(
    k1_relat_1('#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_5828,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5826,c_86])).

tff(c_5882,plain,(
    ! [A_14662,B_14663,C_14664,D_14665] : k3_enumset1(A_14662,A_14662,B_14663,C_14664,D_14665) = k2_enumset1(A_14662,B_14663,C_14664,D_14665) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_36,plain,(
    ! [E_33,G_37,D_32,C_31,B_30] : r2_hidden(G_37,k3_enumset1(G_37,B_30,C_31,D_32,E_33)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_5915,plain,(
    ! [A_14671,B_14672,C_14673,D_14674] : r2_hidden(A_14671,k2_enumset1(A_14671,B_14672,C_14673,D_14674)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5882,c_36])).

tff(c_5919,plain,(
    ! [A_14675,B_14676,C_14677] : r2_hidden(A_14675,k1_enumset1(A_14675,B_14676,C_14677)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_5915])).

tff(c_5923,plain,(
    ! [A_14678,B_14679] : r2_hidden(A_14678,k2_tarski(A_14678,B_14679)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_5919])).

tff(c_5927,plain,(
    ! [A_14680] : r2_hidden(A_14680,k1_tarski(A_14680)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5923])).

tff(c_5930,plain,(
    r2_hidden('#skF_8',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5828,c_5927])).

tff(c_5932,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_5930])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:04:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.34/2.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.34/2.34  
% 6.34/2.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.34/2.34  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 6.34/2.34  
% 6.34/2.34  %Foreground sorts:
% 6.34/2.34  
% 6.34/2.34  
% 6.34/2.34  %Background operators:
% 6.34/2.34  
% 6.34/2.34  
% 6.34/2.34  %Foreground operators:
% 6.34/2.34  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 6.34/2.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.34/2.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.34/2.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 6.34/2.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.34/2.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.34/2.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.34/2.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.34/2.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.34/2.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.34/2.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.34/2.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.34/2.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.34/2.34  tff('#skF_9', type, '#skF_9': $i).
% 6.34/2.34  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 6.34/2.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.34/2.34  tff('#skF_8', type, '#skF_8': $i).
% 6.34/2.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i) > $i).
% 6.34/2.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.34/2.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.34/2.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.34/2.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.34/2.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.34/2.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.34/2.34  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 6.34/2.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.34/2.34  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.34/2.34  
% 6.34/2.36  tff(f_43, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.34/2.36  tff(f_46, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 6.34/2.36  tff(f_111, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 6.34/2.36  tff(f_87, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 6.34/2.36  tff(f_60, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 6.34/2.36  tff(f_102, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 6.34/2.36  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.34/2.36  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.34/2.36  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 6.34/2.36  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 6.34/2.36  tff(f_81, axiom, (![A, B, C, D, E, F]: ((F = k3_enumset1(A, B, C, D, E)) <=> (![G]: (r2_hidden(G, F) <=> ~((((~(G = A) & ~(G = B)) & ~(G = C)) & ~(G = D)) & ~(G = E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_enumset1)).
% 6.34/2.36  tff(c_16, plain, (![A_22]: (k2_zfmisc_1(A_22, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.34/2.36  tff(c_117, plain, (![A_81, B_82]: (~r2_hidden(A_81, k2_zfmisc_1(A_81, B_82)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.34/2.36  tff(c_120, plain, (![A_22]: (~r2_hidden(A_22, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_117])).
% 6.34/2.36  tff(c_90, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.34/2.36  tff(c_143, plain, (![A_87]: (k1_relat_1(A_87)=k1_xboole_0 | k2_relat_1(A_87)!=k1_xboole_0 | ~v1_relat_1(A_87))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.34/2.36  tff(c_147, plain, (k1_relat_1('#skF_9')=k1_xboole_0 | k2_relat_1('#skF_9')!=k1_xboole_0), inference(resolution, [status(thm)], [c_90, c_143])).
% 6.34/2.36  tff(c_148, plain, (k2_relat_1('#skF_9')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_147])).
% 6.34/2.36  tff(c_24, plain, (![A_26, B_27]: (r2_hidden('#skF_1'(A_26, B_27), A_26) | k1_xboole_0=A_26 | k1_tarski(B_27)=A_26)), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.34/2.36  tff(c_88, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.34/2.36  tff(c_70, plain, (![A_39, C_75]: (r2_hidden('#skF_7'(A_39, k2_relat_1(A_39), C_75), k1_relat_1(A_39)) | ~r2_hidden(C_75, k2_relat_1(A_39)) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.34/2.36  tff(c_66, plain, (![A_39, D_78]: (r2_hidden(k1_funct_1(A_39, D_78), k2_relat_1(A_39)) | ~r2_hidden(D_78, k1_relat_1(A_39)) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.34/2.36  tff(c_82, plain, (![A_39, B_61]: (r2_hidden('#skF_5'(A_39, B_61), k1_relat_1(A_39)) | r2_hidden('#skF_6'(A_39, B_61), B_61) | k2_relat_1(A_39)=B_61 | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.34/2.36  tff(c_86, plain, (k1_tarski('#skF_8')=k1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.34/2.36  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.34/2.36  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.34/2.36  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.34/2.36  tff(c_8, plain, (![A_7, B_8, C_9, D_10]: (k3_enumset1(A_7, A_7, B_8, C_9, D_10)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.34/2.36  tff(c_295, plain, (![B_177, A_178, D_176, C_180, G_181, E_179]: (G_181=E_179 | G_181=D_176 | G_181=C_180 | G_181=B_177 | G_181=A_178 | ~r2_hidden(G_181, k3_enumset1(A_178, B_177, C_180, D_176, E_179)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.34/2.36  tff(c_342, plain, (![C_187, D_184, A_188, B_186, G_185]: (G_185=D_184 | G_185=C_187 | G_185=B_186 | G_185=A_188 | G_185=A_188 | ~r2_hidden(G_185, k2_enumset1(A_188, B_186, C_187, D_184)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_295])).
% 6.34/2.36  tff(c_381, plain, (![G_189, C_190, B_191, A_192]: (G_189=C_190 | G_189=B_191 | G_189=A_192 | G_189=A_192 | G_189=A_192 | ~r2_hidden(G_189, k1_enumset1(A_192, B_191, C_190)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_342])).
% 6.34/2.36  tff(c_415, plain, (![G_193, B_194, A_195]: (G_193=B_194 | G_193=A_195 | G_193=A_195 | G_193=A_195 | G_193=A_195 | ~r2_hidden(G_193, k2_tarski(A_195, B_194)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_381])).
% 6.34/2.36  tff(c_481, plain, (![G_198, A_199]: (G_198=A_199 | G_198=A_199 | G_198=A_199 | G_198=A_199 | G_198=A_199 | ~r2_hidden(G_198, k1_tarski(A_199)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_415])).
% 6.34/2.36  tff(c_611, plain, (![G_209]: (G_209='#skF_8' | G_209='#skF_8' | G_209='#skF_8' | G_209='#skF_8' | G_209='#skF_8' | ~r2_hidden(G_209, k1_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_86, c_481])).
% 6.34/2.36  tff(c_622, plain, (![B_61]: ('#skF_5'('#skF_9', B_61)='#skF_8' | r2_hidden('#skF_6'('#skF_9', B_61), B_61) | k2_relat_1('#skF_9')=B_61 | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_82, c_611])).
% 6.34/2.36  tff(c_681, plain, (![B_211]: ('#skF_5'('#skF_9', B_211)='#skF_8' | r2_hidden('#skF_6'('#skF_9', B_211), B_211) | k2_relat_1('#skF_9')=B_211)), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_622])).
% 6.34/2.36  tff(c_713, plain, ('#skF_5'('#skF_9', k1_xboole_0)='#skF_8' | k2_relat_1('#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_681, c_120])).
% 6.34/2.36  tff(c_724, plain, ('#skF_5'('#skF_9', k1_xboole_0)='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_148, c_713])).
% 6.34/2.36  tff(c_444, plain, (![A_196, B_197]: (k1_funct_1(A_196, '#skF_5'(A_196, B_197))='#skF_4'(A_196, B_197) | r2_hidden('#skF_6'(A_196, B_197), B_197) | k2_relat_1(A_196)=B_197 | ~v1_funct_1(A_196) | ~v1_relat_1(A_196))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.34/2.36  tff(c_4813, plain, (![A_12936]: (k1_funct_1(A_12936, '#skF_5'(A_12936, k1_xboole_0))='#skF_4'(A_12936, k1_xboole_0) | k2_relat_1(A_12936)=k1_xboole_0 | ~v1_funct_1(A_12936) | ~v1_relat_1(A_12936))), inference(resolution, [status(thm)], [c_444, c_120])).
% 6.34/2.36  tff(c_4840, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_4'('#skF_9', k1_xboole_0) | k2_relat_1('#skF_9')=k1_xboole_0 | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_724, c_4813])).
% 6.34/2.36  tff(c_4853, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_4'('#skF_9', k1_xboole_0) | k2_relat_1('#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_4840])).
% 6.34/2.36  tff(c_4854, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_4'('#skF_9', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_148, c_4853])).
% 6.34/2.36  tff(c_634, plain, (![C_75]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_75)='#skF_8' | ~r2_hidden(C_75, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_70, c_611])).
% 6.34/2.36  tff(c_651, plain, (![C_210]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_210)='#skF_8' | ~r2_hidden(C_210, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_634])).
% 6.34/2.36  tff(c_667, plain, (![D_78]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), k1_funct_1('#skF_9', D_78))='#skF_8' | ~r2_hidden(D_78, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_66, c_651])).
% 6.34/2.36  tff(c_736, plain, (![D_212]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), k1_funct_1('#skF_9', D_212))='#skF_8' | ~r2_hidden(D_212, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_667])).
% 6.34/2.36  tff(c_68, plain, (![A_39, C_75]: (k1_funct_1(A_39, '#skF_7'(A_39, k2_relat_1(A_39), C_75))=C_75 | ~r2_hidden(C_75, k2_relat_1(A_39)) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.34/2.36  tff(c_742, plain, (![D_212]: (k1_funct_1('#skF_9', D_212)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(k1_funct_1('#skF_9', D_212), k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(D_212, k1_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_736, c_68])).
% 6.34/2.36  tff(c_757, plain, (![D_212]: (k1_funct_1('#skF_9', D_212)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(k1_funct_1('#skF_9', D_212), k2_relat_1('#skF_9')) | ~r2_hidden(D_212, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_742])).
% 6.34/2.36  tff(c_5287, plain, (![D_14100]: (k1_funct_1('#skF_9', D_14100)='#skF_4'('#skF_9', k1_xboole_0) | ~r2_hidden(k1_funct_1('#skF_9', D_14100), k2_relat_1('#skF_9')) | ~r2_hidden(D_14100, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_4854, c_757])).
% 6.34/2.36  tff(c_5307, plain, (![D_78]: (k1_funct_1('#skF_9', D_78)='#skF_4'('#skF_9', k1_xboole_0) | ~r2_hidden(D_78, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_66, c_5287])).
% 6.34/2.36  tff(c_5318, plain, (![D_14158]: (k1_funct_1('#skF_9', D_14158)='#skF_4'('#skF_9', k1_xboole_0) | ~r2_hidden(D_14158, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_5307])).
% 6.34/2.36  tff(c_5352, plain, (![C_75]: (k1_funct_1('#skF_9', '#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_75))='#skF_4'('#skF_9', k1_xboole_0) | ~r2_hidden(C_75, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_70, c_5318])).
% 6.34/2.36  tff(c_5628, plain, (![C_14395]: (k1_funct_1('#skF_9', '#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_14395))='#skF_4'('#skF_9', k1_xboole_0) | ~r2_hidden(C_14395, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_5352])).
% 6.34/2.36  tff(c_5648, plain, (![C_14395]: (C_14395='#skF_4'('#skF_9', k1_xboole_0) | ~r2_hidden(C_14395, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(C_14395, k2_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_5628, c_68])).
% 6.34/2.36  tff(c_5726, plain, (![C_14511]: (C_14511='#skF_4'('#skF_9', k1_xboole_0) | ~r2_hidden(C_14511, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_5648])).
% 6.34/2.36  tff(c_5757, plain, (![B_27]: ('#skF_1'(k2_relat_1('#skF_9'), B_27)='#skF_4'('#skF_9', k1_xboole_0) | k2_relat_1('#skF_9')=k1_xboole_0 | k2_relat_1('#skF_9')=k1_tarski(B_27))), inference(resolution, [status(thm)], [c_24, c_5726])).
% 6.34/2.36  tff(c_5773, plain, (![B_14569]: ('#skF_1'(k2_relat_1('#skF_9'), B_14569)='#skF_4'('#skF_9', k1_xboole_0) | k2_relat_1('#skF_9')=k1_tarski(B_14569))), inference(negUnitSimplification, [status(thm)], [c_148, c_5757])).
% 6.34/2.36  tff(c_22, plain, (![A_26, B_27]: ('#skF_1'(A_26, B_27)!=B_27 | k1_xboole_0=A_26 | k1_tarski(B_27)=A_26)), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.34/2.36  tff(c_5787, plain, (![B_14569]: (B_14569!='#skF_4'('#skF_9', k1_xboole_0) | k2_relat_1('#skF_9')=k1_xboole_0 | k2_relat_1('#skF_9')=k1_tarski(B_14569) | k2_relat_1('#skF_9')=k1_tarski(B_14569))), inference(superposition, [status(thm), theory('equality')], [c_5773, c_22])).
% 6.34/2.36  tff(c_5821, plain, (k1_tarski('#skF_4'('#skF_9', k1_xboole_0))=k2_relat_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_148, c_5787])).
% 6.34/2.36  tff(c_84, plain, (k1_tarski(k1_funct_1('#skF_9', '#skF_8'))!=k2_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.34/2.36  tff(c_4860, plain, (k1_tarski('#skF_4'('#skF_9', k1_xboole_0))!=k2_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_4854, c_84])).
% 6.34/2.36  tff(c_5825, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5821, c_4860])).
% 6.34/2.36  tff(c_5826, plain, (k1_relat_1('#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_147])).
% 6.34/2.36  tff(c_5828, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5826, c_86])).
% 6.34/2.36  tff(c_5882, plain, (![A_14662, B_14663, C_14664, D_14665]: (k3_enumset1(A_14662, A_14662, B_14663, C_14664, D_14665)=k2_enumset1(A_14662, B_14663, C_14664, D_14665))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.34/2.36  tff(c_36, plain, (![E_33, G_37, D_32, C_31, B_30]: (r2_hidden(G_37, k3_enumset1(G_37, B_30, C_31, D_32, E_33)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.34/2.36  tff(c_5915, plain, (![A_14671, B_14672, C_14673, D_14674]: (r2_hidden(A_14671, k2_enumset1(A_14671, B_14672, C_14673, D_14674)))), inference(superposition, [status(thm), theory('equality')], [c_5882, c_36])).
% 6.34/2.36  tff(c_5919, plain, (![A_14675, B_14676, C_14677]: (r2_hidden(A_14675, k1_enumset1(A_14675, B_14676, C_14677)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_5915])).
% 6.34/2.36  tff(c_5923, plain, (![A_14678, B_14679]: (r2_hidden(A_14678, k2_tarski(A_14678, B_14679)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_5919])).
% 6.34/2.36  tff(c_5927, plain, (![A_14680]: (r2_hidden(A_14680, k1_tarski(A_14680)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_5923])).
% 6.34/2.36  tff(c_5930, plain, (r2_hidden('#skF_8', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5828, c_5927])).
% 6.34/2.36  tff(c_5932, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_5930])).
% 6.34/2.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.34/2.36  
% 6.34/2.36  Inference rules
% 6.34/2.36  ----------------------
% 6.34/2.36  #Ref     : 2
% 6.34/2.36  #Sup     : 1191
% 6.34/2.36  #Fact    : 4
% 6.34/2.36  #Define  : 0
% 6.34/2.36  #Split   : 7
% 6.34/2.36  #Chain   : 0
% 6.34/2.36  #Close   : 0
% 6.34/2.36  
% 6.34/2.36  Ordering : KBO
% 6.34/2.36  
% 6.34/2.36  Simplification rules
% 6.34/2.36  ----------------------
% 6.34/2.36  #Subsume      : 196
% 6.34/2.36  #Demod        : 352
% 6.34/2.36  #Tautology    : 369
% 6.34/2.36  #SimpNegUnit  : 141
% 6.34/2.36  #BackRed      : 17
% 6.34/2.36  
% 6.34/2.36  #Partial instantiations: 5250
% 6.34/2.36  #Strategies tried      : 1
% 6.34/2.36  
% 6.34/2.36  Timing (in seconds)
% 6.34/2.36  ----------------------
% 6.34/2.36  Preprocessing        : 0.36
% 6.34/2.36  Parsing              : 0.18
% 6.34/2.36  CNF conversion       : 0.03
% 6.34/2.36  Main loop            : 1.13
% 6.34/2.36  Inferencing          : 0.44
% 6.34/2.36  Reduction            : 0.32
% 6.34/2.36  Demodulation         : 0.21
% 6.34/2.36  BG Simplification    : 0.06
% 6.34/2.36  Subsumption          : 0.24
% 6.34/2.36  Abstraction          : 0.07
% 6.34/2.36  MUC search           : 0.00
% 6.34/2.36  Cooper               : 0.00
% 6.34/2.36  Total                : 1.53
% 6.34/2.36  Index Insertion      : 0.00
% 6.34/2.36  Index Deletion       : 0.00
% 6.34/2.36  Index Matching       : 0.00
% 6.34/2.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
