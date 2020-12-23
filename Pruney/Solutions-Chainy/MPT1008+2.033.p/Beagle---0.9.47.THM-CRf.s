%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:30 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 126 expanded)
%              Number of leaves         :   52 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :  120 ( 197 expanded)
%              Number of equality atoms :   63 (  85 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_140,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_128,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

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

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_69,axiom,(
    ! [A,B,C,D,E,F,G,H,I] :
      ( I = k6_enumset1(A,B,C,D,E,F,G,H)
    <=> ! [J] :
          ( r2_hidden(J,I)
        <=> ~ ( J != A
              & J != B
              & J != C
              & J != D
              & J != E
              & J != F
              & J != G
              & J != H ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

tff(c_104,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_231,plain,(
    ! [A_158,B_159,C_160] :
      ( k2_relset_1(A_158,B_159,C_160) = k2_relat_1(C_160)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_235,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_104,c_231])).

tff(c_100,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') != k1_tarski(k1_funct_1('#skF_5','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_236,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_3')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_100])).

tff(c_127,plain,(
    ! [C_68,A_69,B_70] :
      ( v1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_131,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_104,c_127])).

tff(c_108,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_180,plain,(
    ! [A_84,B_85] :
      ( k9_relat_1(A_84,k1_tarski(B_85)) = k11_relat_1(A_84,B_85)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_146,plain,(
    ! [C_77,A_78,B_79] :
      ( v4_relat_1(C_77,A_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_150,plain,(
    v4_relat_1('#skF_5',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_104,c_146])).

tff(c_151,plain,(
    ! [B_80,A_81] :
      ( k7_relat_1(B_80,A_81) = B_80
      | ~ v4_relat_1(B_80,A_81)
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_154,plain,
    ( k7_relat_1('#skF_5',k1_tarski('#skF_3')) = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_150,c_151])).

tff(c_157,plain,(
    k7_relat_1('#skF_5',k1_tarski('#skF_3')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_154])).

tff(c_72,plain,(
    ! [B_45,A_44] :
      ( k2_relat_1(k7_relat_1(B_45,A_44)) = k9_relat_1(B_45,A_44)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_170,plain,
    ( k9_relat_1('#skF_5',k1_tarski('#skF_3')) = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_72])).

tff(c_174,plain,(
    k9_relat_1('#skF_5',k1_tarski('#skF_3')) = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_170])).

tff(c_186,plain,
    ( k11_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_174])).

tff(c_195,plain,(
    k11_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_186])).

tff(c_102,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_106,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_222,plain,(
    ! [A_155,B_156,C_157] :
      ( k1_relset_1(A_155,B_156,C_157) = k1_relat_1(C_157)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_226,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_104,c_222])).

tff(c_307,plain,(
    ! [B_197,A_198,C_199] :
      ( k1_xboole_0 = B_197
      | k1_relset_1(A_198,B_197,C_199) = A_198
      | ~ v1_funct_2(C_199,A_198,B_197)
      | ~ m1_subset_1(C_199,k1_zfmisc_1(k2_zfmisc_1(A_198,B_197))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_310,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_104,c_307])).

tff(c_313,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_226,c_310])).

tff(c_314,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_313])).

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

tff(c_10,plain,(
    ! [D_14,E_15,B_12,A_11,C_13] : k4_enumset1(A_11,A_11,B_12,C_13,D_14,E_15) = k3_enumset1(A_11,B_12,C_13,D_14,E_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [C_18,B_17,A_16,D_19,E_20,F_21] : k5_enumset1(A_16,A_16,B_17,C_18,D_19,E_20,F_21) = k4_enumset1(A_16,B_17,C_18,D_19,E_20,F_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_270,plain,(
    ! [D_188,G_187,B_189,E_185,C_184,A_183,F_186] : k6_enumset1(A_183,A_183,B_189,C_184,D_188,E_185,F_186,G_187) = k5_enumset1(A_183,B_189,C_184,D_188,E_185,F_186,G_187) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    ! [G_35,H_36,E_33,J_40,A_29,F_34,D_32,B_30] : r2_hidden(J_40,k6_enumset1(A_29,B_30,J_40,D_32,E_33,F_34,G_35,H_36)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_303,plain,(
    ! [C_196,G_194,A_191,B_192,F_190,D_193,E_195] : r2_hidden(B_192,k5_enumset1(A_191,B_192,C_196,D_193,E_195,F_190,G_194)) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_28])).

tff(c_460,plain,(
    ! [C_215,B_211,A_213,F_210,E_212,D_214] : r2_hidden(A_213,k4_enumset1(A_213,B_211,C_215,D_214,E_212,F_210)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_303])).

tff(c_464,plain,(
    ! [C_216,A_217,D_219,B_218,E_220] : r2_hidden(A_217,k3_enumset1(A_217,B_218,C_216,D_219,E_220)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_460])).

tff(c_468,plain,(
    ! [A_221,B_222,C_223,D_224] : r2_hidden(A_221,k2_enumset1(A_221,B_222,C_223,D_224)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_464])).

tff(c_472,plain,(
    ! [A_225,B_226,C_227] : r2_hidden(A_225,k1_enumset1(A_225,B_226,C_227)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_468])).

tff(c_477,plain,(
    ! [A_237,B_238] : r2_hidden(A_237,k2_tarski(A_237,B_238)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_472])).

tff(c_481,plain,(
    ! [A_239] : r2_hidden(A_239,k1_tarski(A_239)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_477])).

tff(c_484,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_481])).

tff(c_76,plain,(
    ! [B_49,A_48] :
      ( k1_tarski(k1_funct_1(B_49,A_48)) = k11_relat_1(B_49,A_48)
      | ~ r2_hidden(A_48,k1_relat_1(B_49))
      | ~ v1_funct_1(B_49)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_487,plain,
    ( k1_tarski(k1_funct_1('#skF_5','#skF_3')) = k11_relat_1('#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_484,c_76])).

tff(c_490,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_3')) = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_108,c_195,c_487])).

tff(c_492,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_490])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:03:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.46/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.47  
% 3.46/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.48  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.46/1.48  
% 3.46/1.48  %Foreground sorts:
% 3.46/1.48  
% 3.46/1.48  
% 3.46/1.48  %Background operators:
% 3.46/1.48  
% 3.46/1.48  
% 3.46/1.48  %Foreground operators:
% 3.46/1.48  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.46/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.46/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.46/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.46/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.46/1.48  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.46/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.46/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.46/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.46/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.46/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.46/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.46/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.46/1.48  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.46/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.46/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.46/1.48  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.46/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.46/1.48  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.46/1.48  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.46/1.48  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.46/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.46/1.48  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.46/1.48  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.46/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.46/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.46/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.46/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.46/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.46/1.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.46/1.48  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.46/1.48  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.46/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.46/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.46/1.48  
% 3.46/1.49  tff(f_140, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 3.46/1.49  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.46/1.49  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.46/1.49  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 3.46/1.49  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.46/1.49  tff(f_84, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.46/1.49  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.46/1.49  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.46/1.49  tff(f_128, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.46/1.49  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.46/1.49  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.46/1.49  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.46/1.49  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.46/1.49  tff(f_35, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.46/1.49  tff(f_37, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 3.46/1.49  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 3.46/1.49  tff(f_69, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_enumset1)).
% 3.46/1.49  tff(f_92, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 3.46/1.49  tff(c_104, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.46/1.49  tff(c_231, plain, (![A_158, B_159, C_160]: (k2_relset_1(A_158, B_159, C_160)=k2_relat_1(C_160) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.46/1.49  tff(c_235, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_104, c_231])).
% 3.46/1.49  tff(c_100, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')!=k1_tarski(k1_funct_1('#skF_5', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.46/1.49  tff(c_236, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_235, c_100])).
% 3.46/1.49  tff(c_127, plain, (![C_68, A_69, B_70]: (v1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.46/1.49  tff(c_131, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_104, c_127])).
% 3.46/1.49  tff(c_108, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.46/1.49  tff(c_180, plain, (![A_84, B_85]: (k9_relat_1(A_84, k1_tarski(B_85))=k11_relat_1(A_84, B_85) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.46/1.49  tff(c_146, plain, (![C_77, A_78, B_79]: (v4_relat_1(C_77, A_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.46/1.49  tff(c_150, plain, (v4_relat_1('#skF_5', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_104, c_146])).
% 3.46/1.49  tff(c_151, plain, (![B_80, A_81]: (k7_relat_1(B_80, A_81)=B_80 | ~v4_relat_1(B_80, A_81) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.46/1.49  tff(c_154, plain, (k7_relat_1('#skF_5', k1_tarski('#skF_3'))='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_150, c_151])).
% 3.46/1.49  tff(c_157, plain, (k7_relat_1('#skF_5', k1_tarski('#skF_3'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_131, c_154])).
% 3.46/1.49  tff(c_72, plain, (![B_45, A_44]: (k2_relat_1(k7_relat_1(B_45, A_44))=k9_relat_1(B_45, A_44) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.46/1.49  tff(c_170, plain, (k9_relat_1('#skF_5', k1_tarski('#skF_3'))=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_157, c_72])).
% 3.46/1.49  tff(c_174, plain, (k9_relat_1('#skF_5', k1_tarski('#skF_3'))=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_170])).
% 3.46/1.49  tff(c_186, plain, (k11_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_180, c_174])).
% 3.46/1.49  tff(c_195, plain, (k11_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_186])).
% 3.46/1.49  tff(c_102, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.46/1.49  tff(c_106, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.46/1.49  tff(c_222, plain, (![A_155, B_156, C_157]: (k1_relset_1(A_155, B_156, C_157)=k1_relat_1(C_157) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.46/1.49  tff(c_226, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_104, c_222])).
% 3.46/1.49  tff(c_307, plain, (![B_197, A_198, C_199]: (k1_xboole_0=B_197 | k1_relset_1(A_198, B_197, C_199)=A_198 | ~v1_funct_2(C_199, A_198, B_197) | ~m1_subset_1(C_199, k1_zfmisc_1(k2_zfmisc_1(A_198, B_197))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.46/1.49  tff(c_310, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_104, c_307])).
% 3.46/1.49  tff(c_313, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_226, c_310])).
% 3.46/1.49  tff(c_314, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_102, c_313])).
% 3.46/1.49  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.46/1.49  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.46/1.49  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.46/1.49  tff(c_8, plain, (![A_7, B_8, C_9, D_10]: (k3_enumset1(A_7, A_7, B_8, C_9, D_10)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.46/1.49  tff(c_10, plain, (![D_14, E_15, B_12, A_11, C_13]: (k4_enumset1(A_11, A_11, B_12, C_13, D_14, E_15)=k3_enumset1(A_11, B_12, C_13, D_14, E_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.46/1.49  tff(c_12, plain, (![C_18, B_17, A_16, D_19, E_20, F_21]: (k5_enumset1(A_16, A_16, B_17, C_18, D_19, E_20, F_21)=k4_enumset1(A_16, B_17, C_18, D_19, E_20, F_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.46/1.49  tff(c_270, plain, (![D_188, G_187, B_189, E_185, C_184, A_183, F_186]: (k6_enumset1(A_183, A_183, B_189, C_184, D_188, E_185, F_186, G_187)=k5_enumset1(A_183, B_189, C_184, D_188, E_185, F_186, G_187))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.46/1.49  tff(c_28, plain, (![G_35, H_36, E_33, J_40, A_29, F_34, D_32, B_30]: (r2_hidden(J_40, k6_enumset1(A_29, B_30, J_40, D_32, E_33, F_34, G_35, H_36)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.46/1.49  tff(c_303, plain, (![C_196, G_194, A_191, B_192, F_190, D_193, E_195]: (r2_hidden(B_192, k5_enumset1(A_191, B_192, C_196, D_193, E_195, F_190, G_194)))), inference(superposition, [status(thm), theory('equality')], [c_270, c_28])).
% 3.46/1.49  tff(c_460, plain, (![C_215, B_211, A_213, F_210, E_212, D_214]: (r2_hidden(A_213, k4_enumset1(A_213, B_211, C_215, D_214, E_212, F_210)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_303])).
% 3.46/1.49  tff(c_464, plain, (![C_216, A_217, D_219, B_218, E_220]: (r2_hidden(A_217, k3_enumset1(A_217, B_218, C_216, D_219, E_220)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_460])).
% 3.46/1.49  tff(c_468, plain, (![A_221, B_222, C_223, D_224]: (r2_hidden(A_221, k2_enumset1(A_221, B_222, C_223, D_224)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_464])).
% 3.46/1.49  tff(c_472, plain, (![A_225, B_226, C_227]: (r2_hidden(A_225, k1_enumset1(A_225, B_226, C_227)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_468])).
% 3.46/1.49  tff(c_477, plain, (![A_237, B_238]: (r2_hidden(A_237, k2_tarski(A_237, B_238)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_472])).
% 3.46/1.49  tff(c_481, plain, (![A_239]: (r2_hidden(A_239, k1_tarski(A_239)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_477])).
% 3.46/1.49  tff(c_484, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_314, c_481])).
% 3.46/1.49  tff(c_76, plain, (![B_49, A_48]: (k1_tarski(k1_funct_1(B_49, A_48))=k11_relat_1(B_49, A_48) | ~r2_hidden(A_48, k1_relat_1(B_49)) | ~v1_funct_1(B_49) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.46/1.49  tff(c_487, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))=k11_relat_1('#skF_5', '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_484, c_76])).
% 3.46/1.49  tff(c_490, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_108, c_195, c_487])).
% 3.46/1.49  tff(c_492, plain, $false, inference(negUnitSimplification, [status(thm)], [c_236, c_490])).
% 3.46/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.49  
% 3.46/1.49  Inference rules
% 3.46/1.49  ----------------------
% 3.46/1.49  #Ref     : 0
% 3.46/1.49  #Sup     : 88
% 3.46/1.49  #Fact    : 0
% 3.46/1.49  #Define  : 0
% 3.46/1.49  #Split   : 0
% 3.46/1.49  #Chain   : 0
% 3.46/1.49  #Close   : 0
% 3.46/1.49  
% 3.46/1.49  Ordering : KBO
% 3.46/1.49  
% 3.46/1.49  Simplification rules
% 3.46/1.49  ----------------------
% 3.46/1.49  #Subsume      : 0
% 3.46/1.49  #Demod        : 36
% 3.46/1.49  #Tautology    : 61
% 3.46/1.49  #SimpNegUnit  : 5
% 3.46/1.49  #BackRed      : 8
% 3.46/1.49  
% 3.46/1.49  #Partial instantiations: 0
% 3.46/1.49  #Strategies tried      : 1
% 3.46/1.49  
% 3.46/1.49  Timing (in seconds)
% 3.46/1.49  ----------------------
% 3.46/1.50  Preprocessing        : 0.40
% 3.46/1.50  Parsing              : 0.19
% 3.46/1.50  CNF conversion       : 0.03
% 3.46/1.50  Main loop            : 0.33
% 3.46/1.50  Inferencing          : 0.10
% 3.46/1.50  Reduction            : 0.10
% 3.46/1.50  Demodulation         : 0.07
% 3.46/1.50  BG Simplification    : 0.03
% 3.46/1.50  Subsumption          : 0.09
% 3.46/1.50  Abstraction          : 0.02
% 3.46/1.50  MUC search           : 0.00
% 3.46/1.50  Cooper               : 0.00
% 3.46/1.50  Total                : 0.77
% 3.46/1.50  Index Insertion      : 0.00
% 3.46/1.50  Index Deletion       : 0.00
% 3.46/1.50  Index Matching       : 0.00
% 3.62/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
