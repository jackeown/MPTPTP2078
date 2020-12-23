%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:39 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 146 expanded)
%              Number of leaves         :   49 (  72 expanded)
%              Depth                    :   11
%              Number of atoms          :  118 ( 275 expanded)
%              Number of equality atoms :   57 ( 125 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_136,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_78,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_124,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k2_relat_1(k7_relat_1(B,k1_tarski(A))) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_funct_1)).

tff(c_102,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_180,plain,(
    ! [A_148,B_149,C_150] :
      ( k2_relset_1(A_148,B_149,C_150) = k2_relat_1(C_150)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_184,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_102,c_180])).

tff(c_98,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') != k1_tarski(k1_funct_1('#skF_5','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_185,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_3')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_98])).

tff(c_72,plain,(
    ! [A_44,B_45] : v1_relat_1(k2_zfmisc_1(A_44,B_45)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_126,plain,(
    ! [B_67,A_68] :
      ( v1_relat_1(B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_68))
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_129,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_102,c_126])).

tff(c_132,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_129])).

tff(c_106,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_100,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_104,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_190,plain,(
    ! [A_151,B_152,C_153] :
      ( k1_relset_1(A_151,B_152,C_153) = k1_relat_1(C_153)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_194,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_102,c_190])).

tff(c_285,plain,(
    ! [B_209,A_210,C_211] :
      ( k1_xboole_0 = B_209
      | k1_relset_1(A_210,B_209,C_211) = A_210
      | ~ v1_funct_2(C_211,A_210,B_209)
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(A_210,B_209))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_288,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_285])).

tff(c_291,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_194,c_288])).

tff(c_292,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_291])).

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

tff(c_221,plain,(
    ! [D_177,G_176,B_178,E_174,C_173,A_172,F_175] : k6_enumset1(A_172,A_172,B_178,C_173,D_177,E_174,F_175,G_176) = k5_enumset1(A_172,B_178,C_173,D_177,E_174,F_175,G_176) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [H_36,E_33,J_40,A_29,F_34,D_32,C_31,B_30] : r2_hidden(J_40,k6_enumset1(A_29,B_30,C_31,D_32,E_33,F_34,J_40,H_36)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_254,plain,(
    ! [F_185,D_181,G_183,C_180,B_182,A_184,E_179] : r2_hidden(F_185,k5_enumset1(A_184,B_182,C_180,D_181,E_179,F_185,G_183)) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_20])).

tff(c_265,plain,(
    ! [E_191,F_189,D_193,C_194,B_190,A_192] : r2_hidden(E_191,k4_enumset1(A_192,B_190,C_194,D_193,E_191,F_189)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_254])).

tff(c_269,plain,(
    ! [C_195,E_199,D_198,B_197,A_196] : r2_hidden(D_198,k3_enumset1(A_196,B_197,C_195,D_198,E_199)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_265])).

tff(c_273,plain,(
    ! [C_200,A_201,B_202,D_203] : r2_hidden(C_200,k2_enumset1(A_201,B_202,C_200,D_203)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_269])).

tff(c_277,plain,(
    ! [B_204,A_205,C_206] : r2_hidden(B_204,k1_enumset1(A_205,B_204,C_206)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_273])).

tff(c_281,plain,(
    ! [A_207,B_208] : r2_hidden(A_207,k2_tarski(A_207,B_208)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_277])).

tff(c_309,plain,(
    ! [A_212] : r2_hidden(A_212,k1_tarski(A_212)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_281])).

tff(c_312,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_309])).

tff(c_134,plain,(
    ! [C_71,A_72,B_73] :
      ( v4_relat_1(C_71,A_72)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_138,plain,(
    v4_relat_1('#skF_5',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_102,c_134])).

tff(c_74,plain,(
    ! [B_47,A_46] :
      ( k7_relat_1(B_47,A_46) = B_47
      | ~ v4_relat_1(B_47,A_46)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_141,plain,
    ( k7_relat_1('#skF_5',k1_tarski('#skF_3')) = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_138,c_74])).

tff(c_144,plain,(
    k7_relat_1('#skF_5',k1_tarski('#skF_3')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_141])).

tff(c_295,plain,(
    k7_relat_1('#skF_5',k1_relat_1('#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_144])).

tff(c_326,plain,(
    ! [B_213,A_214] :
      ( k2_relat_1(k7_relat_1(B_213,k1_tarski(A_214))) = k1_tarski(k1_funct_1(B_213,A_214))
      | ~ r2_hidden(A_214,k1_relat_1(B_213))
      | ~ v1_funct_1(B_213)
      | ~ v1_relat_1(B_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_386,plain,(
    ! [B_228] :
      ( k2_relat_1(k7_relat_1(B_228,k1_relat_1('#skF_5'))) = k1_tarski(k1_funct_1(B_228,'#skF_3'))
      | ~ r2_hidden('#skF_3',k1_relat_1(B_228))
      | ~ v1_funct_1(B_228)
      | ~ v1_relat_1(B_228) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_326])).

tff(c_395,plain,
    ( k1_tarski(k1_funct_1('#skF_5','#skF_3')) = k2_relat_1('#skF_5')
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_386])).

tff(c_399,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_3')) = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_106,c_312,c_395])).

tff(c_401,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_185,c_399])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:43:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.37  
% 3.12/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.37  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.12/1.37  
% 3.12/1.37  %Foreground sorts:
% 3.12/1.37  
% 3.12/1.37  
% 3.12/1.37  %Background operators:
% 3.12/1.37  
% 3.12/1.37  
% 3.12/1.37  %Foreground operators:
% 3.12/1.37  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.12/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.12/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.12/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.12/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.12/1.37  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.12/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.12/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.12/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.12/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.12/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.12/1.37  tff('#skF_5', type, '#skF_5': $i).
% 3.12/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.12/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.12/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.12/1.37  tff('#skF_3', type, '#skF_3': $i).
% 3.12/1.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.12/1.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.12/1.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.12/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.12/1.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.12/1.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.12/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.12/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.12/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.12/1.37  tff('#skF_4', type, '#skF_4': $i).
% 3.12/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.12/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.12/1.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.12/1.37  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.12/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.12/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.12/1.37  
% 3.12/1.39  tff(f_136, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 3.12/1.39  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.12/1.39  tff(f_78, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.12/1.39  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.12/1.39  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.12/1.39  tff(f_124, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.12/1.39  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.12/1.39  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.12/1.39  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.12/1.39  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.12/1.39  tff(f_35, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 3.12/1.39  tff(f_37, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 3.12/1.39  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 3.12/1.39  tff(f_69, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 3.12/1.39  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.12/1.39  tff(f_84, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.12/1.39  tff(f_92, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k2_relat_1(k7_relat_1(B, k1_tarski(A))) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_funct_1)).
% 3.12/1.39  tff(c_102, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.12/1.39  tff(c_180, plain, (![A_148, B_149, C_150]: (k2_relset_1(A_148, B_149, C_150)=k2_relat_1(C_150) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.12/1.39  tff(c_184, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_102, c_180])).
% 3.12/1.39  tff(c_98, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')!=k1_tarski(k1_funct_1('#skF_5', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.12/1.39  tff(c_185, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_184, c_98])).
% 3.12/1.39  tff(c_72, plain, (![A_44, B_45]: (v1_relat_1(k2_zfmisc_1(A_44, B_45)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.12/1.39  tff(c_126, plain, (![B_67, A_68]: (v1_relat_1(B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(A_68)) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.12/1.39  tff(c_129, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_102, c_126])).
% 3.12/1.39  tff(c_132, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_129])).
% 3.12/1.39  tff(c_106, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.12/1.39  tff(c_100, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.12/1.39  tff(c_104, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.12/1.39  tff(c_190, plain, (![A_151, B_152, C_153]: (k1_relset_1(A_151, B_152, C_153)=k1_relat_1(C_153) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.12/1.39  tff(c_194, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_102, c_190])).
% 3.12/1.39  tff(c_285, plain, (![B_209, A_210, C_211]: (k1_xboole_0=B_209 | k1_relset_1(A_210, B_209, C_211)=A_210 | ~v1_funct_2(C_211, A_210, B_209) | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(A_210, B_209))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.12/1.39  tff(c_288, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_102, c_285])).
% 3.12/1.39  tff(c_291, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_194, c_288])).
% 3.12/1.39  tff(c_292, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_100, c_291])).
% 3.12/1.39  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.12/1.39  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.12/1.39  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.12/1.39  tff(c_8, plain, (![A_7, B_8, C_9, D_10]: (k3_enumset1(A_7, A_7, B_8, C_9, D_10)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.12/1.39  tff(c_10, plain, (![D_14, E_15, B_12, A_11, C_13]: (k4_enumset1(A_11, A_11, B_12, C_13, D_14, E_15)=k3_enumset1(A_11, B_12, C_13, D_14, E_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.12/1.39  tff(c_12, plain, (![C_18, B_17, A_16, D_19, E_20, F_21]: (k5_enumset1(A_16, A_16, B_17, C_18, D_19, E_20, F_21)=k4_enumset1(A_16, B_17, C_18, D_19, E_20, F_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.12/1.39  tff(c_221, plain, (![D_177, G_176, B_178, E_174, C_173, A_172, F_175]: (k6_enumset1(A_172, A_172, B_178, C_173, D_177, E_174, F_175, G_176)=k5_enumset1(A_172, B_178, C_173, D_177, E_174, F_175, G_176))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.12/1.39  tff(c_20, plain, (![H_36, E_33, J_40, A_29, F_34, D_32, C_31, B_30]: (r2_hidden(J_40, k6_enumset1(A_29, B_30, C_31, D_32, E_33, F_34, J_40, H_36)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.12/1.39  tff(c_254, plain, (![F_185, D_181, G_183, C_180, B_182, A_184, E_179]: (r2_hidden(F_185, k5_enumset1(A_184, B_182, C_180, D_181, E_179, F_185, G_183)))), inference(superposition, [status(thm), theory('equality')], [c_221, c_20])).
% 3.12/1.39  tff(c_265, plain, (![E_191, F_189, D_193, C_194, B_190, A_192]: (r2_hidden(E_191, k4_enumset1(A_192, B_190, C_194, D_193, E_191, F_189)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_254])).
% 3.12/1.39  tff(c_269, plain, (![C_195, E_199, D_198, B_197, A_196]: (r2_hidden(D_198, k3_enumset1(A_196, B_197, C_195, D_198, E_199)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_265])).
% 3.12/1.39  tff(c_273, plain, (![C_200, A_201, B_202, D_203]: (r2_hidden(C_200, k2_enumset1(A_201, B_202, C_200, D_203)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_269])).
% 3.12/1.39  tff(c_277, plain, (![B_204, A_205, C_206]: (r2_hidden(B_204, k1_enumset1(A_205, B_204, C_206)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_273])).
% 3.12/1.39  tff(c_281, plain, (![A_207, B_208]: (r2_hidden(A_207, k2_tarski(A_207, B_208)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_277])).
% 3.12/1.39  tff(c_309, plain, (![A_212]: (r2_hidden(A_212, k1_tarski(A_212)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_281])).
% 3.12/1.39  tff(c_312, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_292, c_309])).
% 3.12/1.39  tff(c_134, plain, (![C_71, A_72, B_73]: (v4_relat_1(C_71, A_72) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.12/1.39  tff(c_138, plain, (v4_relat_1('#skF_5', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_102, c_134])).
% 3.12/1.39  tff(c_74, plain, (![B_47, A_46]: (k7_relat_1(B_47, A_46)=B_47 | ~v4_relat_1(B_47, A_46) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.12/1.39  tff(c_141, plain, (k7_relat_1('#skF_5', k1_tarski('#skF_3'))='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_138, c_74])).
% 3.12/1.39  tff(c_144, plain, (k7_relat_1('#skF_5', k1_tarski('#skF_3'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_141])).
% 3.12/1.39  tff(c_295, plain, (k7_relat_1('#skF_5', k1_relat_1('#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_292, c_144])).
% 3.12/1.39  tff(c_326, plain, (![B_213, A_214]: (k2_relat_1(k7_relat_1(B_213, k1_tarski(A_214)))=k1_tarski(k1_funct_1(B_213, A_214)) | ~r2_hidden(A_214, k1_relat_1(B_213)) | ~v1_funct_1(B_213) | ~v1_relat_1(B_213))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.12/1.39  tff(c_386, plain, (![B_228]: (k2_relat_1(k7_relat_1(B_228, k1_relat_1('#skF_5')))=k1_tarski(k1_funct_1(B_228, '#skF_3')) | ~r2_hidden('#skF_3', k1_relat_1(B_228)) | ~v1_funct_1(B_228) | ~v1_relat_1(B_228))), inference(superposition, [status(thm), theory('equality')], [c_292, c_326])).
% 3.12/1.39  tff(c_395, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))=k2_relat_1('#skF_5') | ~r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_295, c_386])).
% 3.12/1.39  tff(c_399, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_106, c_312, c_395])).
% 3.12/1.39  tff(c_401, plain, $false, inference(negUnitSimplification, [status(thm)], [c_185, c_399])).
% 3.12/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.39  
% 3.12/1.39  Inference rules
% 3.12/1.39  ----------------------
% 3.12/1.39  #Ref     : 0
% 3.12/1.39  #Sup     : 67
% 3.12/1.39  #Fact    : 0
% 3.12/1.39  #Define  : 0
% 3.12/1.39  #Split   : 0
% 3.12/1.39  #Chain   : 0
% 3.12/1.39  #Close   : 0
% 3.12/1.39  
% 3.12/1.39  Ordering : KBO
% 3.12/1.39  
% 3.12/1.39  Simplification rules
% 3.12/1.39  ----------------------
% 3.12/1.39  #Subsume      : 0
% 3.12/1.39  #Demod        : 28
% 3.12/1.39  #Tautology    : 41
% 3.12/1.39  #SimpNegUnit  : 5
% 3.12/1.39  #BackRed      : 7
% 3.12/1.39  
% 3.12/1.39  #Partial instantiations: 0
% 3.12/1.39  #Strategies tried      : 1
% 3.12/1.39  
% 3.12/1.39  Timing (in seconds)
% 3.12/1.39  ----------------------
% 3.12/1.39  Preprocessing        : 0.37
% 3.12/1.39  Parsing              : 0.18
% 3.12/1.39  CNF conversion       : 0.03
% 3.12/1.39  Main loop            : 0.29
% 3.12/1.39  Inferencing          : 0.08
% 3.12/1.39  Reduction            : 0.09
% 3.12/1.39  Demodulation         : 0.06
% 3.12/1.39  BG Simplification    : 0.03
% 3.12/1.39  Subsumption          : 0.08
% 3.12/1.39  Abstraction          : 0.02
% 3.12/1.39  MUC search           : 0.00
% 3.12/1.39  Cooper               : 0.00
% 3.12/1.39  Total                : 0.70
% 3.12/1.39  Index Insertion      : 0.00
% 3.12/1.39  Index Deletion       : 0.00
% 3.12/1.39  Index Matching       : 0.00
% 3.12/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
