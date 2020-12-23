%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:41 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 120 expanded)
%              Number of leaves         :   46 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :  107 ( 210 expanded)
%              Number of equality atoms :   54 (  95 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_98,axiom,(
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

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_116,axiom,(
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

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k2_relat_1(k7_relat_1(B,k1_tarski(A))) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_funct_1)).

tff(c_98,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_165,plain,(
    ! [A_138,B_139,C_140] :
      ( k2_relset_1(A_138,B_139,C_140) = k2_relat_1(C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_169,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_98,c_165])).

tff(c_94,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') != k1_tarski(k1_funct_1('#skF_5','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_170,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_3')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_94])).

tff(c_72,plain,(
    ! [A_44,B_45] : v1_relat_1(k2_zfmisc_1(A_44,B_45)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_131,plain,(
    ! [B_64,A_65] :
      ( v1_relat_1(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65))
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_134,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_98,c_131])).

tff(c_137,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_134])).

tff(c_102,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_96,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_100,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_175,plain,(
    ! [A_141,B_142,C_143] :
      ( k1_relset_1(A_141,B_142,C_143) = k1_relat_1(C_143)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_179,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_98,c_175])).

tff(c_205,plain,(
    ! [B_161,A_162,C_163] :
      ( k1_xboole_0 = B_161
      | k1_relset_1(A_162,B_161,C_163) = A_162
      | ~ v1_funct_2(C_163,A_162,B_161)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_162,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_208,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_98,c_205])).

tff(c_211,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_179,c_208])).

tff(c_212,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_211])).

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

tff(c_260,plain,(
    ! [F_170,A_167,D_172,E_169,G_171,C_168,B_173] : k6_enumset1(A_167,A_167,B_173,C_168,D_172,E_169,F_170,G_171) = k5_enumset1(A_167,B_173,C_168,D_172,E_169,F_170,G_171) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    ! [G_35,H_36,E_33,J_40,A_29,F_34,D_32,B_30] : r2_hidden(J_40,k6_enumset1(A_29,B_30,J_40,D_32,E_33,F_34,G_35,H_36)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_293,plain,(
    ! [B_177,E_178,F_176,G_175,D_174,A_180,C_179] : r2_hidden(B_177,k5_enumset1(A_180,B_177,C_179,D_174,E_178,F_176,G_175)) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_28])).

tff(c_297,plain,(
    ! [F_181,B_182,D_185,C_186,E_183,A_184] : r2_hidden(A_184,k4_enumset1(A_184,B_182,C_186,D_185,E_183,F_181)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_293])).

tff(c_301,plain,(
    ! [C_187,E_191,B_189,A_188,D_190] : r2_hidden(A_188,k3_enumset1(A_188,B_189,C_187,D_190,E_191)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_297])).

tff(c_305,plain,(
    ! [A_192,B_193,C_194,D_195] : r2_hidden(A_192,k2_enumset1(A_192,B_193,C_194,D_195)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_301])).

tff(c_321,plain,(
    ! [A_198,B_199,C_200] : r2_hidden(A_198,k1_enumset1(A_198,B_199,C_200)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_305])).

tff(c_325,plain,(
    ! [A_201,B_202] : r2_hidden(A_201,k2_tarski(A_201,B_202)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_321])).

tff(c_329,plain,(
    ! [A_203] : r2_hidden(A_203,k1_tarski(A_203)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_325])).

tff(c_332,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_329])).

tff(c_74,plain,(
    ! [A_46] :
      ( k7_relat_1(A_46,k1_relat_1(A_46)) = A_46
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_309,plain,(
    ! [B_196,A_197] :
      ( k2_relat_1(k7_relat_1(B_196,k1_tarski(A_197))) = k1_tarski(k1_funct_1(B_196,A_197))
      | ~ r2_hidden(A_197,k1_relat_1(B_196))
      | ~ v1_funct_1(B_196)
      | ~ v1_relat_1(B_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_412,plain,(
    ! [B_258] :
      ( k2_relat_1(k7_relat_1(B_258,k1_relat_1('#skF_5'))) = k1_tarski(k1_funct_1(B_258,'#skF_3'))
      | ~ r2_hidden('#skF_3',k1_relat_1(B_258))
      | ~ v1_funct_1(B_258)
      | ~ v1_relat_1(B_258) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_309])).

tff(c_422,plain,
    ( k1_tarski(k1_funct_1('#skF_5','#skF_3')) = k2_relat_1('#skF_5')
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_412])).

tff(c_426,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_3')) = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_137,c_102,c_332,c_422])).

tff(c_428,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_426])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:48:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.36/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.51  
% 3.36/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.51  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.36/1.51  
% 3.36/1.51  %Foreground sorts:
% 3.36/1.51  
% 3.36/1.51  
% 3.36/1.51  %Background operators:
% 3.36/1.51  
% 3.36/1.51  
% 3.36/1.51  %Foreground operators:
% 3.36/1.51  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.36/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.36/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.36/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.36/1.51  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.36/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.36/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.36/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.36/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.36/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.36/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.36/1.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.36/1.51  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.36/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.36/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.36/1.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.36/1.51  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.36/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.36/1.51  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.36/1.51  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.36/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.36/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.36/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.36/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.51  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.36/1.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.36/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.36/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.36/1.51  
% 3.51/1.53  tff(f_128, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 3.51/1.53  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.51/1.53  tff(f_78, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.51/1.53  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.51/1.53  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.51/1.53  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.51/1.53  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.51/1.53  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.51/1.53  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.51/1.53  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.51/1.53  tff(f_35, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 3.51/1.53  tff(f_37, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 3.51/1.53  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 3.51/1.53  tff(f_69, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 3.51/1.53  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 3.51/1.53  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k2_relat_1(k7_relat_1(B, k1_tarski(A))) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_funct_1)).
% 3.51/1.53  tff(c_98, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.51/1.53  tff(c_165, plain, (![A_138, B_139, C_140]: (k2_relset_1(A_138, B_139, C_140)=k2_relat_1(C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.51/1.53  tff(c_169, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_98, c_165])).
% 3.51/1.53  tff(c_94, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')!=k1_tarski(k1_funct_1('#skF_5', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.51/1.53  tff(c_170, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_94])).
% 3.51/1.53  tff(c_72, plain, (![A_44, B_45]: (v1_relat_1(k2_zfmisc_1(A_44, B_45)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.51/1.53  tff(c_131, plain, (![B_64, A_65]: (v1_relat_1(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.51/1.53  tff(c_134, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_98, c_131])).
% 3.51/1.53  tff(c_137, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_134])).
% 3.51/1.53  tff(c_102, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.51/1.53  tff(c_96, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.51/1.53  tff(c_100, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.51/1.53  tff(c_175, plain, (![A_141, B_142, C_143]: (k1_relset_1(A_141, B_142, C_143)=k1_relat_1(C_143) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.51/1.53  tff(c_179, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_98, c_175])).
% 3.51/1.53  tff(c_205, plain, (![B_161, A_162, C_163]: (k1_xboole_0=B_161 | k1_relset_1(A_162, B_161, C_163)=A_162 | ~v1_funct_2(C_163, A_162, B_161) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_162, B_161))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.51/1.53  tff(c_208, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_98, c_205])).
% 3.51/1.53  tff(c_211, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_179, c_208])).
% 3.51/1.53  tff(c_212, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_96, c_211])).
% 3.51/1.53  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.51/1.53  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.51/1.53  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.51/1.53  tff(c_8, plain, (![A_7, B_8, C_9, D_10]: (k3_enumset1(A_7, A_7, B_8, C_9, D_10)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.51/1.53  tff(c_10, plain, (![D_14, E_15, B_12, A_11, C_13]: (k4_enumset1(A_11, A_11, B_12, C_13, D_14, E_15)=k3_enumset1(A_11, B_12, C_13, D_14, E_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.51/1.53  tff(c_12, plain, (![C_18, B_17, A_16, D_19, E_20, F_21]: (k5_enumset1(A_16, A_16, B_17, C_18, D_19, E_20, F_21)=k4_enumset1(A_16, B_17, C_18, D_19, E_20, F_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.51/1.53  tff(c_260, plain, (![F_170, A_167, D_172, E_169, G_171, C_168, B_173]: (k6_enumset1(A_167, A_167, B_173, C_168, D_172, E_169, F_170, G_171)=k5_enumset1(A_167, B_173, C_168, D_172, E_169, F_170, G_171))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.51/1.53  tff(c_28, plain, (![G_35, H_36, E_33, J_40, A_29, F_34, D_32, B_30]: (r2_hidden(J_40, k6_enumset1(A_29, B_30, J_40, D_32, E_33, F_34, G_35, H_36)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.51/1.53  tff(c_293, plain, (![B_177, E_178, F_176, G_175, D_174, A_180, C_179]: (r2_hidden(B_177, k5_enumset1(A_180, B_177, C_179, D_174, E_178, F_176, G_175)))), inference(superposition, [status(thm), theory('equality')], [c_260, c_28])).
% 3.51/1.53  tff(c_297, plain, (![F_181, B_182, D_185, C_186, E_183, A_184]: (r2_hidden(A_184, k4_enumset1(A_184, B_182, C_186, D_185, E_183, F_181)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_293])).
% 3.51/1.53  tff(c_301, plain, (![C_187, E_191, B_189, A_188, D_190]: (r2_hidden(A_188, k3_enumset1(A_188, B_189, C_187, D_190, E_191)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_297])).
% 3.51/1.53  tff(c_305, plain, (![A_192, B_193, C_194, D_195]: (r2_hidden(A_192, k2_enumset1(A_192, B_193, C_194, D_195)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_301])).
% 3.51/1.53  tff(c_321, plain, (![A_198, B_199, C_200]: (r2_hidden(A_198, k1_enumset1(A_198, B_199, C_200)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_305])).
% 3.51/1.53  tff(c_325, plain, (![A_201, B_202]: (r2_hidden(A_201, k2_tarski(A_201, B_202)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_321])).
% 3.51/1.53  tff(c_329, plain, (![A_203]: (r2_hidden(A_203, k1_tarski(A_203)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_325])).
% 3.51/1.53  tff(c_332, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_212, c_329])).
% 3.51/1.53  tff(c_74, plain, (![A_46]: (k7_relat_1(A_46, k1_relat_1(A_46))=A_46 | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.51/1.53  tff(c_309, plain, (![B_196, A_197]: (k2_relat_1(k7_relat_1(B_196, k1_tarski(A_197)))=k1_tarski(k1_funct_1(B_196, A_197)) | ~r2_hidden(A_197, k1_relat_1(B_196)) | ~v1_funct_1(B_196) | ~v1_relat_1(B_196))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.51/1.53  tff(c_412, plain, (![B_258]: (k2_relat_1(k7_relat_1(B_258, k1_relat_1('#skF_5')))=k1_tarski(k1_funct_1(B_258, '#skF_3')) | ~r2_hidden('#skF_3', k1_relat_1(B_258)) | ~v1_funct_1(B_258) | ~v1_relat_1(B_258))), inference(superposition, [status(thm), theory('equality')], [c_212, c_309])).
% 3.51/1.53  tff(c_422, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))=k2_relat_1('#skF_5') | ~r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_74, c_412])).
% 3.51/1.53  tff(c_426, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_137, c_102, c_332, c_422])).
% 3.51/1.53  tff(c_428, plain, $false, inference(negUnitSimplification, [status(thm)], [c_170, c_426])).
% 3.51/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/1.53  
% 3.51/1.53  Inference rules
% 3.51/1.53  ----------------------
% 3.51/1.53  #Ref     : 0
% 3.51/1.53  #Sup     : 73
% 3.51/1.53  #Fact    : 0
% 3.51/1.53  #Define  : 0
% 3.51/1.53  #Split   : 0
% 3.51/1.53  #Chain   : 0
% 3.51/1.53  #Close   : 0
% 3.51/1.53  
% 3.51/1.53  Ordering : KBO
% 3.51/1.53  
% 3.51/1.53  Simplification rules
% 3.51/1.53  ----------------------
% 3.51/1.53  #Subsume      : 0
% 3.51/1.53  #Demod        : 23
% 3.51/1.53  #Tautology    : 46
% 3.51/1.53  #SimpNegUnit  : 4
% 3.51/1.53  #BackRed      : 5
% 3.51/1.53  
% 3.51/1.53  #Partial instantiations: 0
% 3.51/1.53  #Strategies tried      : 1
% 3.51/1.53  
% 3.51/1.53  Timing (in seconds)
% 3.51/1.53  ----------------------
% 3.51/1.53  Preprocessing        : 0.39
% 3.51/1.53  Parsing              : 0.19
% 3.51/1.53  CNF conversion       : 0.03
% 3.51/1.53  Main loop            : 0.35
% 3.51/1.53  Inferencing          : 0.10
% 3.51/1.53  Reduction            : 0.10
% 3.51/1.53  Demodulation         : 0.07
% 3.51/1.53  BG Simplification    : 0.02
% 3.51/1.53  Subsumption          : 0.11
% 3.51/1.53  Abstraction          : 0.02
% 3.51/1.53  MUC search           : 0.00
% 3.51/1.53  Cooper               : 0.00
% 3.51/1.53  Total                : 0.78
% 3.51/1.53  Index Insertion      : 0.00
% 3.51/1.53  Index Deletion       : 0.00
% 3.51/1.53  Index Matching       : 0.00
% 3.51/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
