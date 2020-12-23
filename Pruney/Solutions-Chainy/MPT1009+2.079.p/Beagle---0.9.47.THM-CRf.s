%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:53 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 130 expanded)
%              Number of leaves         :   39 (  64 expanded)
%              Depth                    :   10
%              Number of atoms          :  114 ( 254 expanded)
%              Number of equality atoms :   31 (  57 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_99,axiom,(
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

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_99,plain,(
    ! [C_65,A_66,B_67] :
      ( v1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_107,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_99])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_826,plain,(
    ! [C_220,A_221,B_222] :
      ( m1_subset_1(C_220,k1_zfmisc_1(k2_zfmisc_1(A_221,B_222)))
      | ~ r1_tarski(k2_relat_1(C_220),B_222)
      | ~ r1_tarski(k1_relat_1(C_220),A_221)
      | ~ v1_relat_1(C_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_22,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | ~ m1_subset_1(A_31,k1_zfmisc_1(B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_865,plain,(
    ! [C_223,A_224,B_225] :
      ( r1_tarski(C_223,k2_zfmisc_1(A_224,B_225))
      | ~ r1_tarski(k2_relat_1(C_223),B_225)
      | ~ r1_tarski(k1_relat_1(C_223),A_224)
      | ~ v1_relat_1(C_223) ) ),
    inference(resolution,[status(thm)],[c_826,c_22])).

tff(c_869,plain,(
    ! [C_223,A_224] :
      ( r1_tarski(C_223,k2_zfmisc_1(A_224,k2_relat_1(C_223)))
      | ~ r1_tarski(k1_relat_1(C_223),A_224)
      | ~ v1_relat_1(C_223) ) ),
    inference(resolution,[status(thm)],[c_6,c_865])).

tff(c_870,plain,(
    ! [C_226,A_227] :
      ( r1_tarski(C_226,k2_zfmisc_1(A_227,k2_relat_1(C_226)))
      | ~ r1_tarski(k1_relat_1(C_226),A_227)
      | ~ v1_relat_1(C_226) ) ),
    inference(resolution,[status(thm)],[c_6,c_865])).

tff(c_24,plain,(
    ! [A_31,B_32] :
      ( m1_subset_1(A_31,k1_zfmisc_1(B_32))
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_189,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( k7_relset_1(A_95,B_96,C_97,D_98) = k9_relat_1(C_97,D_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_196,plain,(
    ! [A_95,B_96,A_31,D_98] :
      ( k7_relset_1(A_95,B_96,A_31,D_98) = k9_relat_1(A_31,D_98)
      | ~ r1_tarski(A_31,k2_zfmisc_1(A_95,B_96)) ) ),
    inference(resolution,[status(thm)],[c_24,c_189])).

tff(c_917,plain,(
    ! [A_231,C_232,D_233] :
      ( k7_relset_1(A_231,k2_relat_1(C_232),C_232,D_233) = k9_relat_1(C_232,D_233)
      | ~ r1_tarski(k1_relat_1(C_232),A_231)
      | ~ v1_relat_1(C_232) ) ),
    inference(resolution,[status(thm)],[c_870,c_196])).

tff(c_935,plain,(
    ! [C_241,D_242] :
      ( k7_relset_1(k1_relat_1(C_241),k2_relat_1(C_241),C_241,D_242) = k9_relat_1(C_241,D_242)
      | ~ v1_relat_1(C_241) ) ),
    inference(resolution,[status(thm)],[c_6,c_917])).

tff(c_588,plain,(
    ! [A_173,B_174,C_175,D_176] :
      ( m1_subset_1(k7_relset_1(A_173,B_174,C_175,D_176),k1_zfmisc_1(B_174))
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_675,plain,(
    ! [A_183,B_184,C_185,D_186] :
      ( r1_tarski(k7_relset_1(A_183,B_184,C_185,D_186),B_184)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184))) ) ),
    inference(resolution,[status(thm)],[c_588,c_22])).

tff(c_687,plain,(
    ! [A_183,B_184,A_31,D_186] :
      ( r1_tarski(k7_relset_1(A_183,B_184,A_31,D_186),B_184)
      | ~ r1_tarski(A_31,k2_zfmisc_1(A_183,B_184)) ) ),
    inference(resolution,[status(thm)],[c_24,c_675])).

tff(c_950,plain,(
    ! [C_243,D_244] :
      ( r1_tarski(k9_relat_1(C_243,D_244),k2_relat_1(C_243))
      | ~ r1_tarski(C_243,k2_zfmisc_1(k1_relat_1(C_243),k2_relat_1(C_243)))
      | ~ v1_relat_1(C_243) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_935,c_687])).

tff(c_953,plain,(
    ! [C_223,D_244] :
      ( r1_tarski(k9_relat_1(C_223,D_244),k2_relat_1(C_223))
      | ~ r1_tarski(k1_relat_1(C_223),k1_relat_1(C_223))
      | ~ v1_relat_1(C_223) ) ),
    inference(resolution,[status(thm)],[c_869,c_950])).

tff(c_957,plain,(
    ! [C_245,D_246] :
      ( r1_tarski(k9_relat_1(C_245,D_246),k2_relat_1(C_245))
      | ~ v1_relat_1(C_245) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_953])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_238,plain,(
    ! [B_112,A_113] :
      ( k1_tarski(k1_funct_1(B_112,A_113)) = k2_relat_1(B_112)
      | k1_tarski(A_113) != k1_relat_1(B_112)
      | ~ v1_funct_1(B_112)
      | ~ v1_relat_1(B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_195,plain,(
    ! [D_98] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_98) = k9_relat_1('#skF_4',D_98) ),
    inference(resolution,[status(thm)],[c_54,c_189])).

tff(c_50,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_197,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_50])).

tff(c_244,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_197])).

tff(c_250,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_58,c_244])).

tff(c_252,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_250])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_56,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_146,plain,(
    ! [A_82,B_83,C_84] :
      ( k1_relset_1(A_82,B_83,C_84) = k1_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_154,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_146])).

tff(c_539,plain,(
    ! [B_170,A_171,C_172] :
      ( k1_xboole_0 = B_170
      | k1_relset_1(A_171,B_170,C_172) = A_171
      | ~ v1_funct_2(C_172,A_171,B_170)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_171,B_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_549,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_539])).

tff(c_558,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_154,c_549])).

tff(c_560,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_252,c_52,c_558])).

tff(c_561,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_250])).

tff(c_960,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_957,c_561])).

tff(c_966,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_960])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:28:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.59  
% 3.27/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.60  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.27/1.60  
% 3.27/1.60  %Foreground sorts:
% 3.27/1.60  
% 3.27/1.60  
% 3.27/1.60  %Background operators:
% 3.27/1.60  
% 3.27/1.60  
% 3.27/1.60  %Foreground operators:
% 3.27/1.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.27/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.27/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.27/1.60  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.27/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.27/1.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.27/1.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.27/1.60  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.27/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.27/1.60  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.27/1.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.27/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.27/1.60  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.27/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.27/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.27/1.60  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.27/1.60  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.27/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.27/1.60  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.27/1.60  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.27/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.27/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.27/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.27/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.60  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.27/1.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.27/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.27/1.60  
% 3.40/1.61  tff(f_111, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 3.40/1.61  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.40/1.61  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.40/1.61  tff(f_81, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 3.40/1.61  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.40/1.61  tff(f_73, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.40/1.61  tff(f_65, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 3.40/1.61  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.40/1.61  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.40/1.61  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.40/1.61  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.40/1.61  tff(c_99, plain, (![C_65, A_66, B_67]: (v1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.40/1.61  tff(c_107, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_99])).
% 3.40/1.61  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.40/1.61  tff(c_826, plain, (![C_220, A_221, B_222]: (m1_subset_1(C_220, k1_zfmisc_1(k2_zfmisc_1(A_221, B_222))) | ~r1_tarski(k2_relat_1(C_220), B_222) | ~r1_tarski(k1_relat_1(C_220), A_221) | ~v1_relat_1(C_220))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.40/1.61  tff(c_22, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | ~m1_subset_1(A_31, k1_zfmisc_1(B_32)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.40/1.61  tff(c_865, plain, (![C_223, A_224, B_225]: (r1_tarski(C_223, k2_zfmisc_1(A_224, B_225)) | ~r1_tarski(k2_relat_1(C_223), B_225) | ~r1_tarski(k1_relat_1(C_223), A_224) | ~v1_relat_1(C_223))), inference(resolution, [status(thm)], [c_826, c_22])).
% 3.40/1.61  tff(c_869, plain, (![C_223, A_224]: (r1_tarski(C_223, k2_zfmisc_1(A_224, k2_relat_1(C_223))) | ~r1_tarski(k1_relat_1(C_223), A_224) | ~v1_relat_1(C_223))), inference(resolution, [status(thm)], [c_6, c_865])).
% 3.40/1.61  tff(c_870, plain, (![C_226, A_227]: (r1_tarski(C_226, k2_zfmisc_1(A_227, k2_relat_1(C_226))) | ~r1_tarski(k1_relat_1(C_226), A_227) | ~v1_relat_1(C_226))), inference(resolution, [status(thm)], [c_6, c_865])).
% 3.40/1.61  tff(c_24, plain, (![A_31, B_32]: (m1_subset_1(A_31, k1_zfmisc_1(B_32)) | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.40/1.61  tff(c_189, plain, (![A_95, B_96, C_97, D_98]: (k7_relset_1(A_95, B_96, C_97, D_98)=k9_relat_1(C_97, D_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.40/1.61  tff(c_196, plain, (![A_95, B_96, A_31, D_98]: (k7_relset_1(A_95, B_96, A_31, D_98)=k9_relat_1(A_31, D_98) | ~r1_tarski(A_31, k2_zfmisc_1(A_95, B_96)))), inference(resolution, [status(thm)], [c_24, c_189])).
% 3.40/1.61  tff(c_917, plain, (![A_231, C_232, D_233]: (k7_relset_1(A_231, k2_relat_1(C_232), C_232, D_233)=k9_relat_1(C_232, D_233) | ~r1_tarski(k1_relat_1(C_232), A_231) | ~v1_relat_1(C_232))), inference(resolution, [status(thm)], [c_870, c_196])).
% 3.40/1.61  tff(c_935, plain, (![C_241, D_242]: (k7_relset_1(k1_relat_1(C_241), k2_relat_1(C_241), C_241, D_242)=k9_relat_1(C_241, D_242) | ~v1_relat_1(C_241))), inference(resolution, [status(thm)], [c_6, c_917])).
% 3.40/1.61  tff(c_588, plain, (![A_173, B_174, C_175, D_176]: (m1_subset_1(k7_relset_1(A_173, B_174, C_175, D_176), k1_zfmisc_1(B_174)) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.40/1.61  tff(c_675, plain, (![A_183, B_184, C_185, D_186]: (r1_tarski(k7_relset_1(A_183, B_184, C_185, D_186), B_184) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))))), inference(resolution, [status(thm)], [c_588, c_22])).
% 3.40/1.61  tff(c_687, plain, (![A_183, B_184, A_31, D_186]: (r1_tarski(k7_relset_1(A_183, B_184, A_31, D_186), B_184) | ~r1_tarski(A_31, k2_zfmisc_1(A_183, B_184)))), inference(resolution, [status(thm)], [c_24, c_675])).
% 3.40/1.61  tff(c_950, plain, (![C_243, D_244]: (r1_tarski(k9_relat_1(C_243, D_244), k2_relat_1(C_243)) | ~r1_tarski(C_243, k2_zfmisc_1(k1_relat_1(C_243), k2_relat_1(C_243))) | ~v1_relat_1(C_243))), inference(superposition, [status(thm), theory('equality')], [c_935, c_687])).
% 3.40/1.61  tff(c_953, plain, (![C_223, D_244]: (r1_tarski(k9_relat_1(C_223, D_244), k2_relat_1(C_223)) | ~r1_tarski(k1_relat_1(C_223), k1_relat_1(C_223)) | ~v1_relat_1(C_223))), inference(resolution, [status(thm)], [c_869, c_950])).
% 3.40/1.61  tff(c_957, plain, (![C_245, D_246]: (r1_tarski(k9_relat_1(C_245, D_246), k2_relat_1(C_245)) | ~v1_relat_1(C_245))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_953])).
% 3.40/1.61  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.40/1.61  tff(c_238, plain, (![B_112, A_113]: (k1_tarski(k1_funct_1(B_112, A_113))=k2_relat_1(B_112) | k1_tarski(A_113)!=k1_relat_1(B_112) | ~v1_funct_1(B_112) | ~v1_relat_1(B_112))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.40/1.61  tff(c_195, plain, (![D_98]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_98)=k9_relat_1('#skF_4', D_98))), inference(resolution, [status(thm)], [c_54, c_189])).
% 3.40/1.61  tff(c_50, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.40/1.61  tff(c_197, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_50])).
% 3.40/1.61  tff(c_244, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_238, c_197])).
% 3.40/1.61  tff(c_250, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_58, c_244])).
% 3.40/1.61  tff(c_252, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_250])).
% 3.40/1.61  tff(c_52, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.40/1.61  tff(c_56, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.40/1.61  tff(c_146, plain, (![A_82, B_83, C_84]: (k1_relset_1(A_82, B_83, C_84)=k1_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.40/1.61  tff(c_154, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_146])).
% 3.40/1.61  tff(c_539, plain, (![B_170, A_171, C_172]: (k1_xboole_0=B_170 | k1_relset_1(A_171, B_170, C_172)=A_171 | ~v1_funct_2(C_172, A_171, B_170) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_171, B_170))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.40/1.61  tff(c_549, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_54, c_539])).
% 3.40/1.61  tff(c_558, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_154, c_549])).
% 3.40/1.61  tff(c_560, plain, $false, inference(negUnitSimplification, [status(thm)], [c_252, c_52, c_558])).
% 3.40/1.61  tff(c_561, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_250])).
% 3.40/1.61  tff(c_960, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_957, c_561])).
% 3.40/1.61  tff(c_966, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_960])).
% 3.40/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.61  
% 3.40/1.61  Inference rules
% 3.40/1.61  ----------------------
% 3.40/1.61  #Ref     : 0
% 3.40/1.61  #Sup     : 191
% 3.40/1.61  #Fact    : 0
% 3.40/1.61  #Define  : 0
% 3.40/1.61  #Split   : 2
% 3.40/1.61  #Chain   : 0
% 3.40/1.61  #Close   : 0
% 3.40/1.61  
% 3.40/1.61  Ordering : KBO
% 3.40/1.61  
% 3.40/1.61  Simplification rules
% 3.40/1.61  ----------------------
% 3.40/1.61  #Subsume      : 2
% 3.40/1.61  #Demod        : 45
% 3.40/1.61  #Tautology    : 63
% 3.40/1.61  #SimpNegUnit  : 1
% 3.40/1.61  #BackRed      : 7
% 3.40/1.61  
% 3.40/1.61  #Partial instantiations: 0
% 3.40/1.61  #Strategies tried      : 1
% 3.40/1.61  
% 3.40/1.61  Timing (in seconds)
% 3.40/1.61  ----------------------
% 3.40/1.62  Preprocessing        : 0.37
% 3.40/1.62  Parsing              : 0.20
% 3.40/1.62  CNF conversion       : 0.02
% 3.40/1.62  Main loop            : 0.41
% 3.40/1.62  Inferencing          : 0.16
% 3.40/1.62  Reduction            : 0.12
% 3.40/1.62  Demodulation         : 0.09
% 3.40/1.62  BG Simplification    : 0.03
% 3.40/1.62  Subsumption          : 0.08
% 3.40/1.62  Abstraction          : 0.02
% 3.40/1.62  MUC search           : 0.00
% 3.40/1.62  Cooper               : 0.00
% 3.40/1.62  Total                : 0.81
% 3.40/1.62  Index Insertion      : 0.00
% 3.40/1.62  Index Deletion       : 0.00
% 3.40/1.62  Index Matching       : 0.00
% 3.40/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
