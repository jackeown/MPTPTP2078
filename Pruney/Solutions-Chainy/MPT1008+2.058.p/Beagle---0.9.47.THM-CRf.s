%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:34 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 248 expanded)
%              Number of leaves         :   44 ( 103 expanded)
%              Depth                    :   13
%              Number of atoms          :  146 ( 517 expanded)
%              Number of equality atoms :   58 ( 222 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v5_ordinal1 > v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_142,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_54,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_118,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_130,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_83,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_128,plain,(
    ! [C_80,A_81,B_82] :
      ( v1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_132,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_128])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_32,plain,(
    ! [A_27] :
      ( k1_relat_1(A_27) != k1_xboole_0
      | k1_xboole_0 = A_27
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_139,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_132,c_32])).

tff(c_141,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_162,plain,(
    ! [C_88,A_89,B_90] :
      ( v4_relat_1(C_88,A_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_166,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_64,c_162])).

tff(c_181,plain,(
    ! [B_97,A_98] :
      ( r1_tarski(k1_relat_1(B_97),A_98)
      | ~ v4_relat_1(B_97,A_98)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    ! [B_24,A_23] :
      ( k1_tarski(B_24) = A_23
      | k1_xboole_0 = A_23
      | ~ r1_tarski(A_23,k1_tarski(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_242,plain,(
    ! [B_112,B_113] :
      ( k1_tarski(B_112) = k1_relat_1(B_113)
      | k1_relat_1(B_113) = k1_xboole_0
      | ~ v4_relat_1(B_113,k1_tarski(B_112))
      | ~ v1_relat_1(B_113) ) ),
    inference(resolution,[status(thm)],[c_181,c_16])).

tff(c_245,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_166,c_242])).

tff(c_252,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_245])).

tff(c_253,plain,(
    k1_tarski('#skF_2') = k1_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_252])).

tff(c_281,plain,(
    ! [B_114,A_115] :
      ( k1_tarski(k1_funct_1(B_114,A_115)) = k2_relat_1(B_114)
      | k1_tarski(A_115) != k1_relat_1(B_114)
      | ~ v1_funct_1(B_114)
      | ~ v1_relat_1(B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_223,plain,(
    ! [A_104,B_105,C_106] :
      ( k2_relset_1(A_104,B_105,C_106) = k2_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_227,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_223])).

tff(c_60,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') != k1_tarski(k1_funct_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_228,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_60])).

tff(c_290,plain,
    ( k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_228])).

tff(c_307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_68,c_253,c_290])).

tff(c_308,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_309,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_329,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_309])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_315,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_308,c_26])).

tff(c_480,plain,(
    ! [B_153,A_154] :
      ( k1_tarski(k1_funct_1(B_153,A_154)) = k2_relat_1(B_153)
      | k1_tarski(A_154) != k1_relat_1(B_153)
      | ~ v1_funct_1(B_153)
      | ~ v1_relat_1(B_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_452,plain,(
    ! [A_143,B_144,C_145] :
      ( k2_relset_1(A_143,B_144,C_145) = k2_relat_1(C_145)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_455,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_452])).

tff(c_457,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_455])).

tff(c_458,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_60])).

tff(c_489,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_458])).

tff(c_504,plain,(
    k1_tarski('#skF_2') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_68,c_329,c_315,c_489])).

tff(c_56,plain,(
    ! [A_42] :
      ( r2_hidden('#skF_1'(A_42),A_42)
      | k1_xboole_0 = A_42 ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_313,plain,(
    ! [A_42] :
      ( r2_hidden('#skF_1'(A_42),A_42)
      | A_42 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_56])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_317,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_2])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_321,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_62])).

tff(c_66,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_58,plain,(
    ! [D_67,C_66,A_64,B_65] :
      ( r2_hidden(k1_funct_1(D_67,C_66),k2_relset_1(A_64,B_65,D_67))
      | k1_xboole_0 = B_65
      | ~ r2_hidden(C_66,A_64)
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | ~ v1_funct_2(D_67,A_64,B_65)
      | ~ v1_funct_1(D_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_697,plain,(
    ! [D_181,C_182,A_183,B_184] :
      ( r2_hidden(k1_funct_1(D_181,C_182),k2_relset_1(A_183,B_184,D_181))
      | B_184 = '#skF_4'
      | ~ r2_hidden(C_182,A_183)
      | ~ m1_subset_1(D_181,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184)))
      | ~ v1_funct_2(D_181,A_183,B_184)
      | ~ v1_funct_1(D_181) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_58])).

tff(c_703,plain,(
    ! [C_182] :
      ( r2_hidden(k1_funct_1('#skF_4',C_182),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_182,k1_tarski('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3')))
      | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_457,c_697])).

tff(c_706,plain,(
    ! [C_182] :
      ( r2_hidden(k1_funct_1('#skF_4',C_182),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_182,k1_tarski('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_703])).

tff(c_708,plain,(
    ! [C_185] :
      ( r2_hidden(k1_funct_1('#skF_4',C_185),'#skF_4')
      | ~ r2_hidden(C_185,k1_tarski('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_321,c_706])).

tff(c_44,plain,(
    ! [B_32,A_31] :
      ( ~ r1_tarski(B_32,A_31)
      | ~ r2_hidden(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_711,plain,(
    ! [C_185] :
      ( ~ r1_tarski('#skF_4',k1_funct_1('#skF_4',C_185))
      | ~ r2_hidden(C_185,k1_tarski('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_708,c_44])).

tff(c_715,plain,(
    ! [C_186] : ~ r2_hidden(C_186,k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_711])).

tff(c_719,plain,(
    k1_tarski('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_313,c_715])).

tff(c_723,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_504,c_719])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:25:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.44  
% 2.72/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.45  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v5_ordinal1 > v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.03/1.45  
% 3.03/1.45  %Foreground sorts:
% 3.03/1.45  
% 3.03/1.45  
% 3.03/1.45  %Background operators:
% 3.03/1.45  
% 3.03/1.45  
% 3.03/1.45  %Foreground operators:
% 3.03/1.45  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.03/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.03/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.03/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.03/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.03/1.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.03/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.03/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.03/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.03/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.03/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.03/1.45  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 3.03/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.03/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.03/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.03/1.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.03/1.45  tff('#skF_2', type, '#skF_2': $i).
% 3.03/1.45  tff('#skF_3', type, '#skF_3': $i).
% 3.03/1.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.03/1.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.03/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.03/1.45  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.03/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.03/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.03/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.03/1.45  tff('#skF_4', type, '#skF_4': $i).
% 3.03/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.03/1.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.03/1.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.03/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.03/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.03/1.45  
% 3.03/1.46  tff(f_142, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 3.03/1.46  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.03/1.46  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.03/1.46  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.03/1.46  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.03/1.46  tff(f_45, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.03/1.46  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.03/1.46  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.03/1.46  tff(f_54, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.03/1.46  tff(f_118, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 3.03/1.46  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.03/1.46  tff(f_130, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 3.03/1.46  tff(f_83, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.03/1.46  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.03/1.46  tff(c_128, plain, (![C_80, A_81, B_82]: (v1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.03/1.46  tff(c_132, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_128])).
% 3.03/1.46  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.03/1.46  tff(c_32, plain, (![A_27]: (k1_relat_1(A_27)!=k1_xboole_0 | k1_xboole_0=A_27 | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.03/1.46  tff(c_139, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_132, c_32])).
% 3.03/1.46  tff(c_141, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_139])).
% 3.03/1.46  tff(c_162, plain, (![C_88, A_89, B_90]: (v4_relat_1(C_88, A_89) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.03/1.46  tff(c_166, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_64, c_162])).
% 3.03/1.46  tff(c_181, plain, (![B_97, A_98]: (r1_tarski(k1_relat_1(B_97), A_98) | ~v4_relat_1(B_97, A_98) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.03/1.46  tff(c_16, plain, (![B_24, A_23]: (k1_tarski(B_24)=A_23 | k1_xboole_0=A_23 | ~r1_tarski(A_23, k1_tarski(B_24)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.03/1.46  tff(c_242, plain, (![B_112, B_113]: (k1_tarski(B_112)=k1_relat_1(B_113) | k1_relat_1(B_113)=k1_xboole_0 | ~v4_relat_1(B_113, k1_tarski(B_112)) | ~v1_relat_1(B_113))), inference(resolution, [status(thm)], [c_181, c_16])).
% 3.03/1.46  tff(c_245, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_166, c_242])).
% 3.03/1.46  tff(c_252, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_132, c_245])).
% 3.03/1.46  tff(c_253, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_141, c_252])).
% 3.03/1.46  tff(c_281, plain, (![B_114, A_115]: (k1_tarski(k1_funct_1(B_114, A_115))=k2_relat_1(B_114) | k1_tarski(A_115)!=k1_relat_1(B_114) | ~v1_funct_1(B_114) | ~v1_relat_1(B_114))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.03/1.46  tff(c_223, plain, (![A_104, B_105, C_106]: (k2_relset_1(A_104, B_105, C_106)=k2_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.03/1.46  tff(c_227, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_223])).
% 3.03/1.46  tff(c_60, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')!=k1_tarski(k1_funct_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.03/1.46  tff(c_228, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_227, c_60])).
% 3.03/1.46  tff(c_290, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_281, c_228])).
% 3.03/1.46  tff(c_307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_132, c_68, c_253, c_290])).
% 3.03/1.46  tff(c_308, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_139])).
% 3.03/1.46  tff(c_309, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_139])).
% 3.03/1.46  tff(c_329, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_308, c_309])).
% 3.03/1.46  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.03/1.46  tff(c_315, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_308, c_308, c_26])).
% 3.03/1.46  tff(c_480, plain, (![B_153, A_154]: (k1_tarski(k1_funct_1(B_153, A_154))=k2_relat_1(B_153) | k1_tarski(A_154)!=k1_relat_1(B_153) | ~v1_funct_1(B_153) | ~v1_relat_1(B_153))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.03/1.46  tff(c_452, plain, (![A_143, B_144, C_145]: (k2_relset_1(A_143, B_144, C_145)=k2_relat_1(C_145) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.03/1.46  tff(c_455, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_452])).
% 3.03/1.46  tff(c_457, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_315, c_455])).
% 3.03/1.46  tff(c_458, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_457, c_60])).
% 3.03/1.46  tff(c_489, plain, (k2_relat_1('#skF_4')!='#skF_4' | k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_480, c_458])).
% 3.03/1.46  tff(c_504, plain, (k1_tarski('#skF_2')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_68, c_329, c_315, c_489])).
% 3.03/1.46  tff(c_56, plain, (![A_42]: (r2_hidden('#skF_1'(A_42), A_42) | k1_xboole_0=A_42)), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.03/1.46  tff(c_313, plain, (![A_42]: (r2_hidden('#skF_1'(A_42), A_42) | A_42='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_308, c_56])).
% 3.03/1.46  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.03/1.46  tff(c_317, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_308, c_2])).
% 3.03/1.46  tff(c_62, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.03/1.46  tff(c_321, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_308, c_62])).
% 3.03/1.46  tff(c_66, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.03/1.46  tff(c_58, plain, (![D_67, C_66, A_64, B_65]: (r2_hidden(k1_funct_1(D_67, C_66), k2_relset_1(A_64, B_65, D_67)) | k1_xboole_0=B_65 | ~r2_hidden(C_66, A_64) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))) | ~v1_funct_2(D_67, A_64, B_65) | ~v1_funct_1(D_67))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.03/1.46  tff(c_697, plain, (![D_181, C_182, A_183, B_184]: (r2_hidden(k1_funct_1(D_181, C_182), k2_relset_1(A_183, B_184, D_181)) | B_184='#skF_4' | ~r2_hidden(C_182, A_183) | ~m1_subset_1(D_181, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))) | ~v1_funct_2(D_181, A_183, B_184) | ~v1_funct_1(D_181))), inference(demodulation, [status(thm), theory('equality')], [c_308, c_58])).
% 3.03/1.46  tff(c_703, plain, (![C_182]: (r2_hidden(k1_funct_1('#skF_4', C_182), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_182, k1_tarski('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_457, c_697])).
% 3.03/1.46  tff(c_706, plain, (![C_182]: (r2_hidden(k1_funct_1('#skF_4', C_182), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_182, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_703])).
% 3.03/1.46  tff(c_708, plain, (![C_185]: (r2_hidden(k1_funct_1('#skF_4', C_185), '#skF_4') | ~r2_hidden(C_185, k1_tarski('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_321, c_706])).
% 3.03/1.46  tff(c_44, plain, (![B_32, A_31]: (~r1_tarski(B_32, A_31) | ~r2_hidden(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.03/1.46  tff(c_711, plain, (![C_185]: (~r1_tarski('#skF_4', k1_funct_1('#skF_4', C_185)) | ~r2_hidden(C_185, k1_tarski('#skF_2')))), inference(resolution, [status(thm)], [c_708, c_44])).
% 3.03/1.46  tff(c_715, plain, (![C_186]: (~r2_hidden(C_186, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_317, c_711])).
% 3.03/1.46  tff(c_719, plain, (k1_tarski('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_313, c_715])).
% 3.03/1.46  tff(c_723, plain, $false, inference(negUnitSimplification, [status(thm)], [c_504, c_719])).
% 3.03/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.46  
% 3.03/1.46  Inference rules
% 3.03/1.46  ----------------------
% 3.03/1.46  #Ref     : 0
% 3.03/1.46  #Sup     : 137
% 3.03/1.46  #Fact    : 1
% 3.03/1.46  #Define  : 0
% 3.03/1.46  #Split   : 2
% 3.03/1.46  #Chain   : 0
% 3.03/1.46  #Close   : 0
% 3.03/1.46  
% 3.03/1.46  Ordering : KBO
% 3.03/1.46  
% 3.03/1.46  Simplification rules
% 3.03/1.46  ----------------------
% 3.03/1.46  #Subsume      : 15
% 3.03/1.46  #Demod        : 132
% 3.03/1.46  #Tautology    : 71
% 3.03/1.46  #SimpNegUnit  : 4
% 3.03/1.46  #BackRed      : 18
% 3.03/1.46  
% 3.03/1.46  #Partial instantiations: 0
% 3.03/1.46  #Strategies tried      : 1
% 3.03/1.46  
% 3.03/1.46  Timing (in seconds)
% 3.03/1.46  ----------------------
% 3.03/1.46  Preprocessing        : 0.38
% 3.03/1.46  Parsing              : 0.20
% 3.03/1.46  CNF conversion       : 0.03
% 3.03/1.46  Main loop            : 0.31
% 3.03/1.47  Inferencing          : 0.12
% 3.03/1.47  Reduction            : 0.10
% 3.03/1.47  Demodulation         : 0.07
% 3.03/1.47  BG Simplification    : 0.02
% 3.03/1.47  Subsumption          : 0.05
% 3.03/1.47  Abstraction          : 0.02
% 3.03/1.47  MUC search           : 0.00
% 3.03/1.47  Cooper               : 0.00
% 3.03/1.47  Total                : 0.73
% 3.03/1.47  Index Insertion      : 0.00
% 3.03/1.47  Index Deletion       : 0.00
% 3.03/1.47  Index Matching       : 0.00
% 3.03/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
