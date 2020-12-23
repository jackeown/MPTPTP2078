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
% DateTime   : Thu Dec  3 10:14:33 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 281 expanded)
%              Number of leaves         :   40 ( 110 expanded)
%              Depth                    :   13
%              Number of atoms          :  154 ( 598 expanded)
%              Number of equality atoms :   68 ( 262 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k3_mcart_1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_48,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_99,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_111,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_69,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_101,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_105,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_101])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_26,plain,(
    ! [A_12] :
      ( k1_relat_1(A_12) != k1_xboole_0
      | k1_xboole_0 = A_12
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_113,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_105,c_26])).

tff(c_115,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_168,plain,(
    ! [C_70,A_71,B_72] :
      ( v4_relat_1(C_70,A_71)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_172,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_168])).

tff(c_140,plain,(
    ! [B_65,A_66] :
      ( r1_tarski(k1_relat_1(B_65),A_66)
      | ~ v4_relat_1(B_65,A_66)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k1_tarski(B_9) = A_8
      | k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_tarski(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_198,plain,(
    ! [B_91,B_92] :
      ( k1_tarski(B_91) = k1_relat_1(B_92)
      | k1_relat_1(B_92) = k1_xboole_0
      | ~ v4_relat_1(B_92,k1_tarski(B_91))
      | ~ v1_relat_1(B_92) ) ),
    inference(resolution,[status(thm)],[c_140,c_10])).

tff(c_201,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_172,c_198])).

tff(c_204,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_201])).

tff(c_205,plain,(
    k1_tarski('#skF_2') = k1_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_204])).

tff(c_236,plain,(
    ! [B_93,A_94] :
      ( k1_tarski(k1_funct_1(B_93,A_94)) = k2_relat_1(B_93)
      | k1_tarski(A_94) != k1_relat_1(B_93)
      | ~ v1_funct_1(B_93)
      | ~ v1_relat_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_188,plain,(
    ! [A_88,B_89,C_90] :
      ( k2_relset_1(A_88,B_89,C_90) = k2_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_192,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_188])).

tff(c_48,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') != k1_tarski(k1_funct_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_193,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_48])).

tff(c_245,plain,
    ( k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_193])).

tff(c_262,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_56,c_205,c_245])).

tff(c_263,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_24,plain,(
    ! [A_12] :
      ( k2_relat_1(A_12) != k1_xboole_0
      | k1_xboole_0 = A_12
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_112,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_105,c_24])).

tff(c_114,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_265,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_114])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_271,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_263,c_20])).

tff(c_283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_265,c_271])).

tff(c_284,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_292,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_284,c_22])).

tff(c_285,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_298,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_285])).

tff(c_443,plain,(
    ! [B_136,A_137] :
      ( k1_tarski(k1_funct_1(B_136,A_137)) = k2_relat_1(B_136)
      | k1_tarski(A_137) != k1_relat_1(B_136)
      | ~ v1_funct_1(B_136)
      | ~ v1_relat_1(B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_424,plain,(
    ! [A_131,B_132,C_133] :
      ( k2_relset_1(A_131,B_132,C_133) = k2_relat_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_427,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_424])).

tff(c_429,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_427])).

tff(c_430,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_48])).

tff(c_452,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_443,c_430])).

tff(c_467,plain,(
    k1_tarski('#skF_2') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_56,c_292,c_298,c_452])).

tff(c_40,plain,(
    ! [A_26] :
      ( r2_hidden('#skF_1'(A_26),A_26)
      | k1_xboole_0 = A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_289,plain,(
    ! [A_26] :
      ( r2_hidden('#skF_1'(A_26),A_26)
      | A_26 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_40])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_290,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_2])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_293,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_50])).

tff(c_54,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_46,plain,(
    ! [D_43,C_42,A_40,B_41] :
      ( r2_hidden(k1_funct_1(D_43,C_42),k2_relset_1(A_40,B_41,D_43))
      | k1_xboole_0 = B_41
      | ~ r2_hidden(C_42,A_40)
      | ~ m1_subset_1(D_43,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41)))
      | ~ v1_funct_2(D_43,A_40,B_41)
      | ~ v1_funct_1(D_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_483,plain,(
    ! [D_140,C_141,A_142,B_143] :
      ( r2_hidden(k1_funct_1(D_140,C_141),k2_relset_1(A_142,B_143,D_140))
      | B_143 = '#skF_4'
      | ~ r2_hidden(C_141,A_142)
      | ~ m1_subset_1(D_140,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143)))
      | ~ v1_funct_2(D_140,A_142,B_143)
      | ~ v1_funct_1(D_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_46])).

tff(c_493,plain,(
    ! [C_141] :
      ( r2_hidden(k1_funct_1('#skF_4',C_141),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_141,k1_tarski('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3')))
      | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_483])).

tff(c_498,plain,(
    ! [C_141] :
      ( r2_hidden(k1_funct_1('#skF_4',C_141),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_141,k1_tarski('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_493])).

tff(c_500,plain,(
    ! [C_144] :
      ( r2_hidden(k1_funct_1('#skF_4',C_144),'#skF_4')
      | ~ r2_hidden(C_144,k1_tarski('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_293,c_498])).

tff(c_30,plain,(
    ! [B_16,A_15] :
      ( ~ r1_tarski(B_16,A_15)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_507,plain,(
    ! [C_144] :
      ( ~ r1_tarski('#skF_4',k1_funct_1('#skF_4',C_144))
      | ~ r2_hidden(C_144,k1_tarski('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_500,c_30])).

tff(c_515,plain,(
    ! [C_145] : ~ r2_hidden(C_145,k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_507])).

tff(c_519,plain,(
    k1_tarski('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_289,c_515])).

tff(c_523,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_467,c_519])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:35:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.35  
% 2.49/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.35  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k3_mcart_1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.49/1.35  
% 2.49/1.35  %Foreground sorts:
% 2.49/1.35  
% 2.49/1.35  
% 2.49/1.35  %Background operators:
% 2.49/1.35  
% 2.49/1.35  
% 2.49/1.35  %Foreground operators:
% 2.49/1.35  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.49/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.49/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.49/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.49/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.35  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.49/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.49/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.49/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.49/1.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.49/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.49/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.35  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.49/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.49/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.49/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.49/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.49/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.49/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.35  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.49/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.49/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.49/1.35  
% 2.77/1.37  tff(f_123, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 2.77/1.37  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.77/1.37  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.77/1.37  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.77/1.37  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.77/1.37  tff(f_39, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.77/1.37  tff(f_64, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 2.77/1.37  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.77/1.37  tff(f_48, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.77/1.37  tff(f_99, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 2.77/1.37  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.77/1.37  tff(f_111, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 2.77/1.37  tff(f_69, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.77/1.37  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.77/1.37  tff(c_101, plain, (![C_55, A_56, B_57]: (v1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.77/1.37  tff(c_105, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_101])).
% 2.77/1.37  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.77/1.37  tff(c_26, plain, (![A_12]: (k1_relat_1(A_12)!=k1_xboole_0 | k1_xboole_0=A_12 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.77/1.37  tff(c_113, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_105, c_26])).
% 2.77/1.37  tff(c_115, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_113])).
% 2.77/1.37  tff(c_168, plain, (![C_70, A_71, B_72]: (v4_relat_1(C_70, A_71) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.77/1.37  tff(c_172, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_52, c_168])).
% 2.77/1.37  tff(c_140, plain, (![B_65, A_66]: (r1_tarski(k1_relat_1(B_65), A_66) | ~v4_relat_1(B_65, A_66) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.77/1.37  tff(c_10, plain, (![B_9, A_8]: (k1_tarski(B_9)=A_8 | k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_tarski(B_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.77/1.37  tff(c_198, plain, (![B_91, B_92]: (k1_tarski(B_91)=k1_relat_1(B_92) | k1_relat_1(B_92)=k1_xboole_0 | ~v4_relat_1(B_92, k1_tarski(B_91)) | ~v1_relat_1(B_92))), inference(resolution, [status(thm)], [c_140, c_10])).
% 2.77/1.37  tff(c_201, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_172, c_198])).
% 2.77/1.37  tff(c_204, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_105, c_201])).
% 2.77/1.37  tff(c_205, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_115, c_204])).
% 2.77/1.37  tff(c_236, plain, (![B_93, A_94]: (k1_tarski(k1_funct_1(B_93, A_94))=k2_relat_1(B_93) | k1_tarski(A_94)!=k1_relat_1(B_93) | ~v1_funct_1(B_93) | ~v1_relat_1(B_93))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.77/1.37  tff(c_188, plain, (![A_88, B_89, C_90]: (k2_relset_1(A_88, B_89, C_90)=k2_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.77/1.37  tff(c_192, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_188])).
% 2.77/1.37  tff(c_48, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')!=k1_tarski(k1_funct_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.77/1.37  tff(c_193, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_192, c_48])).
% 2.77/1.37  tff(c_245, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_236, c_193])).
% 2.77/1.37  tff(c_262, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_105, c_56, c_205, c_245])).
% 2.77/1.37  tff(c_263, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_113])).
% 2.77/1.37  tff(c_24, plain, (![A_12]: (k2_relat_1(A_12)!=k1_xboole_0 | k1_xboole_0=A_12 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.77/1.37  tff(c_112, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_105, c_24])).
% 2.77/1.37  tff(c_114, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_112])).
% 2.77/1.37  tff(c_265, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_263, c_114])).
% 2.77/1.37  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.77/1.37  tff(c_271, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_263, c_263, c_20])).
% 2.77/1.37  tff(c_283, plain, $false, inference(negUnitSimplification, [status(thm)], [c_265, c_271])).
% 2.77/1.37  tff(c_284, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_112])).
% 2.77/1.37  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.77/1.37  tff(c_292, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_284, c_284, c_22])).
% 2.77/1.37  tff(c_285, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_112])).
% 2.77/1.37  tff(c_298, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_284, c_285])).
% 2.77/1.37  tff(c_443, plain, (![B_136, A_137]: (k1_tarski(k1_funct_1(B_136, A_137))=k2_relat_1(B_136) | k1_tarski(A_137)!=k1_relat_1(B_136) | ~v1_funct_1(B_136) | ~v1_relat_1(B_136))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.77/1.37  tff(c_424, plain, (![A_131, B_132, C_133]: (k2_relset_1(A_131, B_132, C_133)=k2_relat_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.77/1.37  tff(c_427, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_424])).
% 2.77/1.37  tff(c_429, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_298, c_427])).
% 2.77/1.37  tff(c_430, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_429, c_48])).
% 2.77/1.37  tff(c_452, plain, (k2_relat_1('#skF_4')!='#skF_4' | k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_443, c_430])).
% 2.77/1.37  tff(c_467, plain, (k1_tarski('#skF_2')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_105, c_56, c_292, c_298, c_452])).
% 2.77/1.37  tff(c_40, plain, (![A_26]: (r2_hidden('#skF_1'(A_26), A_26) | k1_xboole_0=A_26)), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.77/1.37  tff(c_289, plain, (![A_26]: (r2_hidden('#skF_1'(A_26), A_26) | A_26='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_284, c_40])).
% 2.77/1.37  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.77/1.37  tff(c_290, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_284, c_2])).
% 2.77/1.37  tff(c_50, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.77/1.37  tff(c_293, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_284, c_50])).
% 2.77/1.37  tff(c_54, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.77/1.37  tff(c_46, plain, (![D_43, C_42, A_40, B_41]: (r2_hidden(k1_funct_1(D_43, C_42), k2_relset_1(A_40, B_41, D_43)) | k1_xboole_0=B_41 | ~r2_hidden(C_42, A_40) | ~m1_subset_1(D_43, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))) | ~v1_funct_2(D_43, A_40, B_41) | ~v1_funct_1(D_43))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.77/1.37  tff(c_483, plain, (![D_140, C_141, A_142, B_143]: (r2_hidden(k1_funct_1(D_140, C_141), k2_relset_1(A_142, B_143, D_140)) | B_143='#skF_4' | ~r2_hidden(C_141, A_142) | ~m1_subset_1(D_140, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))) | ~v1_funct_2(D_140, A_142, B_143) | ~v1_funct_1(D_140))), inference(demodulation, [status(thm), theory('equality')], [c_284, c_46])).
% 2.77/1.37  tff(c_493, plain, (![C_141]: (r2_hidden(k1_funct_1('#skF_4', C_141), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_141, k1_tarski('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_429, c_483])).
% 2.77/1.37  tff(c_498, plain, (![C_141]: (r2_hidden(k1_funct_1('#skF_4', C_141), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_141, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_493])).
% 2.77/1.37  tff(c_500, plain, (![C_144]: (r2_hidden(k1_funct_1('#skF_4', C_144), '#skF_4') | ~r2_hidden(C_144, k1_tarski('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_293, c_498])).
% 2.77/1.37  tff(c_30, plain, (![B_16, A_15]: (~r1_tarski(B_16, A_15) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.77/1.37  tff(c_507, plain, (![C_144]: (~r1_tarski('#skF_4', k1_funct_1('#skF_4', C_144)) | ~r2_hidden(C_144, k1_tarski('#skF_2')))), inference(resolution, [status(thm)], [c_500, c_30])).
% 2.77/1.37  tff(c_515, plain, (![C_145]: (~r2_hidden(C_145, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_290, c_507])).
% 2.77/1.37  tff(c_519, plain, (k1_tarski('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_289, c_515])).
% 2.77/1.37  tff(c_523, plain, $false, inference(negUnitSimplification, [status(thm)], [c_467, c_519])).
% 2.77/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.37  
% 2.77/1.37  Inference rules
% 2.77/1.37  ----------------------
% 2.77/1.37  #Ref     : 0
% 2.77/1.37  #Sup     : 96
% 2.77/1.37  #Fact    : 0
% 2.77/1.37  #Define  : 0
% 2.77/1.37  #Split   : 3
% 2.77/1.37  #Chain   : 0
% 2.77/1.37  #Close   : 0
% 2.77/1.37  
% 2.77/1.37  Ordering : KBO
% 2.77/1.37  
% 2.77/1.37  Simplification rules
% 2.77/1.37  ----------------------
% 2.77/1.37  #Subsume      : 5
% 2.77/1.37  #Demod        : 84
% 2.77/1.37  #Tautology    : 53
% 2.77/1.37  #SimpNegUnit  : 4
% 2.77/1.37  #BackRed      : 23
% 2.77/1.37  
% 2.77/1.37  #Partial instantiations: 0
% 2.77/1.37  #Strategies tried      : 1
% 2.77/1.37  
% 2.77/1.37  Timing (in seconds)
% 2.77/1.37  ----------------------
% 2.77/1.37  Preprocessing        : 0.33
% 2.77/1.37  Parsing              : 0.18
% 2.77/1.37  CNF conversion       : 0.02
% 2.77/1.37  Main loop            : 0.27
% 2.77/1.37  Inferencing          : 0.10
% 2.77/1.37  Reduction            : 0.09
% 2.77/1.37  Demodulation         : 0.06
% 2.77/1.37  BG Simplification    : 0.02
% 2.77/1.37  Subsumption          : 0.05
% 2.77/1.37  Abstraction          : 0.01
% 2.77/1.37  MUC search           : 0.00
% 2.77/1.37  Cooper               : 0.00
% 2.77/1.37  Total                : 0.64
% 2.77/1.37  Index Insertion      : 0.00
% 2.77/1.37  Index Deletion       : 0.00
% 2.77/1.37  Index Matching       : 0.00
% 2.77/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
