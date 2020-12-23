%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:33 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 281 expanded)
%              Number of leaves         :   40 ( 110 expanded)
%              Depth                    :   13
%              Number of atoms          :  154 ( 598 expanded)
%              Number of equality atoms :   68 ( 262 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_mcart_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_48,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_99,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

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
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
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

tff(c_197,plain,(
    ! [B_95,A_96] :
      ( k1_tarski(k1_funct_1(B_95,A_96)) = k2_relat_1(B_95)
      | k1_tarski(A_96) != k1_relat_1(B_95)
      | ~ v1_funct_1(B_95)
      | ~ v1_relat_1(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_183,plain,(
    ! [A_87,B_88,C_89] :
      ( k2_relset_1(A_87,B_88,C_89) = k2_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_187,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_183])).

tff(c_48,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') != k1_tarski(k1_funct_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_188,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_48])).

tff(c_203,plain,
    ( k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_188])).

tff(c_219,plain,(
    k1_tarski('#skF_2') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_56,c_203])).

tff(c_168,plain,(
    ! [C_74,A_75,B_76] :
      ( v4_relat_1(C_74,A_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_172,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_168])).

tff(c_140,plain,(
    ! [B_69,A_70] :
      ( r1_tarski(k1_relat_1(B_69),A_70)
      | ~ v4_relat_1(B_69,A_70)
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k1_tarski(B_9) = A_8
      | k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_tarski(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_222,plain,(
    ! [B_101,B_102] :
      ( k1_tarski(B_101) = k1_relat_1(B_102)
      | k1_relat_1(B_102) = k1_xboole_0
      | ~ v4_relat_1(B_102,k1_tarski(B_101))
      | ~ v1_relat_1(B_102) ) ),
    inference(resolution,[status(thm)],[c_140,c_10])).

tff(c_228,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_172,c_222])).

tff(c_231,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_228])).

tff(c_233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_219,c_231])).

tff(c_234,plain,(
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

tff(c_236,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_114])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_242,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_234,c_20])).

tff(c_260,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_242])).

tff(c_261,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_269,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_261,c_22])).

tff(c_262,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_275,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_262])).

tff(c_420,plain,(
    ! [B_152,A_153] :
      ( k1_tarski(k1_funct_1(B_152,A_153)) = k2_relat_1(B_152)
      | k1_tarski(A_153) != k1_relat_1(B_152)
      | ~ v1_funct_1(B_152)
      | ~ v1_relat_1(B_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_389,plain,(
    ! [A_129,B_130,C_131] :
      ( k2_relset_1(A_129,B_130,C_131) = k2_relat_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_392,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_389])).

tff(c_394,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_392])).

tff(c_400,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_48])).

tff(c_429,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_400])).

tff(c_444,plain,(
    k1_tarski('#skF_2') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_56,c_269,c_275,c_429])).

tff(c_40,plain,(
    ! [A_26] :
      ( r2_hidden('#skF_1'(A_26),A_26)
      | k1_xboole_0 = A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_266,plain,(
    ! [A_26] :
      ( r2_hidden('#skF_1'(A_26),A_26)
      | A_26 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_40])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_267,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_2])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_270,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_50])).

tff(c_54,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_46,plain,(
    ! [D_47,C_46,A_44,B_45] :
      ( r2_hidden(k1_funct_1(D_47,C_46),k2_relset_1(A_44,B_45,D_47))
      | k1_xboole_0 = B_45
      | ~ r2_hidden(C_46,A_44)
      | ~ m1_subset_1(D_47,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45)))
      | ~ v1_funct_2(D_47,A_44,B_45)
      | ~ v1_funct_1(D_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_460,plain,(
    ! [D_156,C_157,A_158,B_159] :
      ( r2_hidden(k1_funct_1(D_156,C_157),k2_relset_1(A_158,B_159,D_156))
      | B_159 = '#skF_4'
      | ~ r2_hidden(C_157,A_158)
      | ~ m1_subset_1(D_156,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159)))
      | ~ v1_funct_2(D_156,A_158,B_159)
      | ~ v1_funct_1(D_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_46])).

tff(c_470,plain,(
    ! [C_157] :
      ( r2_hidden(k1_funct_1('#skF_4',C_157),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_157,k1_tarski('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3')))
      | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_460])).

tff(c_475,plain,(
    ! [C_157] :
      ( r2_hidden(k1_funct_1('#skF_4',C_157),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_157,k1_tarski('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_470])).

tff(c_477,plain,(
    ! [C_160] :
      ( r2_hidden(k1_funct_1('#skF_4',C_160),'#skF_4')
      | ~ r2_hidden(C_160,k1_tarski('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_270,c_475])).

tff(c_30,plain,(
    ! [B_16,A_15] :
      ( ~ r1_tarski(B_16,A_15)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_484,plain,(
    ! [C_160] :
      ( ~ r1_tarski('#skF_4',k1_funct_1('#skF_4',C_160))
      | ~ r2_hidden(C_160,k1_tarski('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_477,c_30])).

tff(c_492,plain,(
    ! [C_161] : ~ r2_hidden(C_161,k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_484])).

tff(c_496,plain,(
    k1_tarski('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_266,c_492])).

tff(c_500,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_444,c_496])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:18:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.26/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.84  
% 3.48/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.84  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_mcart_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.48/1.84  
% 3.48/1.84  %Foreground sorts:
% 3.48/1.84  
% 3.48/1.84  
% 3.48/1.84  %Background operators:
% 3.48/1.84  
% 3.48/1.84  
% 3.48/1.84  %Foreground operators:
% 3.48/1.84  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.48/1.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.48/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.48/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.48/1.84  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.48/1.84  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.48/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.48/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.48/1.84  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.48/1.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.48/1.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.48/1.84  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.48/1.84  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.48/1.84  tff('#skF_2', type, '#skF_2': $i).
% 3.48/1.84  tff('#skF_3', type, '#skF_3': $i).
% 3.48/1.84  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.48/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.48/1.84  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.48/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.48/1.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.48/1.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.48/1.84  tff('#skF_4', type, '#skF_4': $i).
% 3.48/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.48/1.84  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.48/1.84  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 3.48/1.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.48/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.48/1.84  
% 3.57/1.87  tff(f_123, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 3.57/1.87  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.57/1.87  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.57/1.87  tff(f_64, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.57/1.87  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.57/1.87  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.57/1.87  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.57/1.87  tff(f_39, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.57/1.87  tff(f_48, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.57/1.87  tff(f_99, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_mcart_1)).
% 3.57/1.87  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.57/1.87  tff(f_111, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 3.57/1.87  tff(f_69, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.57/1.87  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.57/1.87  tff(c_101, plain, (![C_59, A_60, B_61]: (v1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.57/1.87  tff(c_105, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_101])).
% 3.57/1.87  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.57/1.87  tff(c_26, plain, (![A_12]: (k1_relat_1(A_12)!=k1_xboole_0 | k1_xboole_0=A_12 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.57/1.87  tff(c_113, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_105, c_26])).
% 3.57/1.87  tff(c_115, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_113])).
% 3.57/1.87  tff(c_197, plain, (![B_95, A_96]: (k1_tarski(k1_funct_1(B_95, A_96))=k2_relat_1(B_95) | k1_tarski(A_96)!=k1_relat_1(B_95) | ~v1_funct_1(B_95) | ~v1_relat_1(B_95))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.57/1.87  tff(c_183, plain, (![A_87, B_88, C_89]: (k2_relset_1(A_87, B_88, C_89)=k2_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.57/1.87  tff(c_187, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_183])).
% 3.57/1.87  tff(c_48, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')!=k1_tarski(k1_funct_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.57/1.87  tff(c_188, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_187, c_48])).
% 3.57/1.87  tff(c_203, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_197, c_188])).
% 3.57/1.87  tff(c_219, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_56, c_203])).
% 3.57/1.87  tff(c_168, plain, (![C_74, A_75, B_76]: (v4_relat_1(C_74, A_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.57/1.87  tff(c_172, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_52, c_168])).
% 3.57/1.87  tff(c_140, plain, (![B_69, A_70]: (r1_tarski(k1_relat_1(B_69), A_70) | ~v4_relat_1(B_69, A_70) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.57/1.87  tff(c_10, plain, (![B_9, A_8]: (k1_tarski(B_9)=A_8 | k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_tarski(B_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.57/1.87  tff(c_222, plain, (![B_101, B_102]: (k1_tarski(B_101)=k1_relat_1(B_102) | k1_relat_1(B_102)=k1_xboole_0 | ~v4_relat_1(B_102, k1_tarski(B_101)) | ~v1_relat_1(B_102))), inference(resolution, [status(thm)], [c_140, c_10])).
% 3.57/1.87  tff(c_228, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_172, c_222])).
% 3.57/1.87  tff(c_231, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_105, c_228])).
% 3.57/1.87  tff(c_233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_115, c_219, c_231])).
% 3.57/1.87  tff(c_234, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_113])).
% 3.57/1.87  tff(c_24, plain, (![A_12]: (k2_relat_1(A_12)!=k1_xboole_0 | k1_xboole_0=A_12 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.57/1.87  tff(c_112, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_105, c_24])).
% 3.57/1.87  tff(c_114, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_112])).
% 3.57/1.87  tff(c_236, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_234, c_114])).
% 3.57/1.87  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.57/1.87  tff(c_242, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_234, c_234, c_20])).
% 3.57/1.87  tff(c_260, plain, $false, inference(negUnitSimplification, [status(thm)], [c_236, c_242])).
% 3.57/1.87  tff(c_261, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_112])).
% 3.57/1.87  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.57/1.87  tff(c_269, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_261, c_261, c_22])).
% 3.57/1.87  tff(c_262, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_112])).
% 3.57/1.87  tff(c_275, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_261, c_262])).
% 3.57/1.87  tff(c_420, plain, (![B_152, A_153]: (k1_tarski(k1_funct_1(B_152, A_153))=k2_relat_1(B_152) | k1_tarski(A_153)!=k1_relat_1(B_152) | ~v1_funct_1(B_152) | ~v1_relat_1(B_152))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.57/1.87  tff(c_389, plain, (![A_129, B_130, C_131]: (k2_relset_1(A_129, B_130, C_131)=k2_relat_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.57/1.87  tff(c_392, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_389])).
% 3.57/1.87  tff(c_394, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_275, c_392])).
% 3.57/1.87  tff(c_400, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_394, c_48])).
% 3.57/1.87  tff(c_429, plain, (k2_relat_1('#skF_4')!='#skF_4' | k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_420, c_400])).
% 3.57/1.87  tff(c_444, plain, (k1_tarski('#skF_2')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_105, c_56, c_269, c_275, c_429])).
% 3.57/1.87  tff(c_40, plain, (![A_26]: (r2_hidden('#skF_1'(A_26), A_26) | k1_xboole_0=A_26)), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.57/1.87  tff(c_266, plain, (![A_26]: (r2_hidden('#skF_1'(A_26), A_26) | A_26='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_261, c_40])).
% 3.57/1.87  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.57/1.87  tff(c_267, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_261, c_2])).
% 3.57/1.87  tff(c_50, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.57/1.87  tff(c_270, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_261, c_50])).
% 3.57/1.87  tff(c_54, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.57/1.87  tff(c_46, plain, (![D_47, C_46, A_44, B_45]: (r2_hidden(k1_funct_1(D_47, C_46), k2_relset_1(A_44, B_45, D_47)) | k1_xboole_0=B_45 | ~r2_hidden(C_46, A_44) | ~m1_subset_1(D_47, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))) | ~v1_funct_2(D_47, A_44, B_45) | ~v1_funct_1(D_47))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.57/1.87  tff(c_460, plain, (![D_156, C_157, A_158, B_159]: (r2_hidden(k1_funct_1(D_156, C_157), k2_relset_1(A_158, B_159, D_156)) | B_159='#skF_4' | ~r2_hidden(C_157, A_158) | ~m1_subset_1(D_156, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))) | ~v1_funct_2(D_156, A_158, B_159) | ~v1_funct_1(D_156))), inference(demodulation, [status(thm), theory('equality')], [c_261, c_46])).
% 3.57/1.87  tff(c_470, plain, (![C_157]: (r2_hidden(k1_funct_1('#skF_4', C_157), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_157, k1_tarski('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_394, c_460])).
% 3.57/1.87  tff(c_475, plain, (![C_157]: (r2_hidden(k1_funct_1('#skF_4', C_157), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_157, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_470])).
% 3.57/1.87  tff(c_477, plain, (![C_160]: (r2_hidden(k1_funct_1('#skF_4', C_160), '#skF_4') | ~r2_hidden(C_160, k1_tarski('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_270, c_475])).
% 3.57/1.87  tff(c_30, plain, (![B_16, A_15]: (~r1_tarski(B_16, A_15) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.57/1.87  tff(c_484, plain, (![C_160]: (~r1_tarski('#skF_4', k1_funct_1('#skF_4', C_160)) | ~r2_hidden(C_160, k1_tarski('#skF_2')))), inference(resolution, [status(thm)], [c_477, c_30])).
% 3.57/1.87  tff(c_492, plain, (![C_161]: (~r2_hidden(C_161, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_267, c_484])).
% 3.57/1.87  tff(c_496, plain, (k1_tarski('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_266, c_492])).
% 3.57/1.87  tff(c_500, plain, $false, inference(negUnitSimplification, [status(thm)], [c_444, c_496])).
% 3.57/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.87  
% 3.57/1.87  Inference rules
% 3.57/1.87  ----------------------
% 3.57/1.87  #Ref     : 0
% 3.57/1.87  #Sup     : 90
% 3.57/1.87  #Fact    : 0
% 3.57/1.87  #Define  : 0
% 3.57/1.87  #Split   : 3
% 3.57/1.87  #Chain   : 0
% 3.57/1.87  #Close   : 0
% 3.57/1.87  
% 3.57/1.87  Ordering : KBO
% 3.57/1.87  
% 3.57/1.87  Simplification rules
% 3.57/1.87  ----------------------
% 3.57/1.87  #Subsume      : 5
% 3.57/1.87  #Demod        : 73
% 3.57/1.87  #Tautology    : 51
% 3.57/1.87  #SimpNegUnit  : 4
% 3.57/1.87  #BackRed      : 19
% 3.57/1.87  
% 3.57/1.87  #Partial instantiations: 0
% 3.57/1.87  #Strategies tried      : 1
% 3.57/1.87  
% 3.57/1.87  Timing (in seconds)
% 3.57/1.87  ----------------------
% 3.57/1.87  Preprocessing        : 0.55
% 3.57/1.87  Parsing              : 0.28
% 3.57/1.87  CNF conversion       : 0.04
% 3.57/1.87  Main loop            : 0.47
% 3.57/1.87  Inferencing          : 0.17
% 3.57/1.88  Reduction            : 0.15
% 3.57/1.88  Demodulation         : 0.11
% 3.57/1.88  BG Simplification    : 0.03
% 3.57/1.88  Subsumption          : 0.08
% 3.57/1.88  Abstraction          : 0.02
% 3.57/1.88  MUC search           : 0.00
% 3.57/1.88  Cooper               : 0.00
% 3.57/1.88  Total                : 1.08
% 3.57/1.88  Index Insertion      : 0.00
% 3.57/1.88  Index Deletion       : 0.00
% 3.57/1.88  Index Matching       : 0.00
% 3.57/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
