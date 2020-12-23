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
% DateTime   : Thu Dec  3 10:16:34 EST 2020

% Result     : Theorem 4.14s
% Output     : CNFRefutation 4.30s
% Verified   : 
% Statistics : Number of formulae       :  110 (1281 expanded)
%              Number of leaves         :   38 ( 452 expanded)
%              Depth                    :   14
%              Number of atoms          :  186 (3856 expanded)
%              Number of equality atoms :   56 (1311 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_103,axiom,(
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
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_80,plain,(
    ! [C_57,A_58,B_59] :
      ( v1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_89,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_80])).

tff(c_186,plain,(
    ! [A_96,B_97,C_98,D_99] :
      ( k7_relset_1(A_96,B_97,C_98,D_99) = k9_relat_1(C_98,D_99)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_193,plain,(
    ! [D_99] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_99) = k9_relat_1('#skF_7',D_99) ),
    inference(resolution,[status(thm)],[c_54,c_186])).

tff(c_52,plain,(
    r2_hidden('#skF_8',k7_relset_1('#skF_4','#skF_5','#skF_7','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_196,plain,(
    r2_hidden('#skF_8',k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_52])).

tff(c_143,plain,(
    ! [A_77,B_78,C_79] :
      ( r2_hidden('#skF_1'(A_77,B_78,C_79),B_78)
      | ~ r2_hidden(A_77,k9_relat_1(C_79,B_78))
      | ~ v1_relat_1(C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_50,plain,(
    ! [F_47] :
      ( k1_funct_1('#skF_7',F_47) != '#skF_8'
      | ~ r2_hidden(F_47,'#skF_6')
      | ~ m1_subset_1(F_47,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_154,plain,(
    ! [A_77,C_79] :
      ( k1_funct_1('#skF_7','#skF_1'(A_77,'#skF_6',C_79)) != '#skF_8'
      | ~ m1_subset_1('#skF_1'(A_77,'#skF_6',C_79),'#skF_4')
      | ~ r2_hidden(A_77,k9_relat_1(C_79,'#skF_6'))
      | ~ v1_relat_1(C_79) ) ),
    inference(resolution,[status(thm)],[c_143,c_50])).

tff(c_216,plain,
    ( k1_funct_1('#skF_7','#skF_1'('#skF_8','#skF_6','#skF_7')) != '#skF_8'
    | ~ m1_subset_1('#skF_1'('#skF_8','#skF_6','#skF_7'),'#skF_4')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_196,c_154])).

tff(c_228,plain,
    ( k1_funct_1('#skF_7','#skF_1'('#skF_8','#skF_6','#skF_7')) != '#skF_8'
    | ~ m1_subset_1('#skF_1'('#skF_8','#skF_6','#skF_7'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_216])).

tff(c_258,plain,(
    ~ m1_subset_1('#skF_1'('#skF_8','#skF_6','#skF_7'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_102,plain,(
    ! [A_64,B_65,C_66] :
      ( k1_relset_1(A_64,B_65,C_66) = k1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_111,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_102])).

tff(c_458,plain,(
    ! [A_152,B_153,C_154] :
      ( r2_hidden('#skF_2'(A_152,B_153,C_154),B_153)
      | k1_relset_1(B_153,A_152,C_154) = B_153
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(B_153,A_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_466,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_4','#skF_7'),'#skF_4')
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_54,c_458])).

tff(c_470,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_4','#skF_7'),'#skF_4')
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_466])).

tff(c_487,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_470])).

tff(c_259,plain,(
    ! [A_115,B_116,C_117] :
      ( r2_hidden('#skF_1'(A_115,B_116,C_117),k1_relat_1(C_117))
      | ~ r2_hidden(A_115,k9_relat_1(C_117,B_116))
      | ~ v1_relat_1(C_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,B_3)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_266,plain,(
    ! [A_115,B_116,C_117] :
      ( m1_subset_1('#skF_1'(A_115,B_116,C_117),k1_relat_1(C_117))
      | ~ r2_hidden(A_115,k9_relat_1(C_117,B_116))
      | ~ v1_relat_1(C_117) ) ),
    inference(resolution,[status(thm)],[c_259,c_4])).

tff(c_495,plain,(
    ! [A_115,B_116] :
      ( m1_subset_1('#skF_1'(A_115,B_116,'#skF_7'),'#skF_4')
      | ~ r2_hidden(A_115,k9_relat_1('#skF_7',B_116))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_266])).

tff(c_557,plain,(
    ! [A_164,B_165] :
      ( m1_subset_1('#skF_1'(A_164,B_165,'#skF_7'),'#skF_4')
      | ~ r2_hidden(A_164,k9_relat_1('#skF_7',B_165)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_495])).

tff(c_568,plain,(
    m1_subset_1('#skF_1'('#skF_8','#skF_6','#skF_7'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_196,c_557])).

tff(c_578,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_258,c_568])).

tff(c_580,plain,(
    k1_relat_1('#skF_7') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_470])).

tff(c_56,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_675,plain,(
    ! [B_183,A_184,C_185] :
      ( k1_xboole_0 = B_183
      | k1_relset_1(A_184,B_183,C_185) = A_184
      | ~ v1_funct_2(C_185,A_184,B_183)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_184,B_183))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_686,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_675])).

tff(c_691,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_111,c_686])).

tff(c_692,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_580,c_691])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_90,plain,(
    ! [A_60,A_61,B_62] :
      ( v1_relat_1(A_60)
      | ~ r1_tarski(A_60,k2_zfmisc_1(A_61,B_62)) ) ),
    inference(resolution,[status(thm)],[c_8,c_80])).

tff(c_100,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_90])).

tff(c_268,plain,(
    ! [A_118,B_119,C_120] :
      ( r2_hidden(k4_tarski('#skF_1'(A_118,B_119,C_120),A_118),C_120)
      | ~ r2_hidden(A_118,k9_relat_1(C_120,B_119))
      | ~ v1_relat_1(C_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( ~ r1_tarski(B_16,A_15)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_450,plain,(
    ! [C_149,A_150,B_151] :
      ( ~ r1_tarski(C_149,k4_tarski('#skF_1'(A_150,B_151,C_149),A_150))
      | ~ r2_hidden(A_150,k9_relat_1(C_149,B_151))
      | ~ v1_relat_1(C_149) ) ),
    inference(resolution,[status(thm)],[c_268,c_24])).

tff(c_454,plain,(
    ! [A_150,B_151] :
      ( ~ r2_hidden(A_150,k9_relat_1(k1_xboole_0,B_151))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2,c_450])).

tff(c_457,plain,(
    ! [A_150,B_151] : ~ r2_hidden(A_150,k9_relat_1(k1_xboole_0,B_151)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_454])).

tff(c_699,plain,(
    ! [A_150,B_151] : ~ r2_hidden(A_150,k9_relat_1('#skF_5',B_151)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_692,c_457])).

tff(c_62,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(A_53,B_54)
      | ~ m1_subset_1(A_53,k1_zfmisc_1(B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_66,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_54,c_62])).

tff(c_206,plain,(
    ! [C_101,A_102] :
      ( k1_xboole_0 = C_101
      | ~ v1_funct_2(C_101,A_102,k1_xboole_0)
      | k1_xboole_0 = A_102
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_102,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_211,plain,(
    ! [A_4,A_102] :
      ( k1_xboole_0 = A_4
      | ~ v1_funct_2(A_4,A_102,k1_xboole_0)
      | k1_xboole_0 = A_102
      | ~ r1_tarski(A_4,k2_zfmisc_1(A_102,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_8,c_206])).

tff(c_994,plain,(
    ! [A_224,A_225] :
      ( A_224 = '#skF_5'
      | ~ v1_funct_2(A_224,A_225,'#skF_5')
      | A_225 = '#skF_5'
      | ~ r1_tarski(A_224,k2_zfmisc_1(A_225,'#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_692,c_692,c_692,c_692,c_211])).

tff(c_1001,plain,
    ( '#skF_7' = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_66,c_994])).

tff(c_1006,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1001])).

tff(c_1024,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1006])).

tff(c_1049,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1024,c_56])).

tff(c_1047,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1024,c_66])).

tff(c_337,plain,(
    ! [B_134,C_135] :
      ( k1_relset_1(k1_xboole_0,B_134,C_135) = k1_xboole_0
      | ~ v1_funct_2(C_135,k1_xboole_0,B_134)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_342,plain,(
    ! [B_134,A_4] :
      ( k1_relset_1(k1_xboole_0,B_134,A_4) = k1_xboole_0
      | ~ v1_funct_2(A_4,k1_xboole_0,B_134)
      | ~ r1_tarski(A_4,k2_zfmisc_1(k1_xboole_0,B_134)) ) ),
    inference(resolution,[status(thm)],[c_8,c_337])).

tff(c_702,plain,(
    ! [B_134,A_4] :
      ( k1_relset_1('#skF_5',B_134,A_4) = '#skF_5'
      | ~ v1_funct_2(A_4,'#skF_5',B_134)
      | ~ r1_tarski(A_4,k2_zfmisc_1('#skF_5',B_134)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_692,c_692,c_692,c_692,c_342])).

tff(c_1093,plain,(
    ! [B_134,A_4] :
      ( k1_relset_1('#skF_4',B_134,A_4) = '#skF_4'
      | ~ v1_funct_2(A_4,'#skF_4',B_134)
      | ~ r1_tarski(A_4,k2_zfmisc_1('#skF_4',B_134)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1024,c_1024,c_1024,c_1024,c_702])).

tff(c_1103,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_1047,c_1093])).

tff(c_1114,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1049,c_1103])).

tff(c_1046,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_7') = k1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1024,c_111])).

tff(c_1171,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1114,c_1046])).

tff(c_1172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_580,c_1171])).

tff(c_1173,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1006])).

tff(c_1186,plain,(
    r2_hidden('#skF_8',k9_relat_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1173,c_196])).

tff(c_1199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_699,c_1186])).

tff(c_1200,plain,(
    k1_funct_1('#skF_7','#skF_1'('#skF_8','#skF_6','#skF_7')) != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_58,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1233,plain,(
    ! [A_249,B_250,C_251] :
      ( r2_hidden(k4_tarski('#skF_1'(A_249,B_250,C_251),A_249),C_251)
      | ~ r2_hidden(A_249,k9_relat_1(C_251,B_250))
      | ~ v1_relat_1(C_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_20,plain,(
    ! [C_14,A_12,B_13] :
      ( k1_funct_1(C_14,A_12) = B_13
      | ~ r2_hidden(k4_tarski(A_12,B_13),C_14)
      | ~ v1_funct_1(C_14)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1690,plain,(
    ! [C_312,A_313,B_314] :
      ( k1_funct_1(C_312,'#skF_1'(A_313,B_314,C_312)) = A_313
      | ~ v1_funct_1(C_312)
      | ~ r2_hidden(A_313,k9_relat_1(C_312,B_314))
      | ~ v1_relat_1(C_312) ) ),
    inference(resolution,[status(thm)],[c_1233,c_20])).

tff(c_1698,plain,
    ( k1_funct_1('#skF_7','#skF_1'('#skF_8','#skF_6','#skF_7')) = '#skF_8'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_196,c_1690])).

tff(c_1706,plain,(
    k1_funct_1('#skF_7','#skF_1'('#skF_8','#skF_6','#skF_7')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_58,c_1698])).

tff(c_1708,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1200,c_1706])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:26:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.14/1.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/1.79  
% 4.14/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/1.79  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4 > #skF_3
% 4.14/1.79  
% 4.14/1.79  %Foreground sorts:
% 4.14/1.79  
% 4.14/1.79  
% 4.14/1.79  %Background operators:
% 4.14/1.79  
% 4.14/1.79  
% 4.14/1.79  %Foreground operators:
% 4.14/1.79  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.14/1.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.14/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.14/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.14/1.79  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.14/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.14/1.79  tff('#skF_7', type, '#skF_7': $i).
% 4.14/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.14/1.79  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.14/1.79  tff('#skF_5', type, '#skF_5': $i).
% 4.14/1.79  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.14/1.79  tff('#skF_6', type, '#skF_6': $i).
% 4.14/1.79  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.14/1.79  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.14/1.79  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.14/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.14/1.79  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.14/1.79  tff('#skF_8', type, '#skF_8': $i).
% 4.14/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.14/1.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.14/1.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.14/1.79  tff('#skF_4', type, '#skF_4': $i).
% 4.14/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.14/1.79  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.14/1.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.14/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.14/1.79  
% 4.30/1.81  tff(f_122, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 4.30/1.81  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.30/1.81  tff(f_73, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.30/1.81  tff(f_46, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 4.30/1.81  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.30/1.81  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 4.30/1.81  tff(f_31, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 4.30/1.81  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.30/1.81  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.30/1.81  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.30/1.81  tff(f_61, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.30/1.81  tff(f_56, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 4.30/1.81  tff(c_54, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.30/1.81  tff(c_80, plain, (![C_57, A_58, B_59]: (v1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.30/1.81  tff(c_89, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_54, c_80])).
% 4.30/1.81  tff(c_186, plain, (![A_96, B_97, C_98, D_99]: (k7_relset_1(A_96, B_97, C_98, D_99)=k9_relat_1(C_98, D_99) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.30/1.81  tff(c_193, plain, (![D_99]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_99)=k9_relat_1('#skF_7', D_99))), inference(resolution, [status(thm)], [c_54, c_186])).
% 4.30/1.81  tff(c_52, plain, (r2_hidden('#skF_8', k7_relset_1('#skF_4', '#skF_5', '#skF_7', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.30/1.81  tff(c_196, plain, (r2_hidden('#skF_8', k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_52])).
% 4.30/1.81  tff(c_143, plain, (![A_77, B_78, C_79]: (r2_hidden('#skF_1'(A_77, B_78, C_79), B_78) | ~r2_hidden(A_77, k9_relat_1(C_79, B_78)) | ~v1_relat_1(C_79))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.30/1.81  tff(c_50, plain, (![F_47]: (k1_funct_1('#skF_7', F_47)!='#skF_8' | ~r2_hidden(F_47, '#skF_6') | ~m1_subset_1(F_47, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.30/1.81  tff(c_154, plain, (![A_77, C_79]: (k1_funct_1('#skF_7', '#skF_1'(A_77, '#skF_6', C_79))!='#skF_8' | ~m1_subset_1('#skF_1'(A_77, '#skF_6', C_79), '#skF_4') | ~r2_hidden(A_77, k9_relat_1(C_79, '#skF_6')) | ~v1_relat_1(C_79))), inference(resolution, [status(thm)], [c_143, c_50])).
% 4.30/1.81  tff(c_216, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_8', '#skF_6', '#skF_7'))!='#skF_8' | ~m1_subset_1('#skF_1'('#skF_8', '#skF_6', '#skF_7'), '#skF_4') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_196, c_154])).
% 4.30/1.81  tff(c_228, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_8', '#skF_6', '#skF_7'))!='#skF_8' | ~m1_subset_1('#skF_1'('#skF_8', '#skF_6', '#skF_7'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_216])).
% 4.30/1.81  tff(c_258, plain, (~m1_subset_1('#skF_1'('#skF_8', '#skF_6', '#skF_7'), '#skF_4')), inference(splitLeft, [status(thm)], [c_228])).
% 4.30/1.81  tff(c_102, plain, (![A_64, B_65, C_66]: (k1_relset_1(A_64, B_65, C_66)=k1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.30/1.81  tff(c_111, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_54, c_102])).
% 4.30/1.81  tff(c_458, plain, (![A_152, B_153, C_154]: (r2_hidden('#skF_2'(A_152, B_153, C_154), B_153) | k1_relset_1(B_153, A_152, C_154)=B_153 | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(B_153, A_152))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.30/1.81  tff(c_466, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_4', '#skF_7'), '#skF_4') | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4'), inference(resolution, [status(thm)], [c_54, c_458])).
% 4.30/1.81  tff(c_470, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_4', '#skF_7'), '#skF_4') | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_111, c_466])).
% 4.30/1.81  tff(c_487, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_470])).
% 4.30/1.81  tff(c_259, plain, (![A_115, B_116, C_117]: (r2_hidden('#skF_1'(A_115, B_116, C_117), k1_relat_1(C_117)) | ~r2_hidden(A_115, k9_relat_1(C_117, B_116)) | ~v1_relat_1(C_117))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.30/1.81  tff(c_4, plain, (![A_2, B_3]: (m1_subset_1(A_2, B_3) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.30/1.81  tff(c_266, plain, (![A_115, B_116, C_117]: (m1_subset_1('#skF_1'(A_115, B_116, C_117), k1_relat_1(C_117)) | ~r2_hidden(A_115, k9_relat_1(C_117, B_116)) | ~v1_relat_1(C_117))), inference(resolution, [status(thm)], [c_259, c_4])).
% 4.30/1.81  tff(c_495, plain, (![A_115, B_116]: (m1_subset_1('#skF_1'(A_115, B_116, '#skF_7'), '#skF_4') | ~r2_hidden(A_115, k9_relat_1('#skF_7', B_116)) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_487, c_266])).
% 4.30/1.81  tff(c_557, plain, (![A_164, B_165]: (m1_subset_1('#skF_1'(A_164, B_165, '#skF_7'), '#skF_4') | ~r2_hidden(A_164, k9_relat_1('#skF_7', B_165)))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_495])).
% 4.30/1.81  tff(c_568, plain, (m1_subset_1('#skF_1'('#skF_8', '#skF_6', '#skF_7'), '#skF_4')), inference(resolution, [status(thm)], [c_196, c_557])).
% 4.30/1.81  tff(c_578, plain, $false, inference(negUnitSimplification, [status(thm)], [c_258, c_568])).
% 4.30/1.81  tff(c_580, plain, (k1_relat_1('#skF_7')!='#skF_4'), inference(splitRight, [status(thm)], [c_470])).
% 4.30/1.81  tff(c_56, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.30/1.81  tff(c_675, plain, (![B_183, A_184, C_185]: (k1_xboole_0=B_183 | k1_relset_1(A_184, B_183, C_185)=A_184 | ~v1_funct_2(C_185, A_184, B_183) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_184, B_183))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.30/1.81  tff(c_686, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_675])).
% 4.30/1.81  tff(c_691, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_111, c_686])).
% 4.30/1.81  tff(c_692, plain, (k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_580, c_691])).
% 4.30/1.81  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.30/1.81  tff(c_8, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.30/1.81  tff(c_90, plain, (![A_60, A_61, B_62]: (v1_relat_1(A_60) | ~r1_tarski(A_60, k2_zfmisc_1(A_61, B_62)))), inference(resolution, [status(thm)], [c_8, c_80])).
% 4.30/1.81  tff(c_100, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_90])).
% 4.30/1.81  tff(c_268, plain, (![A_118, B_119, C_120]: (r2_hidden(k4_tarski('#skF_1'(A_118, B_119, C_120), A_118), C_120) | ~r2_hidden(A_118, k9_relat_1(C_120, B_119)) | ~v1_relat_1(C_120))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.30/1.81  tff(c_24, plain, (![B_16, A_15]: (~r1_tarski(B_16, A_15) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.30/1.81  tff(c_450, plain, (![C_149, A_150, B_151]: (~r1_tarski(C_149, k4_tarski('#skF_1'(A_150, B_151, C_149), A_150)) | ~r2_hidden(A_150, k9_relat_1(C_149, B_151)) | ~v1_relat_1(C_149))), inference(resolution, [status(thm)], [c_268, c_24])).
% 4.30/1.81  tff(c_454, plain, (![A_150, B_151]: (~r2_hidden(A_150, k9_relat_1(k1_xboole_0, B_151)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_450])).
% 4.30/1.81  tff(c_457, plain, (![A_150, B_151]: (~r2_hidden(A_150, k9_relat_1(k1_xboole_0, B_151)))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_454])).
% 4.30/1.81  tff(c_699, plain, (![A_150, B_151]: (~r2_hidden(A_150, k9_relat_1('#skF_5', B_151)))), inference(demodulation, [status(thm), theory('equality')], [c_692, c_457])).
% 4.30/1.81  tff(c_62, plain, (![A_53, B_54]: (r1_tarski(A_53, B_54) | ~m1_subset_1(A_53, k1_zfmisc_1(B_54)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.30/1.81  tff(c_66, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_54, c_62])).
% 4.30/1.81  tff(c_206, plain, (![C_101, A_102]: (k1_xboole_0=C_101 | ~v1_funct_2(C_101, A_102, k1_xboole_0) | k1_xboole_0=A_102 | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_102, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.30/1.81  tff(c_211, plain, (![A_4, A_102]: (k1_xboole_0=A_4 | ~v1_funct_2(A_4, A_102, k1_xboole_0) | k1_xboole_0=A_102 | ~r1_tarski(A_4, k2_zfmisc_1(A_102, k1_xboole_0)))), inference(resolution, [status(thm)], [c_8, c_206])).
% 4.30/1.81  tff(c_994, plain, (![A_224, A_225]: (A_224='#skF_5' | ~v1_funct_2(A_224, A_225, '#skF_5') | A_225='#skF_5' | ~r1_tarski(A_224, k2_zfmisc_1(A_225, '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_692, c_692, c_692, c_692, c_211])).
% 4.30/1.81  tff(c_1001, plain, ('#skF_7'='#skF_5' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_66, c_994])).
% 4.30/1.81  tff(c_1006, plain, ('#skF_7'='#skF_5' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1001])).
% 4.30/1.81  tff(c_1024, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_1006])).
% 4.30/1.81  tff(c_1049, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1024, c_56])).
% 4.30/1.81  tff(c_1047, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1024, c_66])).
% 4.30/1.81  tff(c_337, plain, (![B_134, C_135]: (k1_relset_1(k1_xboole_0, B_134, C_135)=k1_xboole_0 | ~v1_funct_2(C_135, k1_xboole_0, B_134) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_134))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.30/1.81  tff(c_342, plain, (![B_134, A_4]: (k1_relset_1(k1_xboole_0, B_134, A_4)=k1_xboole_0 | ~v1_funct_2(A_4, k1_xboole_0, B_134) | ~r1_tarski(A_4, k2_zfmisc_1(k1_xboole_0, B_134)))), inference(resolution, [status(thm)], [c_8, c_337])).
% 4.30/1.81  tff(c_702, plain, (![B_134, A_4]: (k1_relset_1('#skF_5', B_134, A_4)='#skF_5' | ~v1_funct_2(A_4, '#skF_5', B_134) | ~r1_tarski(A_4, k2_zfmisc_1('#skF_5', B_134)))), inference(demodulation, [status(thm), theory('equality')], [c_692, c_692, c_692, c_692, c_342])).
% 4.30/1.81  tff(c_1093, plain, (![B_134, A_4]: (k1_relset_1('#skF_4', B_134, A_4)='#skF_4' | ~v1_funct_2(A_4, '#skF_4', B_134) | ~r1_tarski(A_4, k2_zfmisc_1('#skF_4', B_134)))), inference(demodulation, [status(thm), theory('equality')], [c_1024, c_1024, c_1024, c_1024, c_702])).
% 4.30/1.81  tff(c_1103, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_1047, c_1093])).
% 4.30/1.81  tff(c_1114, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1049, c_1103])).
% 4.30/1.81  tff(c_1046, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_7')=k1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1024, c_111])).
% 4.30/1.81  tff(c_1171, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1114, c_1046])).
% 4.30/1.81  tff(c_1172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_580, c_1171])).
% 4.30/1.81  tff(c_1173, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_1006])).
% 4.30/1.81  tff(c_1186, plain, (r2_hidden('#skF_8', k9_relat_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1173, c_196])).
% 4.30/1.81  tff(c_1199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_699, c_1186])).
% 4.30/1.81  tff(c_1200, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_8', '#skF_6', '#skF_7'))!='#skF_8'), inference(splitRight, [status(thm)], [c_228])).
% 4.30/1.81  tff(c_58, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.30/1.81  tff(c_1233, plain, (![A_249, B_250, C_251]: (r2_hidden(k4_tarski('#skF_1'(A_249, B_250, C_251), A_249), C_251) | ~r2_hidden(A_249, k9_relat_1(C_251, B_250)) | ~v1_relat_1(C_251))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.30/1.81  tff(c_20, plain, (![C_14, A_12, B_13]: (k1_funct_1(C_14, A_12)=B_13 | ~r2_hidden(k4_tarski(A_12, B_13), C_14) | ~v1_funct_1(C_14) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.30/1.81  tff(c_1690, plain, (![C_312, A_313, B_314]: (k1_funct_1(C_312, '#skF_1'(A_313, B_314, C_312))=A_313 | ~v1_funct_1(C_312) | ~r2_hidden(A_313, k9_relat_1(C_312, B_314)) | ~v1_relat_1(C_312))), inference(resolution, [status(thm)], [c_1233, c_20])).
% 4.30/1.81  tff(c_1698, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_8', '#skF_6', '#skF_7'))='#skF_8' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_196, c_1690])).
% 4.30/1.81  tff(c_1706, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_8', '#skF_6', '#skF_7'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_89, c_58, c_1698])).
% 4.30/1.81  tff(c_1708, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1200, c_1706])).
% 4.30/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.30/1.81  
% 4.30/1.81  Inference rules
% 4.30/1.81  ----------------------
% 4.30/1.81  #Ref     : 0
% 4.30/1.81  #Sup     : 312
% 4.30/1.81  #Fact    : 0
% 4.30/1.81  #Define  : 0
% 4.30/1.81  #Split   : 11
% 4.30/1.81  #Chain   : 0
% 4.30/1.81  #Close   : 0
% 4.30/1.81  
% 4.30/1.81  Ordering : KBO
% 4.30/1.81  
% 4.30/1.81  Simplification rules
% 4.30/1.81  ----------------------
% 4.30/1.81  #Subsume      : 21
% 4.30/1.81  #Demod        : 177
% 4.30/1.81  #Tautology    : 54
% 4.30/1.81  #SimpNegUnit  : 7
% 4.30/1.81  #BackRed      : 77
% 4.30/1.81  
% 4.30/1.81  #Partial instantiations: 0
% 4.30/1.81  #Strategies tried      : 1
% 4.30/1.81  
% 4.30/1.81  Timing (in seconds)
% 4.30/1.81  ----------------------
% 4.30/1.82  Preprocessing        : 0.38
% 4.30/1.82  Parsing              : 0.20
% 4.30/1.82  CNF conversion       : 0.03
% 4.30/1.82  Main loop            : 0.57
% 4.30/1.82  Inferencing          : 0.20
% 4.30/1.82  Reduction            : 0.16
% 4.30/1.82  Demodulation         : 0.11
% 4.30/1.82  BG Simplification    : 0.03
% 4.30/1.82  Subsumption          : 0.12
% 4.30/1.82  Abstraction          : 0.03
% 4.30/1.82  MUC search           : 0.00
% 4.30/1.82  Cooper               : 0.00
% 4.30/1.82  Total                : 0.99
% 4.30/1.82  Index Insertion      : 0.00
% 4.30/1.82  Index Deletion       : 0.00
% 4.30/1.82  Index Matching       : 0.00
% 4.30/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
