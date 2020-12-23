%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:23 EST 2020

% Result     : Theorem 3.76s
% Output     : CNFRefutation 4.05s
% Verified   : 
% Statistics : Number of formulae       :  136 (1032 expanded)
%              Number of leaves         :   41 ( 366 expanded)
%              Depth                    :   16
%              Number of atoms          :  221 (3003 expanded)
%              Number of equality atoms :   97 (1292 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_10 > #skF_4 > #skF_3 > #skF_13 > #skF_9 > #skF_14 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(E,D),C) )
      <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).

tff(f_65,axiom,(
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

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_57,axiom,(
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

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_36,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(c_66,plain,(
    m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_11','#skF_12'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_111,plain,(
    ! [A_101,B_102,C_103] :
      ( k2_relset_1(A_101,B_102,C_103) = k2_relat_1(C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_115,plain,(
    k2_relset_1('#skF_11','#skF_12','#skF_13') = k2_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_66,c_111])).

tff(c_64,plain,(
    k2_relset_1('#skF_11','#skF_12','#skF_13') != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_116,plain,(
    k2_relat_1('#skF_13') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_64])).

tff(c_188,plain,(
    ! [A_129,B_130,C_131] :
      ( r2_hidden('#skF_9'(A_129,B_130,C_131),B_130)
      | k2_relset_1(A_129,B_130,C_131) = B_130
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_190,plain,
    ( r2_hidden('#skF_9'('#skF_11','#skF_12','#skF_13'),'#skF_12')
    | k2_relset_1('#skF_11','#skF_12','#skF_13') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_66,c_188])).

tff(c_192,plain,
    ( r2_hidden('#skF_9'('#skF_11','#skF_12','#skF_13'),'#skF_12')
    | k2_relat_1('#skF_13') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_190])).

tff(c_193,plain,(
    r2_hidden('#skF_9'('#skF_11','#skF_12','#skF_13'),'#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_192])).

tff(c_74,plain,(
    ! [D_89] :
      ( r2_hidden('#skF_14'(D_89),'#skF_11')
      | ~ r2_hidden(D_89,'#skF_12') ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_68,plain,(
    v1_funct_2('#skF_13','#skF_11','#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_122,plain,(
    ! [A_105,B_106,C_107] :
      ( k1_relset_1(A_105,B_106,C_107) = k1_relat_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_126,plain,(
    k1_relset_1('#skF_11','#skF_12','#skF_13') = k1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_66,c_122])).

tff(c_194,plain,(
    ! [B_132,A_133,C_134] :
      ( k1_xboole_0 = B_132
      | k1_relset_1(A_133,B_132,C_134) = A_133
      | ~ v1_funct_2(C_134,A_133,B_132)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_133,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_197,plain,
    ( k1_xboole_0 = '#skF_12'
    | k1_relset_1('#skF_11','#skF_12','#skF_13') = '#skF_11'
    | ~ v1_funct_2('#skF_13','#skF_11','#skF_12') ),
    inference(resolution,[status(thm)],[c_66,c_194])).

tff(c_200,plain,
    ( k1_xboole_0 = '#skF_12'
    | k1_relat_1('#skF_13') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_126,c_197])).

tff(c_201,plain,(
    k1_relat_1('#skF_13') = '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_200])).

tff(c_95,plain,(
    ! [C_95,A_96,B_97] :
      ( v1_relat_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_99,plain,(
    v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_66,c_95])).

tff(c_70,plain,(
    v1_funct_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_72,plain,(
    ! [D_89] :
      ( k1_funct_1('#skF_13','#skF_14'(D_89)) = D_89
      | ~ r2_hidden(D_89,'#skF_12') ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_147,plain,(
    ! [A_113,D_114] :
      ( r2_hidden(k1_funct_1(A_113,D_114),k2_relat_1(A_113))
      | ~ r2_hidden(D_114,k1_relat_1(A_113))
      | ~ v1_funct_1(A_113)
      | ~ v1_relat_1(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_150,plain,(
    ! [D_89] :
      ( r2_hidden(D_89,k2_relat_1('#skF_13'))
      | ~ r2_hidden('#skF_14'(D_89),k1_relat_1('#skF_13'))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13')
      | ~ r2_hidden(D_89,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_147])).

tff(c_155,plain,(
    ! [D_89] :
      ( r2_hidden(D_89,k2_relat_1('#skF_13'))
      | ~ r2_hidden('#skF_14'(D_89),k1_relat_1('#skF_13'))
      | ~ r2_hidden(D_89,'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_70,c_150])).

tff(c_218,plain,(
    ! [D_135] :
      ( r2_hidden(D_135,k2_relat_1('#skF_13'))
      | ~ r2_hidden('#skF_14'(D_135),'#skF_11')
      | ~ r2_hidden(D_135,'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_155])).

tff(c_222,plain,(
    ! [D_89] :
      ( r2_hidden(D_89,k2_relat_1('#skF_13'))
      | ~ r2_hidden(D_89,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_74,c_218])).

tff(c_2,plain,(
    ! [A_1,C_16] :
      ( r2_hidden(k4_tarski('#skF_4'(A_1,k2_relat_1(A_1),C_16),C_16),A_1)
      | ~ r2_hidden(C_16,k2_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_456,plain,(
    ! [E_170,A_171,B_172,C_173] :
      ( ~ r2_hidden(k4_tarski(E_170,'#skF_9'(A_171,B_172,C_173)),C_173)
      | k2_relset_1(A_171,B_172,C_173) = B_172
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_498,plain,(
    ! [A_176,B_177,A_178] :
      ( k2_relset_1(A_176,B_177,A_178) = B_177
      | ~ m1_subset_1(A_178,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177)))
      | ~ r2_hidden('#skF_9'(A_176,B_177,A_178),k2_relat_1(A_178)) ) ),
    inference(resolution,[status(thm)],[c_2,c_456])).

tff(c_532,plain,(
    ! [A_179,B_180] :
      ( k2_relset_1(A_179,B_180,'#skF_13') = B_180
      | ~ m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1(A_179,B_180)))
      | ~ r2_hidden('#skF_9'(A_179,B_180,'#skF_13'),'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_222,c_498])).

tff(c_535,plain,
    ( k2_relset_1('#skF_11','#skF_12','#skF_13') = '#skF_12'
    | ~ r2_hidden('#skF_9'('#skF_11','#skF_12','#skF_13'),'#skF_12') ),
    inference(resolution,[status(thm)],[c_66,c_532])).

tff(c_538,plain,(
    k2_relat_1('#skF_13') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_115,c_535])).

tff(c_540,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_538])).

tff(c_541,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_16,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_562,plain,(
    k1_relat_1('#skF_12') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_541,c_16])).

tff(c_18,plain,(
    ! [A_20] :
      ( k1_relat_1(A_20) = k1_xboole_0
      | k2_relat_1(A_20) != k1_xboole_0
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_106,plain,
    ( k1_relat_1('#skF_13') = k1_xboole_0
    | k2_relat_1('#skF_13') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_99,c_18])).

tff(c_108,plain,(
    k2_relat_1('#skF_13') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_20,plain,(
    ! [A_20] :
      ( k2_relat_1(A_20) = k1_xboole_0
      | k1_relat_1(A_20) != k1_xboole_0
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_107,plain,
    ( k2_relat_1('#skF_13') = k1_xboole_0
    | k1_relat_1('#skF_13') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_99,c_20])).

tff(c_109,plain,(
    k1_relat_1('#skF_13') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_107])).

tff(c_557,plain,(
    k1_relat_1('#skF_13') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_109])).

tff(c_54,plain,(
    ! [C_85,A_83] :
      ( k1_xboole_0 = C_85
      | ~ v1_funct_2(C_85,A_83,k1_xboole_0)
      | k1_xboole_0 = A_83
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_626,plain,(
    ! [C_195,A_196] :
      ( C_195 = '#skF_12'
      | ~ v1_funct_2(C_195,A_196,'#skF_12')
      | A_196 = '#skF_12'
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_196,'#skF_12'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_541,c_541,c_541,c_54])).

tff(c_629,plain,
    ( '#skF_13' = '#skF_12'
    | ~ v1_funct_2('#skF_13','#skF_11','#skF_12')
    | '#skF_11' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_66,c_626])).

tff(c_632,plain,
    ( '#skF_13' = '#skF_12'
    | '#skF_11' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_629])).

tff(c_633,plain,(
    '#skF_11' = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_632])).

tff(c_640,plain,(
    v1_funct_2('#skF_13','#skF_12','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_633,c_68])).

tff(c_636,plain,(
    k1_relset_1('#skF_12','#skF_12','#skF_13') = k1_relat_1('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_633,c_126])).

tff(c_639,plain,(
    m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_12','#skF_12'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_633,c_66])).

tff(c_60,plain,(
    ! [B_84,C_85] :
      ( k1_relset_1(k1_xboole_0,B_84,C_85) = k1_xboole_0
      | ~ v1_funct_2(C_85,k1_xboole_0,B_84)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_685,plain,(
    ! [B_200,C_201] :
      ( k1_relset_1('#skF_12',B_200,C_201) = '#skF_12'
      | ~ v1_funct_2(C_201,'#skF_12',B_200)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1('#skF_12',B_200))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_541,c_541,c_541,c_60])).

tff(c_688,plain,
    ( k1_relset_1('#skF_12','#skF_12','#skF_13') = '#skF_12'
    | ~ v1_funct_2('#skF_13','#skF_12','#skF_12') ),
    inference(resolution,[status(thm)],[c_639,c_685])).

tff(c_691,plain,(
    k1_relat_1('#skF_13') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_640,c_636,c_688])).

tff(c_693,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_557,c_691])).

tff(c_694,plain,(
    '#skF_13' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_632])).

tff(c_696,plain,(
    k1_relat_1('#skF_12') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_694,c_557])).

tff(c_710,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_562,c_696])).

tff(c_712,plain,(
    k2_relat_1('#skF_13') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_735,plain,(
    ! [A_209,B_210,C_211] :
      ( k2_relset_1(A_209,B_210,C_211) = k2_relat_1(C_211)
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(A_209,B_210))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_738,plain,(
    k2_relset_1('#skF_11','#skF_12','#skF_13') = k2_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_66,c_735])).

tff(c_740,plain,(
    k2_relset_1('#skF_11','#skF_12','#skF_13') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_712,c_738])).

tff(c_741,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_740,c_64])).

tff(c_711,plain,(
    k1_relat_1('#skF_13') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_724,plain,(
    ! [A_205,B_206,C_207] :
      ( k1_relset_1(A_205,B_206,C_207) = k1_relat_1(C_207)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_205,B_206))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_727,plain,(
    k1_relset_1('#skF_11','#skF_12','#skF_13') = k1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_66,c_724])).

tff(c_729,plain,(
    k1_relset_1('#skF_11','#skF_12','#skF_13') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_711,c_727])).

tff(c_886,plain,(
    ! [B_248,A_249,C_250] :
      ( k1_xboole_0 = B_248
      | k1_relset_1(A_249,B_248,C_250) = A_249
      | ~ v1_funct_2(C_250,A_249,B_248)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(A_249,B_248))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_889,plain,
    ( k1_xboole_0 = '#skF_12'
    | k1_relset_1('#skF_11','#skF_12','#skF_13') = '#skF_11'
    | ~ v1_funct_2('#skF_13','#skF_11','#skF_12') ),
    inference(resolution,[status(thm)],[c_66,c_886])).

tff(c_892,plain,
    ( k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_729,c_889])).

tff(c_893,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(negUnitSimplification,[status(thm)],[c_741,c_892])).

tff(c_908,plain,(
    '#skF_11' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_893,c_741])).

tff(c_945,plain,(
    ! [A_251,B_252,C_253] :
      ( r2_hidden('#skF_9'(A_251,B_252,C_253),B_252)
      | k2_relset_1(A_251,B_252,C_253) = B_252
      | ~ m1_subset_1(C_253,k1_zfmisc_1(k2_zfmisc_1(A_251,B_252))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_948,plain,
    ( r2_hidden('#skF_9'('#skF_11','#skF_12','#skF_13'),'#skF_12')
    | k2_relset_1('#skF_11','#skF_12','#skF_13') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_66,c_945])).

tff(c_993,plain,(
    k2_relset_1('#skF_11','#skF_12','#skF_13') = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_948])).

tff(c_909,plain,(
    k2_relset_1('#skF_11','#skF_12','#skF_13') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_893,c_740])).

tff(c_1002,plain,(
    '#skF_11' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_993,c_909])).

tff(c_1003,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_908,c_1002])).

tff(c_1004,plain,(
    r2_hidden('#skF_9'('#skF_11','#skF_12','#skF_13'),'#skF_12') ),
    inference(splitRight,[status(thm)],[c_948])).

tff(c_772,plain,(
    ! [A_218,D_219] :
      ( r2_hidden(k1_funct_1(A_218,D_219),k2_relat_1(A_218))
      | ~ r2_hidden(D_219,k1_relat_1(A_218))
      | ~ v1_funct_1(A_218)
      | ~ v1_relat_1(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_778,plain,(
    ! [D_89] :
      ( r2_hidden(D_89,k2_relat_1('#skF_13'))
      | ~ r2_hidden('#skF_14'(D_89),k1_relat_1('#skF_13'))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13')
      | ~ r2_hidden(D_89,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_772])).

tff(c_785,plain,(
    ! [D_89] :
      ( r2_hidden(D_89,k1_xboole_0)
      | ~ r2_hidden('#skF_14'(D_89),k1_xboole_0)
      | ~ r2_hidden(D_89,'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_70,c_711,c_712,c_778])).

tff(c_1032,plain,(
    ! [D_257] :
      ( r2_hidden(D_257,'#skF_11')
      | ~ r2_hidden('#skF_14'(D_257),'#skF_11')
      | ~ r2_hidden(D_257,'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_893,c_893,c_785])).

tff(c_1036,plain,(
    ! [D_89] :
      ( r2_hidden(D_89,'#skF_11')
      | ~ r2_hidden(D_89,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_74,c_1032])).

tff(c_912,plain,(
    k2_relat_1('#skF_13') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_893,c_712])).

tff(c_981,plain,(
    ! [C_16] :
      ( r2_hidden(k4_tarski('#skF_4'('#skF_13','#skF_11',C_16),C_16),'#skF_13')
      | ~ r2_hidden(C_16,k2_relat_1('#skF_13')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_912,c_2])).

tff(c_991,plain,(
    ! [C_16] :
      ( r2_hidden(k4_tarski('#skF_4'('#skF_13','#skF_11',C_16),C_16),'#skF_13')
      | ~ r2_hidden(C_16,'#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_912,c_981])).

tff(c_1188,plain,(
    ! [E_273,A_274,B_275,C_276] :
      ( ~ r2_hidden(k4_tarski(E_273,'#skF_9'(A_274,B_275,C_276)),C_276)
      | k2_relset_1(A_274,B_275,C_276) = B_275
      | ~ m1_subset_1(C_276,k1_zfmisc_1(k2_zfmisc_1(A_274,B_275))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1615,plain,(
    ! [A_327,B_328] :
      ( k2_relset_1(A_327,B_328,'#skF_13') = B_328
      | ~ m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1(A_327,B_328)))
      | ~ r2_hidden('#skF_9'(A_327,B_328,'#skF_13'),'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_991,c_1188])).

tff(c_1618,plain,
    ( k2_relset_1('#skF_11','#skF_12','#skF_13') = '#skF_12'
    | ~ r2_hidden('#skF_9'('#skF_11','#skF_12','#skF_13'),'#skF_11') ),
    inference(resolution,[status(thm)],[c_66,c_1615])).

tff(c_1620,plain,
    ( '#skF_11' = '#skF_12'
    | ~ r2_hidden('#skF_9'('#skF_11','#skF_12','#skF_13'),'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_909,c_1618])).

tff(c_1621,plain,(
    ~ r2_hidden('#skF_9'('#skF_11','#skF_12','#skF_13'),'#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_908,c_1620])).

tff(c_1624,plain,(
    ~ r2_hidden('#skF_9'('#skF_11','#skF_12','#skF_13'),'#skF_12') ),
    inference(resolution,[status(thm)],[c_1036,c_1621])).

tff(c_1628,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_1624])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:41:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.76/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.76/1.68  
% 3.76/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.05/1.68  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_10 > #skF_4 > #skF_3 > #skF_13 > #skF_9 > #skF_14 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_12
% 4.05/1.68  
% 4.05/1.68  %Foreground sorts:
% 4.05/1.68  
% 4.05/1.68  
% 4.05/1.68  %Background operators:
% 4.05/1.68  
% 4.05/1.68  
% 4.05/1.68  %Foreground operators:
% 4.05/1.68  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.05/1.68  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.05/1.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.05/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.05/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.05/1.68  tff('#skF_11', type, '#skF_11': $i).
% 4.05/1.68  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.05/1.68  tff('#skF_10', type, '#skF_10': ($i * $i * $i * $i) > $i).
% 4.05/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.05/1.68  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.05/1.68  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.05/1.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.05/1.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.05/1.68  tff('#skF_13', type, '#skF_13': $i).
% 4.05/1.68  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.05/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.05/1.68  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.05/1.68  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 4.05/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.05/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.05/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.05/1.68  tff('#skF_14', type, '#skF_14': $i > $i).
% 4.05/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.05/1.68  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.05/1.68  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 4.05/1.68  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 4.05/1.68  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.05/1.68  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.05/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.05/1.68  tff('#skF_12', type, '#skF_12': $i).
% 4.05/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.05/1.68  
% 4.05/1.71  tff(f_118, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 4.05/1.71  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.05/1.71  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(E, D), C)))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_relset_1)).
% 4.05/1.71  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.05/1.71  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.05/1.71  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.05/1.71  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 4.05/1.71  tff(f_33, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 4.05/1.71  tff(f_36, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 4.05/1.71  tff(f_42, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 4.05/1.71  tff(c_66, plain, (m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_11', '#skF_12')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.05/1.71  tff(c_111, plain, (![A_101, B_102, C_103]: (k2_relset_1(A_101, B_102, C_103)=k2_relat_1(C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.05/1.71  tff(c_115, plain, (k2_relset_1('#skF_11', '#skF_12', '#skF_13')=k2_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_66, c_111])).
% 4.05/1.71  tff(c_64, plain, (k2_relset_1('#skF_11', '#skF_12', '#skF_13')!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.05/1.71  tff(c_116, plain, (k2_relat_1('#skF_13')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_115, c_64])).
% 4.05/1.71  tff(c_188, plain, (![A_129, B_130, C_131]: (r2_hidden('#skF_9'(A_129, B_130, C_131), B_130) | k2_relset_1(A_129, B_130, C_131)=B_130 | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.05/1.71  tff(c_190, plain, (r2_hidden('#skF_9'('#skF_11', '#skF_12', '#skF_13'), '#skF_12') | k2_relset_1('#skF_11', '#skF_12', '#skF_13')='#skF_12'), inference(resolution, [status(thm)], [c_66, c_188])).
% 4.05/1.71  tff(c_192, plain, (r2_hidden('#skF_9'('#skF_11', '#skF_12', '#skF_13'), '#skF_12') | k2_relat_1('#skF_13')='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_115, c_190])).
% 4.05/1.71  tff(c_193, plain, (r2_hidden('#skF_9'('#skF_11', '#skF_12', '#skF_13'), '#skF_12')), inference(negUnitSimplification, [status(thm)], [c_116, c_192])).
% 4.05/1.71  tff(c_74, plain, (![D_89]: (r2_hidden('#skF_14'(D_89), '#skF_11') | ~r2_hidden(D_89, '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.05/1.71  tff(c_68, plain, (v1_funct_2('#skF_13', '#skF_11', '#skF_12')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.05/1.71  tff(c_122, plain, (![A_105, B_106, C_107]: (k1_relset_1(A_105, B_106, C_107)=k1_relat_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.05/1.71  tff(c_126, plain, (k1_relset_1('#skF_11', '#skF_12', '#skF_13')=k1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_66, c_122])).
% 4.05/1.71  tff(c_194, plain, (![B_132, A_133, C_134]: (k1_xboole_0=B_132 | k1_relset_1(A_133, B_132, C_134)=A_133 | ~v1_funct_2(C_134, A_133, B_132) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_133, B_132))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.05/1.71  tff(c_197, plain, (k1_xboole_0='#skF_12' | k1_relset_1('#skF_11', '#skF_12', '#skF_13')='#skF_11' | ~v1_funct_2('#skF_13', '#skF_11', '#skF_12')), inference(resolution, [status(thm)], [c_66, c_194])).
% 4.05/1.71  tff(c_200, plain, (k1_xboole_0='#skF_12' | k1_relat_1('#skF_13')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_126, c_197])).
% 4.05/1.71  tff(c_201, plain, (k1_relat_1('#skF_13')='#skF_11'), inference(splitLeft, [status(thm)], [c_200])).
% 4.05/1.71  tff(c_95, plain, (![C_95, A_96, B_97]: (v1_relat_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.05/1.71  tff(c_99, plain, (v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_66, c_95])).
% 4.05/1.71  tff(c_70, plain, (v1_funct_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.05/1.71  tff(c_72, plain, (![D_89]: (k1_funct_1('#skF_13', '#skF_14'(D_89))=D_89 | ~r2_hidden(D_89, '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.05/1.71  tff(c_147, plain, (![A_113, D_114]: (r2_hidden(k1_funct_1(A_113, D_114), k2_relat_1(A_113)) | ~r2_hidden(D_114, k1_relat_1(A_113)) | ~v1_funct_1(A_113) | ~v1_relat_1(A_113))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.05/1.71  tff(c_150, plain, (![D_89]: (r2_hidden(D_89, k2_relat_1('#skF_13')) | ~r2_hidden('#skF_14'(D_89), k1_relat_1('#skF_13')) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13') | ~r2_hidden(D_89, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_147])).
% 4.05/1.71  tff(c_155, plain, (![D_89]: (r2_hidden(D_89, k2_relat_1('#skF_13')) | ~r2_hidden('#skF_14'(D_89), k1_relat_1('#skF_13')) | ~r2_hidden(D_89, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_70, c_150])).
% 4.05/1.71  tff(c_218, plain, (![D_135]: (r2_hidden(D_135, k2_relat_1('#skF_13')) | ~r2_hidden('#skF_14'(D_135), '#skF_11') | ~r2_hidden(D_135, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_201, c_155])).
% 4.05/1.71  tff(c_222, plain, (![D_89]: (r2_hidden(D_89, k2_relat_1('#skF_13')) | ~r2_hidden(D_89, '#skF_12'))), inference(resolution, [status(thm)], [c_74, c_218])).
% 4.05/1.71  tff(c_2, plain, (![A_1, C_16]: (r2_hidden(k4_tarski('#skF_4'(A_1, k2_relat_1(A_1), C_16), C_16), A_1) | ~r2_hidden(C_16, k2_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.05/1.71  tff(c_456, plain, (![E_170, A_171, B_172, C_173]: (~r2_hidden(k4_tarski(E_170, '#skF_9'(A_171, B_172, C_173)), C_173) | k2_relset_1(A_171, B_172, C_173)=B_172 | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.05/1.71  tff(c_498, plain, (![A_176, B_177, A_178]: (k2_relset_1(A_176, B_177, A_178)=B_177 | ~m1_subset_1(A_178, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))) | ~r2_hidden('#skF_9'(A_176, B_177, A_178), k2_relat_1(A_178)))), inference(resolution, [status(thm)], [c_2, c_456])).
% 4.05/1.71  tff(c_532, plain, (![A_179, B_180]: (k2_relset_1(A_179, B_180, '#skF_13')=B_180 | ~m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))) | ~r2_hidden('#skF_9'(A_179, B_180, '#skF_13'), '#skF_12'))), inference(resolution, [status(thm)], [c_222, c_498])).
% 4.05/1.71  tff(c_535, plain, (k2_relset_1('#skF_11', '#skF_12', '#skF_13')='#skF_12' | ~r2_hidden('#skF_9'('#skF_11', '#skF_12', '#skF_13'), '#skF_12')), inference(resolution, [status(thm)], [c_66, c_532])).
% 4.05/1.71  tff(c_538, plain, (k2_relat_1('#skF_13')='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_193, c_115, c_535])).
% 4.05/1.71  tff(c_540, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116, c_538])).
% 4.05/1.71  tff(c_541, plain, (k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_200])).
% 4.05/1.71  tff(c_16, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.05/1.71  tff(c_562, plain, (k1_relat_1('#skF_12')='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_541, c_541, c_16])).
% 4.05/1.71  tff(c_18, plain, (![A_20]: (k1_relat_1(A_20)=k1_xboole_0 | k2_relat_1(A_20)!=k1_xboole_0 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.05/1.71  tff(c_106, plain, (k1_relat_1('#skF_13')=k1_xboole_0 | k2_relat_1('#skF_13')!=k1_xboole_0), inference(resolution, [status(thm)], [c_99, c_18])).
% 4.05/1.71  tff(c_108, plain, (k2_relat_1('#skF_13')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_106])).
% 4.05/1.71  tff(c_20, plain, (![A_20]: (k2_relat_1(A_20)=k1_xboole_0 | k1_relat_1(A_20)!=k1_xboole_0 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.05/1.71  tff(c_107, plain, (k2_relat_1('#skF_13')=k1_xboole_0 | k1_relat_1('#skF_13')!=k1_xboole_0), inference(resolution, [status(thm)], [c_99, c_20])).
% 4.05/1.71  tff(c_109, plain, (k1_relat_1('#skF_13')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_108, c_107])).
% 4.05/1.71  tff(c_557, plain, (k1_relat_1('#skF_13')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_541, c_109])).
% 4.05/1.71  tff(c_54, plain, (![C_85, A_83]: (k1_xboole_0=C_85 | ~v1_funct_2(C_85, A_83, k1_xboole_0) | k1_xboole_0=A_83 | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.05/1.71  tff(c_626, plain, (![C_195, A_196]: (C_195='#skF_12' | ~v1_funct_2(C_195, A_196, '#skF_12') | A_196='#skF_12' | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_196, '#skF_12'))))), inference(demodulation, [status(thm), theory('equality')], [c_541, c_541, c_541, c_541, c_54])).
% 4.05/1.71  tff(c_629, plain, ('#skF_13'='#skF_12' | ~v1_funct_2('#skF_13', '#skF_11', '#skF_12') | '#skF_11'='#skF_12'), inference(resolution, [status(thm)], [c_66, c_626])).
% 4.05/1.71  tff(c_632, plain, ('#skF_13'='#skF_12' | '#skF_11'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_629])).
% 4.05/1.71  tff(c_633, plain, ('#skF_11'='#skF_12'), inference(splitLeft, [status(thm)], [c_632])).
% 4.05/1.71  tff(c_640, plain, (v1_funct_2('#skF_13', '#skF_12', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_633, c_68])).
% 4.05/1.71  tff(c_636, plain, (k1_relset_1('#skF_12', '#skF_12', '#skF_13')=k1_relat_1('#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_633, c_126])).
% 4.05/1.71  tff(c_639, plain, (m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_12', '#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_633, c_66])).
% 4.05/1.71  tff(c_60, plain, (![B_84, C_85]: (k1_relset_1(k1_xboole_0, B_84, C_85)=k1_xboole_0 | ~v1_funct_2(C_85, k1_xboole_0, B_84) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_84))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.05/1.71  tff(c_685, plain, (![B_200, C_201]: (k1_relset_1('#skF_12', B_200, C_201)='#skF_12' | ~v1_funct_2(C_201, '#skF_12', B_200) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1('#skF_12', B_200))))), inference(demodulation, [status(thm), theory('equality')], [c_541, c_541, c_541, c_541, c_60])).
% 4.05/1.71  tff(c_688, plain, (k1_relset_1('#skF_12', '#skF_12', '#skF_13')='#skF_12' | ~v1_funct_2('#skF_13', '#skF_12', '#skF_12')), inference(resolution, [status(thm)], [c_639, c_685])).
% 4.05/1.71  tff(c_691, plain, (k1_relat_1('#skF_13')='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_640, c_636, c_688])).
% 4.05/1.71  tff(c_693, plain, $false, inference(negUnitSimplification, [status(thm)], [c_557, c_691])).
% 4.05/1.71  tff(c_694, plain, ('#skF_13'='#skF_12'), inference(splitRight, [status(thm)], [c_632])).
% 4.05/1.71  tff(c_696, plain, (k1_relat_1('#skF_12')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_694, c_557])).
% 4.05/1.71  tff(c_710, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_562, c_696])).
% 4.05/1.71  tff(c_712, plain, (k2_relat_1('#skF_13')=k1_xboole_0), inference(splitRight, [status(thm)], [c_106])).
% 4.05/1.71  tff(c_735, plain, (![A_209, B_210, C_211]: (k2_relset_1(A_209, B_210, C_211)=k2_relat_1(C_211) | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(A_209, B_210))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.05/1.71  tff(c_738, plain, (k2_relset_1('#skF_11', '#skF_12', '#skF_13')=k2_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_66, c_735])).
% 4.05/1.71  tff(c_740, plain, (k2_relset_1('#skF_11', '#skF_12', '#skF_13')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_712, c_738])).
% 4.05/1.71  tff(c_741, plain, (k1_xboole_0!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_740, c_64])).
% 4.05/1.71  tff(c_711, plain, (k1_relat_1('#skF_13')=k1_xboole_0), inference(splitRight, [status(thm)], [c_106])).
% 4.05/1.71  tff(c_724, plain, (![A_205, B_206, C_207]: (k1_relset_1(A_205, B_206, C_207)=k1_relat_1(C_207) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_205, B_206))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.05/1.71  tff(c_727, plain, (k1_relset_1('#skF_11', '#skF_12', '#skF_13')=k1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_66, c_724])).
% 4.05/1.71  tff(c_729, plain, (k1_relset_1('#skF_11', '#skF_12', '#skF_13')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_711, c_727])).
% 4.05/1.71  tff(c_886, plain, (![B_248, A_249, C_250]: (k1_xboole_0=B_248 | k1_relset_1(A_249, B_248, C_250)=A_249 | ~v1_funct_2(C_250, A_249, B_248) | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(A_249, B_248))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.05/1.71  tff(c_889, plain, (k1_xboole_0='#skF_12' | k1_relset_1('#skF_11', '#skF_12', '#skF_13')='#skF_11' | ~v1_funct_2('#skF_13', '#skF_11', '#skF_12')), inference(resolution, [status(thm)], [c_66, c_886])).
% 4.05/1.71  tff(c_892, plain, (k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_729, c_889])).
% 4.05/1.71  tff(c_893, plain, (k1_xboole_0='#skF_11'), inference(negUnitSimplification, [status(thm)], [c_741, c_892])).
% 4.05/1.71  tff(c_908, plain, ('#skF_11'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_893, c_741])).
% 4.05/1.71  tff(c_945, plain, (![A_251, B_252, C_253]: (r2_hidden('#skF_9'(A_251, B_252, C_253), B_252) | k2_relset_1(A_251, B_252, C_253)=B_252 | ~m1_subset_1(C_253, k1_zfmisc_1(k2_zfmisc_1(A_251, B_252))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.05/1.71  tff(c_948, plain, (r2_hidden('#skF_9'('#skF_11', '#skF_12', '#skF_13'), '#skF_12') | k2_relset_1('#skF_11', '#skF_12', '#skF_13')='#skF_12'), inference(resolution, [status(thm)], [c_66, c_945])).
% 4.05/1.71  tff(c_993, plain, (k2_relset_1('#skF_11', '#skF_12', '#skF_13')='#skF_12'), inference(splitLeft, [status(thm)], [c_948])).
% 4.05/1.71  tff(c_909, plain, (k2_relset_1('#skF_11', '#skF_12', '#skF_13')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_893, c_740])).
% 4.05/1.71  tff(c_1002, plain, ('#skF_11'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_993, c_909])).
% 4.05/1.71  tff(c_1003, plain, $false, inference(negUnitSimplification, [status(thm)], [c_908, c_1002])).
% 4.05/1.71  tff(c_1004, plain, (r2_hidden('#skF_9'('#skF_11', '#skF_12', '#skF_13'), '#skF_12')), inference(splitRight, [status(thm)], [c_948])).
% 4.05/1.71  tff(c_772, plain, (![A_218, D_219]: (r2_hidden(k1_funct_1(A_218, D_219), k2_relat_1(A_218)) | ~r2_hidden(D_219, k1_relat_1(A_218)) | ~v1_funct_1(A_218) | ~v1_relat_1(A_218))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.05/1.71  tff(c_778, plain, (![D_89]: (r2_hidden(D_89, k2_relat_1('#skF_13')) | ~r2_hidden('#skF_14'(D_89), k1_relat_1('#skF_13')) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13') | ~r2_hidden(D_89, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_772])).
% 4.05/1.71  tff(c_785, plain, (![D_89]: (r2_hidden(D_89, k1_xboole_0) | ~r2_hidden('#skF_14'(D_89), k1_xboole_0) | ~r2_hidden(D_89, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_70, c_711, c_712, c_778])).
% 4.05/1.71  tff(c_1032, plain, (![D_257]: (r2_hidden(D_257, '#skF_11') | ~r2_hidden('#skF_14'(D_257), '#skF_11') | ~r2_hidden(D_257, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_893, c_893, c_785])).
% 4.05/1.71  tff(c_1036, plain, (![D_89]: (r2_hidden(D_89, '#skF_11') | ~r2_hidden(D_89, '#skF_12'))), inference(resolution, [status(thm)], [c_74, c_1032])).
% 4.05/1.71  tff(c_912, plain, (k2_relat_1('#skF_13')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_893, c_712])).
% 4.05/1.71  tff(c_981, plain, (![C_16]: (r2_hidden(k4_tarski('#skF_4'('#skF_13', '#skF_11', C_16), C_16), '#skF_13') | ~r2_hidden(C_16, k2_relat_1('#skF_13')))), inference(superposition, [status(thm), theory('equality')], [c_912, c_2])).
% 4.05/1.71  tff(c_991, plain, (![C_16]: (r2_hidden(k4_tarski('#skF_4'('#skF_13', '#skF_11', C_16), C_16), '#skF_13') | ~r2_hidden(C_16, '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_912, c_981])).
% 4.05/1.71  tff(c_1188, plain, (![E_273, A_274, B_275, C_276]: (~r2_hidden(k4_tarski(E_273, '#skF_9'(A_274, B_275, C_276)), C_276) | k2_relset_1(A_274, B_275, C_276)=B_275 | ~m1_subset_1(C_276, k1_zfmisc_1(k2_zfmisc_1(A_274, B_275))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.05/1.71  tff(c_1615, plain, (![A_327, B_328]: (k2_relset_1(A_327, B_328, '#skF_13')=B_328 | ~m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1(A_327, B_328))) | ~r2_hidden('#skF_9'(A_327, B_328, '#skF_13'), '#skF_11'))), inference(resolution, [status(thm)], [c_991, c_1188])).
% 4.05/1.71  tff(c_1618, plain, (k2_relset_1('#skF_11', '#skF_12', '#skF_13')='#skF_12' | ~r2_hidden('#skF_9'('#skF_11', '#skF_12', '#skF_13'), '#skF_11')), inference(resolution, [status(thm)], [c_66, c_1615])).
% 4.05/1.71  tff(c_1620, plain, ('#skF_11'='#skF_12' | ~r2_hidden('#skF_9'('#skF_11', '#skF_12', '#skF_13'), '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_909, c_1618])).
% 4.05/1.71  tff(c_1621, plain, (~r2_hidden('#skF_9'('#skF_11', '#skF_12', '#skF_13'), '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_908, c_1620])).
% 4.05/1.71  tff(c_1624, plain, (~r2_hidden('#skF_9'('#skF_11', '#skF_12', '#skF_13'), '#skF_12')), inference(resolution, [status(thm)], [c_1036, c_1621])).
% 4.05/1.71  tff(c_1628, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1004, c_1624])).
% 4.05/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.05/1.71  
% 4.05/1.71  Inference rules
% 4.05/1.71  ----------------------
% 4.05/1.71  #Ref     : 1
% 4.05/1.71  #Sup     : 307
% 4.05/1.71  #Fact    : 0
% 4.05/1.71  #Define  : 0
% 4.05/1.71  #Split   : 11
% 4.05/1.71  #Chain   : 0
% 4.05/1.71  #Close   : 0
% 4.05/1.71  
% 4.05/1.71  Ordering : KBO
% 4.05/1.71  
% 4.05/1.71  Simplification rules
% 4.05/1.71  ----------------------
% 4.05/1.71  #Subsume      : 51
% 4.05/1.71  #Demod        : 310
% 4.05/1.71  #Tautology    : 117
% 4.05/1.71  #SimpNegUnit  : 20
% 4.05/1.71  #BackRed      : 64
% 4.05/1.71  
% 4.05/1.71  #Partial instantiations: 0
% 4.05/1.71  #Strategies tried      : 1
% 4.05/1.71  
% 4.05/1.71  Timing (in seconds)
% 4.05/1.71  ----------------------
% 4.05/1.71  Preprocessing        : 0.34
% 4.05/1.71  Parsing              : 0.17
% 4.05/1.71  CNF conversion       : 0.03
% 4.05/1.71  Main loop            : 0.56
% 4.05/1.71  Inferencing          : 0.21
% 4.05/1.71  Reduction            : 0.16
% 4.05/1.71  Demodulation         : 0.10
% 4.05/1.71  BG Simplification    : 0.03
% 4.05/1.71  Subsumption          : 0.11
% 4.05/1.71  Abstraction          : 0.03
% 4.05/1.71  MUC search           : 0.00
% 4.05/1.71  Cooper               : 0.00
% 4.05/1.71  Total                : 0.94
% 4.05/1.71  Index Insertion      : 0.00
% 4.05/1.71  Index Deletion       : 0.00
% 4.05/1.71  Index Matching       : 0.00
% 4.05/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
