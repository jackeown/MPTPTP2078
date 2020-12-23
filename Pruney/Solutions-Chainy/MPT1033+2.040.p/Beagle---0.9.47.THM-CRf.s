%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:56 EST 2020

% Result     : Theorem 4.40s
% Output     : CNFRefutation 4.52s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 572 expanded)
%              Number of leaves         :   32 ( 190 expanded)
%              Depth                    :   12
%              Number of atoms          :  252 (1858 expanded)
%              Number of equality atoms :   30 ( 426 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_relset_1(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ~ ( r2_hidden(A,D)
          & ! [E,F] :
              ~ ( A = k4_tarski(E,F)
                & r2_hidden(E,B)
                & r2_hidden(F,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( v1_partfun1(C,A)
              & v1_partfun1(D,A)
              & r1_partfun1(C,D) )
           => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

tff(f_74,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(c_32,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_47,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_36,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_239,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( r2_relset_1(A_95,B_96,C_97,C_97)
      | ~ m1_subset_1(D_98,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96)))
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_249,plain,(
    ! [C_99] :
      ( r2_relset_1('#skF_5','#skF_6',C_99,C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_36,c_239])).

tff(c_257,plain,(
    r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_249])).

tff(c_105,plain,(
    ! [A_62,B_63,C_64,D_65] :
      ( r2_hidden('#skF_3'(A_62,B_63,C_64,D_65),C_64)
      | ~ r2_hidden(A_62,D_65)
      | ~ m1_subset_1(D_65,k1_zfmisc_1(k2_zfmisc_1(B_63,C_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_117,plain,(
    ! [A_68] :
      ( r2_hidden('#skF_3'(A_68,'#skF_5','#skF_6','#skF_8'),'#skF_6')
      | ~ r2_hidden(A_68,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_36,c_105])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_131,plain,(
    ! [A_68] :
      ( ~ v1_xboole_0('#skF_6')
      | ~ r2_hidden(A_68,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_117,c_2])).

tff(c_132,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_46,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_44,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_42,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_213,plain,(
    ! [C_84,A_85,B_86] :
      ( v1_partfun1(C_84,A_85)
      | ~ v1_funct_2(C_84,A_85,B_86)
      | ~ v1_funct_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86)))
      | v1_xboole_0(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_219,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_213])).

tff(c_230,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_219])).

tff(c_231,plain,(
    v1_partfun1('#skF_7','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_230])).

tff(c_40,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_38,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_216,plain,
    ( v1_partfun1('#skF_8','#skF_5')
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_8')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_213])).

tff(c_226,plain,
    ( v1_partfun1('#skF_8','#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_216])).

tff(c_227,plain,(
    v1_partfun1('#skF_8','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_226])).

tff(c_34,plain,(
    r1_partfun1('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_340,plain,(
    ! [D_115,C_116,A_117,B_118] :
      ( D_115 = C_116
      | ~ r1_partfun1(C_116,D_115)
      | ~ v1_partfun1(D_115,A_117)
      | ~ v1_partfun1(C_116,A_117)
      | ~ m1_subset_1(D_115,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118)))
      | ~ v1_funct_1(D_115)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118)))
      | ~ v1_funct_1(C_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_342,plain,(
    ! [A_117,B_118] :
      ( '#skF_7' = '#skF_8'
      | ~ v1_partfun1('#skF_8',A_117)
      | ~ v1_partfun1('#skF_7',A_117)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(A_117,B_118)))
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_117,B_118)))
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_34,c_340])).

tff(c_345,plain,(
    ! [A_117,B_118] :
      ( '#skF_7' = '#skF_8'
      | ~ v1_partfun1('#skF_8',A_117)
      | ~ v1_partfun1('#skF_7',A_117)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(A_117,B_118)))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_342])).

tff(c_447,plain,(
    ! [A_124,B_125] :
      ( ~ v1_partfun1('#skF_8',A_124)
      | ~ v1_partfun1('#skF_7',A_124)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(A_124,B_125)))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(splitLeft,[status(thm)],[c_345])).

tff(c_450,plain,
    ( ~ v1_partfun1('#skF_8','#skF_5')
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_42,c_447])).

tff(c_454,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_231,c_227,c_450])).

tff(c_455,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_345])).

tff(c_30,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_467,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_30])).

tff(c_476,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_467])).

tff(c_478,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_50,plain,(
    ! [A_42] :
      ( r2_hidden('#skF_4'(A_42),A_42)
      | k1_xboole_0 = A_42 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_54,plain,(
    ! [A_42] :
      ( ~ v1_xboole_0(A_42)
      | k1_xboole_0 = A_42 ) ),
    inference(resolution,[status(thm)],[c_50,c_2])).

tff(c_481,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_478,c_54])).

tff(c_485,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_481])).

tff(c_487,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_486,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_492,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_486])).

tff(c_520,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_36])).

tff(c_1985,plain,(
    ! [A_367,B_368,C_369,D_370] :
      ( r2_relset_1(A_367,B_368,C_369,C_369)
      | ~ m1_subset_1(D_370,k1_zfmisc_1(k2_zfmisc_1(A_367,B_368)))
      | ~ m1_subset_1(C_369,k1_zfmisc_1(k2_zfmisc_1(A_367,B_368))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2078,plain,(
    ! [C_377] :
      ( r2_relset_1('#skF_6','#skF_6',C_377,C_377)
      | ~ m1_subset_1(C_377,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_520,c_1985])).

tff(c_2114,plain,(
    r2_relset_1('#skF_6','#skF_6','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_520,c_2078])).

tff(c_498,plain,(
    v1_funct_2('#skF_7','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_44])).

tff(c_514,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_42])).

tff(c_18,plain,(
    ! [A_19] :
      ( r2_hidden('#skF_4'(A_19),A_19)
      | k1_xboole_0 = A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_507,plain,(
    ! [A_19] :
      ( r2_hidden('#skF_4'(A_19),A_19)
      | A_19 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_18])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_503,plain,(
    ! [A_5] : m1_subset_1('#skF_6',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_6])).

tff(c_530,plain,(
    ! [A_137,C_138,B_139] :
      ( m1_subset_1(A_137,C_138)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(C_138))
      | ~ r2_hidden(A_137,B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_548,plain,(
    ! [A_143,A_144] :
      ( m1_subset_1(A_143,A_144)
      | ~ r2_hidden(A_143,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_503,c_530])).

tff(c_555,plain,(
    ! [A_144] :
      ( m1_subset_1('#skF_1'('#skF_6'),A_144)
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_4,c_548])).

tff(c_558,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_555])).

tff(c_569,plain,(
    ! [A_153,B_154,C_155,D_156] :
      ( r2_hidden('#skF_3'(A_153,B_154,C_155,D_156),C_155)
      | ~ r2_hidden(A_153,D_156)
      | ~ m1_subset_1(D_156,k1_zfmisc_1(k2_zfmisc_1(B_154,C_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_591,plain,(
    ! [A_161] :
      ( r2_hidden('#skF_3'(A_161,'#skF_6','#skF_6','#skF_8'),'#skF_6')
      | ~ r2_hidden(A_161,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_520,c_569])).

tff(c_600,plain,(
    ! [A_161] :
      ( ~ v1_xboole_0('#skF_6')
      | ~ r2_hidden(A_161,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_591,c_2])).

tff(c_609,plain,(
    ! [A_162] : ~ r2_hidden(A_162,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_600])).

tff(c_619,plain,(
    '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_507,c_609])).

tff(c_659,plain,(
    ! [A_5] : m1_subset_1('#skF_8',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_619,c_503])).

tff(c_725,plain,(
    ! [A_170,B_171,C_172,D_173] :
      ( r2_relset_1(A_170,B_171,C_172,C_172)
      | ~ m1_subset_1(D_173,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171)))
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_787,plain,(
    ! [A_199,B_200,C_201] :
      ( r2_relset_1(A_199,B_200,C_201,C_201)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(A_199,B_200))) ) ),
    inference(resolution,[status(thm)],[c_659,c_725])).

tff(c_791,plain,(
    ! [A_199,B_200] : r2_relset_1(A_199,B_200,'#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_659,c_787])).

tff(c_580,plain,(
    ! [A_157,B_158,C_159,D_160] :
      ( r2_hidden('#skF_2'(A_157,B_158,C_159,D_160),B_158)
      | ~ r2_hidden(A_157,D_160)
      | ~ m1_subset_1(D_160,k1_zfmisc_1(k2_zfmisc_1(B_158,C_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_624,plain,(
    ! [A_163] :
      ( r2_hidden('#skF_2'(A_163,'#skF_6','#skF_6','#skF_7'),'#skF_6')
      | ~ r2_hidden(A_163,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_514,c_580])).

tff(c_633,plain,(
    ! [A_163] :
      ( ~ v1_xboole_0('#skF_6')
      | ~ r2_hidden(A_163,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_624,c_2])).

tff(c_677,plain,(
    ! [A_164] : ~ r2_hidden(A_164,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_633])).

tff(c_682,plain,(
    v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_4,c_677])).

tff(c_508,plain,(
    ! [A_129] :
      ( r2_hidden('#skF_4'(A_129),A_129)
      | A_129 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_18])).

tff(c_512,plain,(
    ! [A_129] :
      ( ~ v1_xboole_0(A_129)
      | A_129 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_508,c_2])).

tff(c_703,plain,(
    ! [A_169] :
      ( ~ v1_xboole_0(A_169)
      | A_169 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_619,c_512])).

tff(c_710,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_682,c_703])).

tff(c_506,plain,(
    ~ r2_relset_1('#skF_6','#skF_6','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_30])).

tff(c_656,plain,(
    ~ r2_relset_1('#skF_8','#skF_8','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_619,c_619,c_506])).

tff(c_724,plain,(
    ~ r2_relset_1('#skF_8','#skF_8','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_710,c_656])).

tff(c_794,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_791,c_724])).

tff(c_796,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_555])).

tff(c_814,plain,(
    ! [A_209,B_210,C_211,D_212] :
      ( r2_hidden('#skF_3'(A_209,B_210,C_211,D_212),C_211)
      | ~ r2_hidden(A_209,D_212)
      | ~ m1_subset_1(D_212,k1_zfmisc_1(k2_zfmisc_1(B_210,C_211))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1761,plain,(
    ! [A_343,B_344,C_345] :
      ( r2_hidden('#skF_3'(A_343,B_344,C_345,'#skF_6'),C_345)
      | ~ r2_hidden(A_343,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_503,c_814])).

tff(c_1787,plain,(
    ! [C_345,A_343] :
      ( ~ v1_xboole_0(C_345)
      | ~ r2_hidden(A_343,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1761,c_2])).

tff(c_1814,plain,(
    ! [A_350] : ~ r2_hidden(A_350,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1787])).

tff(c_1818,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_1814])).

tff(c_1826,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_796,c_1818])).

tff(c_1827,plain,(
    ! [C_345] : ~ v1_xboole_0(C_345) ),
    inference(splitRight,[status(thm)],[c_1787])).

tff(c_24,plain,(
    ! [C_32,A_29,B_30] :
      ( v1_partfun1(C_32,A_29)
      | ~ v1_funct_2(C_32,A_29,B_30)
      | ~ v1_funct_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | v1_xboole_0(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1897,plain,(
    ! [C_358,A_359,B_360] :
      ( v1_partfun1(C_358,A_359)
      | ~ v1_funct_2(C_358,A_359,B_360)
      | ~ v1_funct_1(C_358)
      | ~ m1_subset_1(C_358,k1_zfmisc_1(k2_zfmisc_1(A_359,B_360))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1827,c_24])).

tff(c_1923,plain,
    ( v1_partfun1('#skF_7','#skF_6')
    | ~ v1_funct_2('#skF_7','#skF_6','#skF_6')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_514,c_1897])).

tff(c_1938,plain,(
    v1_partfun1('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_498,c_1923])).

tff(c_497,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_38])).

tff(c_1920,plain,
    ( v1_partfun1('#skF_8','#skF_6')
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_6')
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_520,c_1897])).

tff(c_1935,plain,(
    v1_partfun1('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_497,c_1920])).

tff(c_2332,plain,(
    ! [D_396,C_397,A_398,B_399] :
      ( D_396 = C_397
      | ~ r1_partfun1(C_397,D_396)
      | ~ v1_partfun1(D_396,A_398)
      | ~ v1_partfun1(C_397,A_398)
      | ~ m1_subset_1(D_396,k1_zfmisc_1(k2_zfmisc_1(A_398,B_399)))
      | ~ v1_funct_1(D_396)
      | ~ m1_subset_1(C_397,k1_zfmisc_1(k2_zfmisc_1(A_398,B_399)))
      | ~ v1_funct_1(C_397) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2334,plain,(
    ! [A_398,B_399] :
      ( '#skF_7' = '#skF_8'
      | ~ v1_partfun1('#skF_8',A_398)
      | ~ v1_partfun1('#skF_7',A_398)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(A_398,B_399)))
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_398,B_399)))
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_34,c_2332])).

tff(c_2337,plain,(
    ! [A_398,B_399] :
      ( '#skF_7' = '#skF_8'
      | ~ v1_partfun1('#skF_8',A_398)
      | ~ v1_partfun1('#skF_7',A_398)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(A_398,B_399)))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_398,B_399))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_2334])).

tff(c_2587,plain,(
    ! [A_423,B_424] :
      ( ~ v1_partfun1('#skF_8',A_423)
      | ~ v1_partfun1('#skF_7',A_423)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(A_423,B_424)))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_423,B_424))) ) ),
    inference(splitLeft,[status(thm)],[c_2337])).

tff(c_2590,plain,
    ( ~ v1_partfun1('#skF_8','#skF_6')
    | ~ v1_partfun1('#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_514,c_2587])).

tff(c_2594,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_520,c_1938,c_1935,c_2590])).

tff(c_2595,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_2337])).

tff(c_2605,plain,(
    ~ r2_relset_1('#skF_6','#skF_6','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2595,c_506])).

tff(c_2614,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2114,c_2605])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:50:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.40/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.49/1.82  
% 4.49/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.52/1.82  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3
% 4.52/1.82  
% 4.52/1.82  %Foreground sorts:
% 4.52/1.82  
% 4.52/1.82  
% 4.52/1.82  %Background operators:
% 4.52/1.82  
% 4.52/1.82  
% 4.52/1.82  %Foreground operators:
% 4.52/1.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.52/1.82  tff('#skF_4', type, '#skF_4': $i > $i).
% 4.52/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.52/1.82  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.52/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.52/1.82  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.52/1.82  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.52/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.52/1.82  tff('#skF_7', type, '#skF_7': $i).
% 4.52/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.52/1.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.52/1.82  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.52/1.82  tff('#skF_6', type, '#skF_6': $i).
% 4.52/1.82  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.52/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.52/1.82  tff('#skF_8', type, '#skF_8': $i).
% 4.52/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.52/1.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.52/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.52/1.82  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.52/1.82  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.52/1.82  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 4.52/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.52/1.82  
% 4.52/1.84  tff(f_128, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_2)).
% 4.52/1.84  tff(f_45, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 4.52/1.84  tff(f_58, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => ~(r2_hidden(A, D) & (![E, F]: ~(((A = k4_tarski(E, F)) & r2_hidden(E, B)) & r2_hidden(F, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_relset_1)).
% 4.52/1.84  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.52/1.84  tff(f_88, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 4.52/1.84  tff(f_105, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 4.52/1.84  tff(f_74, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 4.52/1.84  tff(f_33, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.52/1.84  tff(f_39, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.52/1.84  tff(c_32, plain, (k1_xboole_0='#skF_5' | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.52/1.84  tff(c_47, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_32])).
% 4.52/1.84  tff(c_36, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.52/1.84  tff(c_239, plain, (![A_95, B_96, C_97, D_98]: (r2_relset_1(A_95, B_96, C_97, C_97) | ~m1_subset_1(D_98, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.52/1.84  tff(c_249, plain, (![C_99]: (r2_relset_1('#skF_5', '#skF_6', C_99, C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(resolution, [status(thm)], [c_36, c_239])).
% 4.52/1.84  tff(c_257, plain, (r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_36, c_249])).
% 4.52/1.84  tff(c_105, plain, (![A_62, B_63, C_64, D_65]: (r2_hidden('#skF_3'(A_62, B_63, C_64, D_65), C_64) | ~r2_hidden(A_62, D_65) | ~m1_subset_1(D_65, k1_zfmisc_1(k2_zfmisc_1(B_63, C_64))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.52/1.84  tff(c_117, plain, (![A_68]: (r2_hidden('#skF_3'(A_68, '#skF_5', '#skF_6', '#skF_8'), '#skF_6') | ~r2_hidden(A_68, '#skF_8'))), inference(resolution, [status(thm)], [c_36, c_105])).
% 4.52/1.84  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.52/1.84  tff(c_131, plain, (![A_68]: (~v1_xboole_0('#skF_6') | ~r2_hidden(A_68, '#skF_8'))), inference(resolution, [status(thm)], [c_117, c_2])).
% 4.52/1.84  tff(c_132, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_131])).
% 4.52/1.84  tff(c_46, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.52/1.84  tff(c_44, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.52/1.84  tff(c_42, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.52/1.84  tff(c_213, plain, (![C_84, A_85, B_86]: (v1_partfun1(C_84, A_85) | ~v1_funct_2(C_84, A_85, B_86) | ~v1_funct_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))) | v1_xboole_0(B_86))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.52/1.84  tff(c_219, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_42, c_213])).
% 4.52/1.84  tff(c_230, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_219])).
% 4.52/1.84  tff(c_231, plain, (v1_partfun1('#skF_7', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_132, c_230])).
% 4.52/1.84  tff(c_40, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.52/1.84  tff(c_38, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.52/1.84  tff(c_216, plain, (v1_partfun1('#skF_8', '#skF_5') | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6') | ~v1_funct_1('#skF_8') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_36, c_213])).
% 4.52/1.84  tff(c_226, plain, (v1_partfun1('#skF_8', '#skF_5') | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_216])).
% 4.52/1.84  tff(c_227, plain, (v1_partfun1('#skF_8', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_132, c_226])).
% 4.52/1.84  tff(c_34, plain, (r1_partfun1('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.52/1.84  tff(c_340, plain, (![D_115, C_116, A_117, B_118]: (D_115=C_116 | ~r1_partfun1(C_116, D_115) | ~v1_partfun1(D_115, A_117) | ~v1_partfun1(C_116, A_117) | ~m1_subset_1(D_115, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))) | ~v1_funct_1(D_115) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))) | ~v1_funct_1(C_116))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.52/1.84  tff(c_342, plain, (![A_117, B_118]: ('#skF_7'='#skF_8' | ~v1_partfun1('#skF_8', A_117) | ~v1_partfun1('#skF_7', A_117) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))) | ~v1_funct_1('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_34, c_340])).
% 4.52/1.84  tff(c_345, plain, (![A_117, B_118]: ('#skF_7'='#skF_8' | ~v1_partfun1('#skF_8', A_117) | ~v1_partfun1('#skF_7', A_117) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_342])).
% 4.52/1.84  tff(c_447, plain, (![A_124, B_125]: (~v1_partfun1('#skF_8', A_124) | ~v1_partfun1('#skF_7', A_124) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(splitLeft, [status(thm)], [c_345])).
% 4.52/1.84  tff(c_450, plain, (~v1_partfun1('#skF_8', '#skF_5') | ~v1_partfun1('#skF_7', '#skF_5') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_42, c_447])).
% 4.52/1.84  tff(c_454, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_231, c_227, c_450])).
% 4.52/1.84  tff(c_455, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_345])).
% 4.52/1.84  tff(c_30, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.52/1.84  tff(c_467, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_455, c_30])).
% 4.52/1.84  tff(c_476, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_257, c_467])).
% 4.52/1.84  tff(c_478, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_131])).
% 4.52/1.84  tff(c_50, plain, (![A_42]: (r2_hidden('#skF_4'(A_42), A_42) | k1_xboole_0=A_42)), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.52/1.84  tff(c_54, plain, (![A_42]: (~v1_xboole_0(A_42) | k1_xboole_0=A_42)), inference(resolution, [status(thm)], [c_50, c_2])).
% 4.52/1.84  tff(c_481, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_478, c_54])).
% 4.52/1.84  tff(c_485, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_481])).
% 4.52/1.84  tff(c_487, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_32])).
% 4.52/1.84  tff(c_486, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_32])).
% 4.52/1.84  tff(c_492, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_487, c_486])).
% 4.52/1.84  tff(c_520, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_492, c_36])).
% 4.52/1.84  tff(c_1985, plain, (![A_367, B_368, C_369, D_370]: (r2_relset_1(A_367, B_368, C_369, C_369) | ~m1_subset_1(D_370, k1_zfmisc_1(k2_zfmisc_1(A_367, B_368))) | ~m1_subset_1(C_369, k1_zfmisc_1(k2_zfmisc_1(A_367, B_368))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.52/1.84  tff(c_2078, plain, (![C_377]: (r2_relset_1('#skF_6', '#skF_6', C_377, C_377) | ~m1_subset_1(C_377, k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6'))))), inference(resolution, [status(thm)], [c_520, c_1985])).
% 4.52/1.84  tff(c_2114, plain, (r2_relset_1('#skF_6', '#skF_6', '#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_520, c_2078])).
% 4.52/1.84  tff(c_498, plain, (v1_funct_2('#skF_7', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_492, c_44])).
% 4.52/1.84  tff(c_514, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_492, c_42])).
% 4.52/1.84  tff(c_18, plain, (![A_19]: (r2_hidden('#skF_4'(A_19), A_19) | k1_xboole_0=A_19)), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.52/1.84  tff(c_507, plain, (![A_19]: (r2_hidden('#skF_4'(A_19), A_19) | A_19='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_487, c_18])).
% 4.52/1.84  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.52/1.84  tff(c_6, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.52/1.84  tff(c_503, plain, (![A_5]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_487, c_6])).
% 4.52/1.84  tff(c_530, plain, (![A_137, C_138, B_139]: (m1_subset_1(A_137, C_138) | ~m1_subset_1(B_139, k1_zfmisc_1(C_138)) | ~r2_hidden(A_137, B_139))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.52/1.84  tff(c_548, plain, (![A_143, A_144]: (m1_subset_1(A_143, A_144) | ~r2_hidden(A_143, '#skF_6'))), inference(resolution, [status(thm)], [c_503, c_530])).
% 4.52/1.84  tff(c_555, plain, (![A_144]: (m1_subset_1('#skF_1'('#skF_6'), A_144) | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_4, c_548])).
% 4.52/1.84  tff(c_558, plain, (v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_555])).
% 4.52/1.84  tff(c_569, plain, (![A_153, B_154, C_155, D_156]: (r2_hidden('#skF_3'(A_153, B_154, C_155, D_156), C_155) | ~r2_hidden(A_153, D_156) | ~m1_subset_1(D_156, k1_zfmisc_1(k2_zfmisc_1(B_154, C_155))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.52/1.84  tff(c_591, plain, (![A_161]: (r2_hidden('#skF_3'(A_161, '#skF_6', '#skF_6', '#skF_8'), '#skF_6') | ~r2_hidden(A_161, '#skF_8'))), inference(resolution, [status(thm)], [c_520, c_569])).
% 4.52/1.84  tff(c_600, plain, (![A_161]: (~v1_xboole_0('#skF_6') | ~r2_hidden(A_161, '#skF_8'))), inference(resolution, [status(thm)], [c_591, c_2])).
% 4.52/1.84  tff(c_609, plain, (![A_162]: (~r2_hidden(A_162, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_558, c_600])).
% 4.52/1.84  tff(c_619, plain, ('#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_507, c_609])).
% 4.52/1.84  tff(c_659, plain, (![A_5]: (m1_subset_1('#skF_8', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_619, c_503])).
% 4.52/1.84  tff(c_725, plain, (![A_170, B_171, C_172, D_173]: (r2_relset_1(A_170, B_171, C_172, C_172) | ~m1_subset_1(D_173, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.52/1.84  tff(c_787, plain, (![A_199, B_200, C_201]: (r2_relset_1(A_199, B_200, C_201, C_201) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(A_199, B_200))))), inference(resolution, [status(thm)], [c_659, c_725])).
% 4.52/1.84  tff(c_791, plain, (![A_199, B_200]: (r2_relset_1(A_199, B_200, '#skF_8', '#skF_8'))), inference(resolution, [status(thm)], [c_659, c_787])).
% 4.52/1.84  tff(c_580, plain, (![A_157, B_158, C_159, D_160]: (r2_hidden('#skF_2'(A_157, B_158, C_159, D_160), B_158) | ~r2_hidden(A_157, D_160) | ~m1_subset_1(D_160, k1_zfmisc_1(k2_zfmisc_1(B_158, C_159))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.52/1.84  tff(c_624, plain, (![A_163]: (r2_hidden('#skF_2'(A_163, '#skF_6', '#skF_6', '#skF_7'), '#skF_6') | ~r2_hidden(A_163, '#skF_7'))), inference(resolution, [status(thm)], [c_514, c_580])).
% 4.52/1.84  tff(c_633, plain, (![A_163]: (~v1_xboole_0('#skF_6') | ~r2_hidden(A_163, '#skF_7'))), inference(resolution, [status(thm)], [c_624, c_2])).
% 4.52/1.84  tff(c_677, plain, (![A_164]: (~r2_hidden(A_164, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_558, c_633])).
% 4.52/1.84  tff(c_682, plain, (v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_4, c_677])).
% 4.52/1.84  tff(c_508, plain, (![A_129]: (r2_hidden('#skF_4'(A_129), A_129) | A_129='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_487, c_18])).
% 4.52/1.84  tff(c_512, plain, (![A_129]: (~v1_xboole_0(A_129) | A_129='#skF_6')), inference(resolution, [status(thm)], [c_508, c_2])).
% 4.52/1.84  tff(c_703, plain, (![A_169]: (~v1_xboole_0(A_169) | A_169='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_619, c_512])).
% 4.52/1.84  tff(c_710, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_682, c_703])).
% 4.52/1.84  tff(c_506, plain, (~r2_relset_1('#skF_6', '#skF_6', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_492, c_30])).
% 4.52/1.84  tff(c_656, plain, (~r2_relset_1('#skF_8', '#skF_8', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_619, c_619, c_506])).
% 4.52/1.84  tff(c_724, plain, (~r2_relset_1('#skF_8', '#skF_8', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_710, c_656])).
% 4.52/1.84  tff(c_794, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_791, c_724])).
% 4.52/1.84  tff(c_796, plain, (~v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_555])).
% 4.52/1.84  tff(c_814, plain, (![A_209, B_210, C_211, D_212]: (r2_hidden('#skF_3'(A_209, B_210, C_211, D_212), C_211) | ~r2_hidden(A_209, D_212) | ~m1_subset_1(D_212, k1_zfmisc_1(k2_zfmisc_1(B_210, C_211))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.52/1.84  tff(c_1761, plain, (![A_343, B_344, C_345]: (r2_hidden('#skF_3'(A_343, B_344, C_345, '#skF_6'), C_345) | ~r2_hidden(A_343, '#skF_6'))), inference(resolution, [status(thm)], [c_503, c_814])).
% 4.52/1.84  tff(c_1787, plain, (![C_345, A_343]: (~v1_xboole_0(C_345) | ~r2_hidden(A_343, '#skF_6'))), inference(resolution, [status(thm)], [c_1761, c_2])).
% 4.52/1.84  tff(c_1814, plain, (![A_350]: (~r2_hidden(A_350, '#skF_6'))), inference(splitLeft, [status(thm)], [c_1787])).
% 4.52/1.84  tff(c_1818, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_4, c_1814])).
% 4.52/1.84  tff(c_1826, plain, $false, inference(negUnitSimplification, [status(thm)], [c_796, c_1818])).
% 4.52/1.84  tff(c_1827, plain, (![C_345]: (~v1_xboole_0(C_345))), inference(splitRight, [status(thm)], [c_1787])).
% 4.52/1.84  tff(c_24, plain, (![C_32, A_29, B_30]: (v1_partfun1(C_32, A_29) | ~v1_funct_2(C_32, A_29, B_30) | ~v1_funct_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | v1_xboole_0(B_30))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.52/1.84  tff(c_1897, plain, (![C_358, A_359, B_360]: (v1_partfun1(C_358, A_359) | ~v1_funct_2(C_358, A_359, B_360) | ~v1_funct_1(C_358) | ~m1_subset_1(C_358, k1_zfmisc_1(k2_zfmisc_1(A_359, B_360))))), inference(negUnitSimplification, [status(thm)], [c_1827, c_24])).
% 4.52/1.84  tff(c_1923, plain, (v1_partfun1('#skF_7', '#skF_6') | ~v1_funct_2('#skF_7', '#skF_6', '#skF_6') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_514, c_1897])).
% 4.52/1.84  tff(c_1938, plain, (v1_partfun1('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_498, c_1923])).
% 4.52/1.84  tff(c_497, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_492, c_38])).
% 4.52/1.84  tff(c_1920, plain, (v1_partfun1('#skF_8', '#skF_6') | ~v1_funct_2('#skF_8', '#skF_6', '#skF_6') | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_520, c_1897])).
% 4.52/1.84  tff(c_1935, plain, (v1_partfun1('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_497, c_1920])).
% 4.52/1.84  tff(c_2332, plain, (![D_396, C_397, A_398, B_399]: (D_396=C_397 | ~r1_partfun1(C_397, D_396) | ~v1_partfun1(D_396, A_398) | ~v1_partfun1(C_397, A_398) | ~m1_subset_1(D_396, k1_zfmisc_1(k2_zfmisc_1(A_398, B_399))) | ~v1_funct_1(D_396) | ~m1_subset_1(C_397, k1_zfmisc_1(k2_zfmisc_1(A_398, B_399))) | ~v1_funct_1(C_397))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.52/1.84  tff(c_2334, plain, (![A_398, B_399]: ('#skF_7'='#skF_8' | ~v1_partfun1('#skF_8', A_398) | ~v1_partfun1('#skF_7', A_398) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(A_398, B_399))) | ~v1_funct_1('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_398, B_399))) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_34, c_2332])).
% 4.52/1.84  tff(c_2337, plain, (![A_398, B_399]: ('#skF_7'='#skF_8' | ~v1_partfun1('#skF_8', A_398) | ~v1_partfun1('#skF_7', A_398) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(A_398, B_399))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_398, B_399))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_2334])).
% 4.52/1.84  tff(c_2587, plain, (![A_423, B_424]: (~v1_partfun1('#skF_8', A_423) | ~v1_partfun1('#skF_7', A_423) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(A_423, B_424))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_423, B_424))))), inference(splitLeft, [status(thm)], [c_2337])).
% 4.52/1.84  tff(c_2590, plain, (~v1_partfun1('#skF_8', '#skF_6') | ~v1_partfun1('#skF_7', '#skF_6') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6')))), inference(resolution, [status(thm)], [c_514, c_2587])).
% 4.52/1.84  tff(c_2594, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_520, c_1938, c_1935, c_2590])).
% 4.52/1.84  tff(c_2595, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_2337])).
% 4.52/1.84  tff(c_2605, plain, (~r2_relset_1('#skF_6', '#skF_6', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2595, c_506])).
% 4.52/1.84  tff(c_2614, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2114, c_2605])).
% 4.52/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.52/1.84  
% 4.52/1.84  Inference rules
% 4.52/1.84  ----------------------
% 4.52/1.84  #Ref     : 0
% 4.52/1.84  #Sup     : 541
% 4.52/1.84  #Fact    : 0
% 4.52/1.84  #Define  : 0
% 4.52/1.84  #Split   : 26
% 4.52/1.84  #Chain   : 0
% 4.52/1.84  #Close   : 0
% 4.52/1.84  
% 4.52/1.84  Ordering : KBO
% 4.52/1.84  
% 4.52/1.84  Simplification rules
% 4.52/1.84  ----------------------
% 4.52/1.84  #Subsume      : 114
% 4.52/1.84  #Demod        : 306
% 4.52/1.84  #Tautology    : 119
% 4.52/1.84  #SimpNegUnit  : 37
% 4.52/1.84  #BackRed      : 130
% 4.52/1.84  
% 4.52/1.84  #Partial instantiations: 0
% 4.52/1.84  #Strategies tried      : 1
% 4.52/1.84  
% 4.52/1.84  Timing (in seconds)
% 4.52/1.84  ----------------------
% 4.52/1.85  Preprocessing        : 0.33
% 4.52/1.85  Parsing              : 0.19
% 4.52/1.85  CNF conversion       : 0.02
% 4.52/1.85  Main loop            : 0.72
% 4.52/1.85  Inferencing          : 0.26
% 4.52/1.85  Reduction            : 0.21
% 4.52/1.85  Demodulation         : 0.13
% 4.52/1.85  BG Simplification    : 0.03
% 4.52/1.85  Subsumption          : 0.14
% 4.52/1.85  Abstraction          : 0.04
% 4.52/1.85  MUC search           : 0.00
% 4.52/1.85  Cooper               : 0.00
% 4.52/1.85  Total                : 1.10
% 4.52/1.85  Index Insertion      : 0.00
% 4.52/1.85  Index Deletion       : 0.00
% 4.52/1.85  Index Matching       : 0.00
% 4.52/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
