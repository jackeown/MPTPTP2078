%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:07 EST 2020

% Result     : Theorem 8.84s
% Output     : CNFRefutation 8.84s
% Verified   : 
% Statistics : Number of formulae       :  228 (1582 expanded)
%              Number of leaves         :   45 ( 513 expanded)
%              Depth                    :   16
%              Number of atoms          :  379 (4276 expanded)
%              Number of equality atoms :   91 (1245 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_192,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(k2_relset_1(A,B,D),C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_127,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_162,axiom,(
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

tff(f_44,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_103,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_88,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_10538,plain,(
    ! [A_843,B_844,C_845] :
      ( k2_relset_1(A_843,B_844,C_845) = k2_relat_1(C_845)
      | ~ m1_subset_1(C_845,k1_zfmisc_1(k2_zfmisc_1(A_843,B_844))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_10557,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_88,c_10538])).

tff(c_86,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_10558,plain,(
    r1_tarski(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10557,c_86])).

tff(c_11000,plain,(
    ! [D_878,C_879,B_880,A_881] :
      ( m1_subset_1(D_878,k1_zfmisc_1(k2_zfmisc_1(C_879,B_880)))
      | ~ r1_tarski(k2_relat_1(D_878),B_880)
      | ~ m1_subset_1(D_878,k1_zfmisc_1(k2_zfmisc_1(C_879,A_881))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_11395,plain,(
    ! [B_893] :
      ( m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_893)))
      | ~ r1_tarski(k2_relat_1('#skF_7'),B_893) ) ),
    inference(resolution,[status(thm)],[c_88,c_11000])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_256,plain,(
    ! [A_96,B_97] :
      ( ~ r2_hidden('#skF_2'(A_96,B_97),B_97)
      | r1_tarski(A_96,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_261,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_256])).

tff(c_92,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_82,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_6')))
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_6')
    | ~ v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_94,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_6')))
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_82])).

tff(c_160,plain,(
    ~ v1_funct_2('#skF_7','#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_949,plain,(
    ! [A_190,B_191,C_192] :
      ( k2_relset_1(A_190,B_191,C_192) = k2_relat_1(C_192)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(A_190,B_191))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_964,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_88,c_949])).

tff(c_965,plain,(
    r1_tarski(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_964,c_86])).

tff(c_84,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_123,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_90,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_994,plain,(
    ! [A_199,B_200,C_201] :
      ( k1_relset_1(A_199,B_200,C_201) = k1_relat_1(C_201)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(A_199,B_200))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1009,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_88,c_994])).

tff(c_4080,plain,(
    ! [B_370,A_371,C_372] :
      ( k1_xboole_0 = B_370
      | k1_relset_1(A_371,B_370,C_372) = A_371
      | ~ v1_funct_2(C_372,A_371,B_370)
      | ~ m1_subset_1(C_372,k1_zfmisc_1(k2_zfmisc_1(A_371,B_370))) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_4093,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_4080])).

tff(c_4105,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_1009,c_4093])).

tff(c_4106,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_4105])).

tff(c_3930,plain,(
    ! [D_351,C_352,B_353,A_354] :
      ( m1_subset_1(D_351,k1_zfmisc_1(k2_zfmisc_1(C_352,B_353)))
      | ~ r1_tarski(k2_relat_1(D_351),B_353)
      | ~ m1_subset_1(D_351,k1_zfmisc_1(k2_zfmisc_1(C_352,A_354))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_4011,plain,(
    ! [B_368] :
      ( m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_368)))
      | ~ r1_tarski(k2_relat_1('#skF_7'),B_368) ) ),
    inference(resolution,[status(thm)],[c_88,c_3930])).

tff(c_52,plain,(
    ! [A_42,B_43,C_44] :
      ( k1_relset_1(A_42,B_43,C_44) = k1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_4049,plain,(
    ! [B_368] :
      ( k1_relset_1('#skF_4',B_368,'#skF_7') = k1_relat_1('#skF_7')
      | ~ r1_tarski(k2_relat_1('#skF_7'),B_368) ) ),
    inference(resolution,[status(thm)],[c_4011,c_52])).

tff(c_5364,plain,(
    ! [B_419] :
      ( k1_relset_1('#skF_4',B_419,'#skF_7') = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_7'),B_419) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4106,c_4049])).

tff(c_5380,plain,(
    k1_relset_1('#skF_4','#skF_6','#skF_7') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_965,c_5364])).

tff(c_3944,plain,(
    ! [B_353] :
      ( m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_353)))
      | ~ r1_tarski(k2_relat_1('#skF_7'),B_353) ) ),
    inference(resolution,[status(thm)],[c_88,c_3930])).

tff(c_4203,plain,(
    ! [B_373,C_374,A_375] :
      ( k1_xboole_0 = B_373
      | v1_funct_2(C_374,A_375,B_373)
      | k1_relset_1(A_375,B_373,C_374) != A_375
      | ~ m1_subset_1(C_374,k1_zfmisc_1(k2_zfmisc_1(A_375,B_373))) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_6220,plain,(
    ! [B_473] :
      ( k1_xboole_0 = B_473
      | v1_funct_2('#skF_7','#skF_4',B_473)
      | k1_relset_1('#skF_4',B_473,'#skF_7') != '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_7'),B_473) ) ),
    inference(resolution,[status(thm)],[c_3944,c_4203])).

tff(c_6223,plain,
    ( k1_xboole_0 = '#skF_6'
    | v1_funct_2('#skF_7','#skF_4','#skF_6')
    | k1_relset_1('#skF_4','#skF_6','#skF_7') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_965,c_6220])).

tff(c_6238,plain,
    ( k1_xboole_0 = '#skF_6'
    | v1_funct_2('#skF_7','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5380,c_6223])).

tff(c_6239,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_6238])).

tff(c_14,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_127,plain,(
    ! [A_73] :
      ( v1_xboole_0(A_73)
      | r2_hidden('#skF_1'(A_73),A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    ! [B_35,A_34] :
      ( ~ r1_tarski(B_35,A_34)
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_136,plain,(
    ! [A_74] :
      ( ~ r1_tarski(A_74,'#skF_1'(A_74))
      | v1_xboole_0(A_74) ) ),
    inference(resolution,[status(thm)],[c_127,c_44])).

tff(c_141,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_136])).

tff(c_20,plain,(
    ! [A_14] : k2_zfmisc_1(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_759,plain,(
    ! [C_169,A_170,B_171] :
      ( r1_tarski(k2_zfmisc_1(C_169,A_170),k2_zfmisc_1(C_169,B_171))
      | ~ r1_tarski(A_170,B_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_802,plain,(
    ! [A_174,A_175] :
      ( r1_tarski(k2_zfmisc_1(A_174,A_175),k1_xboole_0)
      | ~ r1_tarski(A_175,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_759])).

tff(c_36,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(A_29,k1_zfmisc_1(B_30))
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_196,plain,(
    ! [B_87,A_88] :
      ( v1_xboole_0(B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_88))
      | ~ v1_xboole_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_203,plain,(
    ! [A_29,B_30] :
      ( v1_xboole_0(A_29)
      | ~ v1_xboole_0(B_30)
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(resolution,[status(thm)],[c_36,c_196])).

tff(c_813,plain,(
    ! [A_174,A_175] :
      ( v1_xboole_0(k2_zfmisc_1(A_174,A_175))
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ r1_tarski(A_175,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_802,c_203])).

tff(c_826,plain,(
    ! [A_174,A_175] :
      ( v1_xboole_0(k2_zfmisc_1(A_174,A_175))
      | ~ r1_tarski(A_175,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_813])).

tff(c_172,plain,(
    ! [A_81,B_82] :
      ( r2_hidden('#skF_2'(A_81,B_82),A_81)
      | r1_tarski(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_180,plain,(
    ! [A_81,B_82] :
      ( ~ v1_xboole_0(A_81)
      | r1_tarski(A_81,B_82) ) ),
    inference(resolution,[status(thm)],[c_172,c_2])).

tff(c_279,plain,(
    ! [C_100,A_101,B_102] :
      ( v4_relat_1(C_100,A_101)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_414,plain,(
    ! [A_130,A_131,B_132] :
      ( v4_relat_1(A_130,A_131)
      | ~ r1_tarski(A_130,k2_zfmisc_1(A_131,B_132)) ) ),
    inference(resolution,[status(thm)],[c_36,c_279])).

tff(c_437,plain,(
    ! [A_81,A_131] :
      ( v4_relat_1(A_81,A_131)
      | ~ v1_xboole_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_180,c_414])).

tff(c_22,plain,(
    ! [B_15] : k2_zfmisc_1(k1_xboole_0,B_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_647,plain,(
    ! [A_160,C_161,B_162] :
      ( r1_tarski(k2_zfmisc_1(A_160,C_161),k2_zfmisc_1(B_162,C_161))
      | ~ r1_tarski(A_160,B_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_682,plain,(
    ! [A_163,B_164] :
      ( r1_tarski(k2_zfmisc_1(A_163,B_164),k1_xboole_0)
      | ~ r1_tarski(A_163,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_647])).

tff(c_691,plain,(
    ! [A_163,B_164] :
      ( v1_xboole_0(k2_zfmisc_1(A_163,B_164))
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ r1_tarski(A_163,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_682,c_203])).

tff(c_707,plain,(
    ! [A_165,B_166] :
      ( v1_xboole_0(k2_zfmisc_1(A_165,B_166))
      | ~ r1_tarski(A_165,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_691])).

tff(c_204,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_88,c_196])).

tff(c_205,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_204])).

tff(c_727,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_707,c_205])).

tff(c_736,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_180,c_727])).

tff(c_225,plain,(
    ! [C_91,A_92,B_93] :
      ( v1_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_238,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_88,c_225])).

tff(c_40,plain,(
    ! [B_32,A_31] :
      ( r1_tarski(k1_relat_1(B_32),A_31)
      | ~ v4_relat_1(B_32,A_31)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_334,plain,(
    ! [C_109,B_110,A_111] :
      ( r2_hidden(C_109,B_110)
      | ~ r2_hidden(C_109,A_111)
      | ~ r1_tarski(A_111,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_572,plain,(
    ! [A_156,B_157] :
      ( r2_hidden('#skF_1'(A_156),B_157)
      | ~ r1_tarski(A_156,B_157)
      | v1_xboole_0(A_156) ) ),
    inference(resolution,[status(thm)],[c_4,c_334])).

tff(c_187,plain,(
    ! [A_85,B_86] :
      ( r2_hidden('#skF_3'(A_85,B_86),B_86)
      | ~ r2_hidden(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_373,plain,(
    ! [B_124,A_125] :
      ( ~ r1_tarski(B_124,'#skF_3'(A_125,B_124))
      | ~ r2_hidden(A_125,B_124) ) ),
    inference(resolution,[status(thm)],[c_187,c_44])).

tff(c_383,plain,(
    ! [A_125] : ~ r2_hidden(A_125,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_373])).

tff(c_589,plain,(
    ! [A_158] :
      ( ~ r1_tarski(A_158,k1_xboole_0)
      | v1_xboole_0(A_158) ) ),
    inference(resolution,[status(thm)],[c_572,c_383])).

tff(c_606,plain,(
    ! [B_32] :
      ( v1_xboole_0(k1_relat_1(B_32))
      | ~ v4_relat_1(B_32,k1_xboole_0)
      | ~ v1_relat_1(B_32) ) ),
    inference(resolution,[status(thm)],[c_40,c_589])).

tff(c_4115,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v4_relat_1('#skF_7',k1_xboole_0)
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_4106,c_606])).

tff(c_4141,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v4_relat_1('#skF_7',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_4115])).

tff(c_4142,plain,(
    ~ v4_relat_1('#skF_7',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_736,c_4141])).

tff(c_4164,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_437,c_4142])).

tff(c_34,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,B_30)
      | ~ m1_subset_1(A_29,k1_zfmisc_1(B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4346,plain,(
    ! [B_378] :
      ( r1_tarski('#skF_7',k2_zfmisc_1('#skF_4',B_378))
      | ~ r1_tarski(k2_relat_1('#skF_7'),B_378) ) ),
    inference(resolution,[status(thm)],[c_4011,c_34])).

tff(c_4362,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_965,c_4346])).

tff(c_4378,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_4362,c_203])).

tff(c_4387,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_4164,c_4378])).

tff(c_4403,plain,(
    ~ r1_tarski('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_826,c_4387])).

tff(c_6274,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6239,c_4403])).

tff(c_6333,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_6274])).

tff(c_6334,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6342,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_6334,c_12])).

tff(c_6345,plain,(
    '#skF_7' != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6342,c_123])).

tff(c_6335,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_6376,plain,(
    ! [A_478] :
      ( A_478 = '#skF_7'
      | ~ v1_xboole_0(A_478) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6342,c_12])).

tff(c_6383,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_6335,c_6376])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( k1_xboole_0 = B_15
      | k1_xboole_0 = A_14
      | k2_zfmisc_1(A_14,B_15) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6768,plain,(
    ! [B_543,A_544] :
      ( B_543 = '#skF_7'
      | A_544 = '#skF_7'
      | k2_zfmisc_1(A_544,B_543) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6342,c_6342,c_6342,c_18])).

tff(c_6771,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_7' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_6383,c_6768])).

tff(c_6780,plain,(
    '#skF_7' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_6345,c_6771])).

tff(c_6363,plain,(
    ! [C_475,A_476,B_477] :
      ( v1_relat_1(C_475)
      | ~ m1_subset_1(C_475,k1_zfmisc_1(k2_zfmisc_1(A_476,B_477))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_6372,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_88,c_6363])).

tff(c_6800,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6780,c_6372])).

tff(c_6413,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6383,c_88])).

tff(c_6348,plain,(
    ! [A_14] : k2_zfmisc_1(A_14,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6342,c_6342,c_20])).

tff(c_6526,plain,(
    ! [C_494,A_495,B_496] :
      ( v4_relat_1(C_494,A_495)
      | ~ m1_subset_1(C_494,k1_zfmisc_1(k2_zfmisc_1(A_495,B_496))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_6542,plain,(
    ! [C_497,A_498] :
      ( v4_relat_1(C_497,A_498)
      | ~ m1_subset_1(C_497,k1_zfmisc_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6348,c_6526])).

tff(c_6548,plain,(
    ! [A_498] : v4_relat_1('#skF_7',A_498) ),
    inference(resolution,[status(thm)],[c_6413,c_6542])).

tff(c_6791,plain,(
    ! [A_498] : v4_relat_1('#skF_4',A_498) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6780,c_6548])).

tff(c_6630,plain,(
    ! [C_517,B_518,A_519] :
      ( r2_hidden(C_517,B_518)
      | ~ r2_hidden(C_517,A_519)
      | ~ r1_tarski(A_519,B_518) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_7414,plain,(
    ! [A_613,B_614] :
      ( r2_hidden('#skF_1'(A_613),B_614)
      | ~ r1_tarski(A_613,B_614)
      | v1_xboole_0(A_613) ) ),
    inference(resolution,[status(thm)],[c_4,c_6630])).

tff(c_6349,plain,(
    ! [A_11] : r1_tarski('#skF_7',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6342,c_14])).

tff(c_6552,plain,(
    ! [B_502,A_503] :
      ( ~ r1_tarski(B_502,'#skF_3'(A_503,B_502))
      | ~ r2_hidden(A_503,B_502) ) ),
    inference(resolution,[status(thm)],[c_187,c_44])).

tff(c_6561,plain,(
    ! [A_503] : ~ r2_hidden(A_503,'#skF_7') ),
    inference(resolution,[status(thm)],[c_6349,c_6552])).

tff(c_6789,plain,(
    ! [A_503] : ~ r2_hidden(A_503,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6780,c_6561])).

tff(c_7469,plain,(
    ! [A_616] :
      ( ~ r1_tarski(A_616,'#skF_4')
      | v1_xboole_0(A_616) ) ),
    inference(resolution,[status(thm)],[c_7414,c_6789])).

tff(c_7500,plain,(
    ! [B_617] :
      ( v1_xboole_0(k1_relat_1(B_617))
      | ~ v4_relat_1(B_617,'#skF_4')
      | ~ v1_relat_1(B_617) ) ),
    inference(resolution,[status(thm)],[c_40,c_7469])).

tff(c_6346,plain,(
    ! [A_10] :
      ( A_10 = '#skF_7'
      | ~ v1_xboole_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6342,c_12])).

tff(c_6799,plain,(
    ! [A_10] :
      ( A_10 = '#skF_4'
      | ~ v1_xboole_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6780,c_6346])).

tff(c_7521,plain,(
    ! [B_618] :
      ( k1_relat_1(B_618) = '#skF_4'
      | ~ v4_relat_1(B_618,'#skF_4')
      | ~ v1_relat_1(B_618) ) ),
    inference(resolution,[status(thm)],[c_7500,c_6799])).

tff(c_7533,plain,
    ( k1_relat_1('#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6791,c_7521])).

tff(c_7548,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6800,c_7533])).

tff(c_6801,plain,(
    ! [A_11] : r1_tarski('#skF_4',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6780,c_6349])).

tff(c_7340,plain,(
    ! [A_603,B_604,C_605] :
      ( k1_relset_1(A_603,B_604,C_605) = k1_relat_1(C_605)
      | ~ m1_subset_1(C_605,k1_zfmisc_1(k2_zfmisc_1(A_603,B_604))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_9291,plain,(
    ! [A_709,B_710,A_711] :
      ( k1_relset_1(A_709,B_710,A_711) = k1_relat_1(A_711)
      | ~ r1_tarski(A_711,k2_zfmisc_1(A_709,B_710)) ) ),
    inference(resolution,[status(thm)],[c_36,c_7340])).

tff(c_9319,plain,(
    ! [A_709,B_710] : k1_relset_1(A_709,B_710,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6801,c_9291])).

tff(c_9338,plain,(
    ! [A_709,B_710] : k1_relset_1(A_709,B_710,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7548,c_9319])).

tff(c_6795,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6780,c_6780,c_6413])).

tff(c_6803,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6780,c_6342])).

tff(c_68,plain,(
    ! [C_61,B_60] :
      ( v1_funct_2(C_61,k1_xboole_0,B_60)
      | k1_relset_1(k1_xboole_0,B_60,C_61) != k1_xboole_0
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_96,plain,(
    ! [C_61,B_60] :
      ( v1_funct_2(C_61,k1_xboole_0,B_60)
      | k1_relset_1(k1_xboole_0,B_60,C_61) != k1_xboole_0
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_68])).

tff(c_7690,plain,(
    ! [C_623,B_624] :
      ( v1_funct_2(C_623,'#skF_4',B_624)
      | k1_relset_1('#skF_4',B_624,C_623) != '#skF_4'
      | ~ m1_subset_1(C_623,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6803,c_6803,c_6803,c_6803,c_96])).

tff(c_7783,plain,(
    ! [B_630] :
      ( v1_funct_2('#skF_4','#skF_4',B_630)
      | k1_relset_1('#skF_4',B_630,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_6795,c_7690])).

tff(c_6805,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6780,c_160])).

tff(c_7794,plain,(
    k1_relset_1('#skF_4','#skF_6','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_7783,c_6805])).

tff(c_9349,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9338,c_7794])).

tff(c_9350,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_11424,plain,(
    ~ r1_tarski(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_11395,c_9350])).

tff(c_11458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10558,c_11424])).

tff(c_11459,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_11464,plain,(
    ! [A_11] : r1_tarski('#skF_4',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11459,c_14])).

tff(c_11503,plain,(
    ! [A_902] :
      ( v1_xboole_0(A_902)
      | r2_hidden('#skF_1'(A_902),A_902) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_11513,plain,(
    ! [A_905] :
      ( ~ r1_tarski(A_905,'#skF_1'(A_905))
      | v1_xboole_0(A_905) ) ),
    inference(resolution,[status(thm)],[c_11503,c_44])).

tff(c_11518,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_11464,c_11513])).

tff(c_11462,plain,(
    ! [B_15] : k2_zfmisc_1('#skF_4',B_15) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11459,c_11459,c_22])).

tff(c_11460,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_11469,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11459,c_11460])).

tff(c_11500,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11462,c_11469,c_88])).

tff(c_11537,plain,(
    ! [B_910,A_911] :
      ( v1_xboole_0(B_910)
      | ~ m1_subset_1(B_910,k1_zfmisc_1(A_911))
      | ~ v1_xboole_0(A_911) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_11543,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_11500,c_11537])).

tff(c_11547,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11518,c_11543])).

tff(c_11461,plain,(
    ! [A_10] :
      ( A_10 = '#skF_4'
      | ~ v1_xboole_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11459,c_12])).

tff(c_11556,plain,(
    '#skF_7' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_11547,c_11461])).

tff(c_11561,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11556,c_11500])).

tff(c_11463,plain,(
    ! [A_14] : k2_zfmisc_1(A_14,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11459,c_11459,c_20])).

tff(c_11582,plain,(
    ! [C_912,A_913,B_914] :
      ( v1_relat_1(C_912)
      | ~ m1_subset_1(C_912,k1_zfmisc_1(k2_zfmisc_1(A_913,B_914))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_11592,plain,(
    ! [C_915] :
      ( v1_relat_1(C_915)
      | ~ m1_subset_1(C_915,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11463,c_11582])).

tff(c_11600,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_11561,c_11592])).

tff(c_11675,plain,(
    ! [A_929,B_930] :
      ( ~ r2_hidden('#skF_2'(A_929,B_930),B_930)
      | r1_tarski(A_929,B_930) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_11680,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_11675])).

tff(c_11906,plain,(
    ! [C_971,A_972,B_973] :
      ( v4_relat_1(C_971,A_972)
      | ~ m1_subset_1(C_971,k1_zfmisc_1(k2_zfmisc_1(A_972,B_973))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_11928,plain,(
    ! [A_979,A_980,B_981] :
      ( v4_relat_1(A_979,A_980)
      | ~ r1_tarski(A_979,k2_zfmisc_1(A_980,B_981)) ) ),
    inference(resolution,[status(thm)],[c_36,c_11906])).

tff(c_11956,plain,(
    ! [A_980,B_981] : v4_relat_1(k2_zfmisc_1(A_980,B_981),A_980) ),
    inference(resolution,[status(thm)],[c_11680,c_11928])).

tff(c_11895,plain,(
    ! [C_967,B_968,A_969] :
      ( r2_hidden(C_967,B_968)
      | ~ r2_hidden(C_967,A_969)
      | ~ r1_tarski(A_969,B_968) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12089,plain,(
    ! [A_1001,B_1002] :
      ( r2_hidden('#skF_1'(A_1001),B_1002)
      | ~ r1_tarski(A_1001,B_1002)
      | v1_xboole_0(A_1001) ) ),
    inference(resolution,[status(thm)],[c_4,c_11895])).

tff(c_11666,plain,(
    ! [A_927,B_928] :
      ( r2_hidden('#skF_3'(A_927,B_928),B_928)
      | ~ r2_hidden(A_927,B_928) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_11716,plain,(
    ! [B_936,A_937] :
      ( ~ r1_tarski(B_936,'#skF_3'(A_937,B_936))
      | ~ r2_hidden(A_937,B_936) ) ),
    inference(resolution,[status(thm)],[c_11666,c_44])).

tff(c_11726,plain,(
    ! [A_937] : ~ r2_hidden(A_937,'#skF_4') ),
    inference(resolution,[status(thm)],[c_11464,c_11716])).

tff(c_12106,plain,(
    ! [A_1003] :
      ( ~ r1_tarski(A_1003,'#skF_4')
      | v1_xboole_0(A_1003) ) ),
    inference(resolution,[status(thm)],[c_12089,c_11726])).

tff(c_12133,plain,(
    ! [B_1004] :
      ( v1_xboole_0(k1_relat_1(B_1004))
      | ~ v4_relat_1(B_1004,'#skF_4')
      | ~ v1_relat_1(B_1004) ) ),
    inference(resolution,[status(thm)],[c_40,c_12106])).

tff(c_12181,plain,(
    ! [B_1008] :
      ( k1_relat_1(B_1008) = '#skF_4'
      | ~ v4_relat_1(B_1008,'#skF_4')
      | ~ v1_relat_1(B_1008) ) ),
    inference(resolution,[status(thm)],[c_12133,c_11461])).

tff(c_12193,plain,(
    ! [B_981] :
      ( k1_relat_1(k2_zfmisc_1('#skF_4',B_981)) = '#skF_4'
      | ~ v1_relat_1(k2_zfmisc_1('#skF_4',B_981)) ) ),
    inference(resolution,[status(thm)],[c_11956,c_12181])).

tff(c_12208,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11600,c_11462,c_11462,c_12193])).

tff(c_12733,plain,(
    ! [A_1050,B_1051,C_1052] :
      ( k1_relset_1(A_1050,B_1051,C_1052) = k1_relat_1(C_1052)
      | ~ m1_subset_1(C_1052,k1_zfmisc_1(k2_zfmisc_1(A_1050,B_1051))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_13642,plain,(
    ! [B_1100,C_1101] :
      ( k1_relset_1('#skF_4',B_1100,C_1101) = k1_relat_1(C_1101)
      | ~ m1_subset_1(C_1101,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11462,c_12733])).

tff(c_13644,plain,(
    ! [B_1100] : k1_relset_1('#skF_4',B_1100,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_11561,c_13642])).

tff(c_13649,plain,(
    ! [B_1100] : k1_relset_1('#skF_4',B_1100,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12208,c_13644])).

tff(c_13457,plain,(
    ! [C_1082,B_1083] :
      ( v1_funct_2(C_1082,'#skF_4',B_1083)
      | k1_relset_1('#skF_4',B_1083,C_1082) != '#skF_4'
      | ~ m1_subset_1(C_1082,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11459,c_11459,c_11459,c_11459,c_96])).

tff(c_13511,plain,(
    ! [B_1089] :
      ( v1_funct_2('#skF_4','#skF_4',B_1089)
      | k1_relset_1('#skF_4',B_1089,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_11561,c_13457])).

tff(c_11549,plain,(
    ~ v1_funct_2('#skF_7','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11500,c_11462,c_94])).

tff(c_11558,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11556,c_11549])).

tff(c_13522,plain,(
    k1_relset_1('#skF_4','#skF_6','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_13511,c_11558])).

tff(c_13656,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13649,c_13522])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:37:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.84/3.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.84/3.03  
% 8.84/3.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.84/3.04  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 8.84/3.04  
% 8.84/3.04  %Foreground sorts:
% 8.84/3.04  
% 8.84/3.04  
% 8.84/3.04  %Background operators:
% 8.84/3.04  
% 8.84/3.04  
% 8.84/3.04  %Foreground operators:
% 8.84/3.04  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.84/3.04  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.84/3.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.84/3.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.84/3.04  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.84/3.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.84/3.04  tff('#skF_7', type, '#skF_7': $i).
% 8.84/3.04  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.84/3.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.84/3.04  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.84/3.04  tff('#skF_5', type, '#skF_5': $i).
% 8.84/3.04  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.84/3.04  tff('#skF_6', type, '#skF_6': $i).
% 8.84/3.04  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.84/3.04  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.84/3.04  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.84/3.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.84/3.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.84/3.04  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.84/3.04  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.84/3.04  tff('#skF_4', type, '#skF_4': $i).
% 8.84/3.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.84/3.04  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.84/3.04  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.84/3.04  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.84/3.04  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.84/3.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.84/3.04  
% 8.84/3.06  tff(f_192, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_2)).
% 8.84/3.06  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.84/3.06  tff(f_127, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 8.84/3.06  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.84/3.06  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.84/3.06  tff(f_162, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 8.84/3.06  tff(f_44, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.84/3.06  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.84/3.06  tff(f_103, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 8.84/3.06  tff(f_58, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.84/3.06  tff(f_64, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 8.84/3.06  tff(f_88, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.84/3.06  tff(f_84, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 8.84/3.06  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.84/3.06  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.84/3.06  tff(f_94, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 8.84/3.06  tff(f_77, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 8.84/3.06  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 8.84/3.06  tff(c_88, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_192])).
% 8.84/3.06  tff(c_10538, plain, (![A_843, B_844, C_845]: (k2_relset_1(A_843, B_844, C_845)=k2_relat_1(C_845) | ~m1_subset_1(C_845, k1_zfmisc_1(k2_zfmisc_1(A_843, B_844))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.84/3.06  tff(c_10557, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_88, c_10538])).
% 8.84/3.06  tff(c_86, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_192])).
% 8.84/3.06  tff(c_10558, plain, (r1_tarski(k2_relat_1('#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10557, c_86])).
% 8.84/3.06  tff(c_11000, plain, (![D_878, C_879, B_880, A_881]: (m1_subset_1(D_878, k1_zfmisc_1(k2_zfmisc_1(C_879, B_880))) | ~r1_tarski(k2_relat_1(D_878), B_880) | ~m1_subset_1(D_878, k1_zfmisc_1(k2_zfmisc_1(C_879, A_881))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.84/3.06  tff(c_11395, plain, (![B_893]: (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_893))) | ~r1_tarski(k2_relat_1('#skF_7'), B_893))), inference(resolution, [status(thm)], [c_88, c_11000])).
% 8.84/3.06  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.84/3.06  tff(c_256, plain, (![A_96, B_97]: (~r2_hidden('#skF_2'(A_96, B_97), B_97) | r1_tarski(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.84/3.06  tff(c_261, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_256])).
% 8.84/3.06  tff(c_92, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_192])).
% 8.84/3.06  tff(c_82, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_6'))) | ~v1_funct_2('#skF_7', '#skF_4', '#skF_6') | ~v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_192])).
% 8.84/3.06  tff(c_94, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_6'))) | ~v1_funct_2('#skF_7', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_82])).
% 8.84/3.06  tff(c_160, plain, (~v1_funct_2('#skF_7', '#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_94])).
% 8.84/3.06  tff(c_949, plain, (![A_190, B_191, C_192]: (k2_relset_1(A_190, B_191, C_192)=k2_relat_1(C_192) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(A_190, B_191))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.84/3.06  tff(c_964, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_88, c_949])).
% 8.84/3.06  tff(c_965, plain, (r1_tarski(k2_relat_1('#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_964, c_86])).
% 8.84/3.06  tff(c_84, plain, (k1_xboole_0='#skF_4' | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_192])).
% 8.84/3.06  tff(c_123, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_84])).
% 8.84/3.06  tff(c_90, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_192])).
% 8.84/3.06  tff(c_994, plain, (![A_199, B_200, C_201]: (k1_relset_1(A_199, B_200, C_201)=k1_relat_1(C_201) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(A_199, B_200))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.84/3.06  tff(c_1009, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_88, c_994])).
% 8.84/3.06  tff(c_4080, plain, (![B_370, A_371, C_372]: (k1_xboole_0=B_370 | k1_relset_1(A_371, B_370, C_372)=A_371 | ~v1_funct_2(C_372, A_371, B_370) | ~m1_subset_1(C_372, k1_zfmisc_1(k2_zfmisc_1(A_371, B_370))))), inference(cnfTransformation, [status(thm)], [f_162])).
% 8.84/3.06  tff(c_4093, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_88, c_4080])).
% 8.84/3.06  tff(c_4105, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_1009, c_4093])).
% 8.84/3.06  tff(c_4106, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_123, c_4105])).
% 8.84/3.06  tff(c_3930, plain, (![D_351, C_352, B_353, A_354]: (m1_subset_1(D_351, k1_zfmisc_1(k2_zfmisc_1(C_352, B_353))) | ~r1_tarski(k2_relat_1(D_351), B_353) | ~m1_subset_1(D_351, k1_zfmisc_1(k2_zfmisc_1(C_352, A_354))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.84/3.06  tff(c_4011, plain, (![B_368]: (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_368))) | ~r1_tarski(k2_relat_1('#skF_7'), B_368))), inference(resolution, [status(thm)], [c_88, c_3930])).
% 8.84/3.06  tff(c_52, plain, (![A_42, B_43, C_44]: (k1_relset_1(A_42, B_43, C_44)=k1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.84/3.06  tff(c_4049, plain, (![B_368]: (k1_relset_1('#skF_4', B_368, '#skF_7')=k1_relat_1('#skF_7') | ~r1_tarski(k2_relat_1('#skF_7'), B_368))), inference(resolution, [status(thm)], [c_4011, c_52])).
% 8.84/3.06  tff(c_5364, plain, (![B_419]: (k1_relset_1('#skF_4', B_419, '#skF_7')='#skF_4' | ~r1_tarski(k2_relat_1('#skF_7'), B_419))), inference(demodulation, [status(thm), theory('equality')], [c_4106, c_4049])).
% 8.84/3.06  tff(c_5380, plain, (k1_relset_1('#skF_4', '#skF_6', '#skF_7')='#skF_4'), inference(resolution, [status(thm)], [c_965, c_5364])).
% 8.84/3.06  tff(c_3944, plain, (![B_353]: (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_353))) | ~r1_tarski(k2_relat_1('#skF_7'), B_353))), inference(resolution, [status(thm)], [c_88, c_3930])).
% 8.84/3.06  tff(c_4203, plain, (![B_373, C_374, A_375]: (k1_xboole_0=B_373 | v1_funct_2(C_374, A_375, B_373) | k1_relset_1(A_375, B_373, C_374)!=A_375 | ~m1_subset_1(C_374, k1_zfmisc_1(k2_zfmisc_1(A_375, B_373))))), inference(cnfTransformation, [status(thm)], [f_162])).
% 8.84/3.06  tff(c_6220, plain, (![B_473]: (k1_xboole_0=B_473 | v1_funct_2('#skF_7', '#skF_4', B_473) | k1_relset_1('#skF_4', B_473, '#skF_7')!='#skF_4' | ~r1_tarski(k2_relat_1('#skF_7'), B_473))), inference(resolution, [status(thm)], [c_3944, c_4203])).
% 8.84/3.06  tff(c_6223, plain, (k1_xboole_0='#skF_6' | v1_funct_2('#skF_7', '#skF_4', '#skF_6') | k1_relset_1('#skF_4', '#skF_6', '#skF_7')!='#skF_4'), inference(resolution, [status(thm)], [c_965, c_6220])).
% 8.84/3.06  tff(c_6238, plain, (k1_xboole_0='#skF_6' | v1_funct_2('#skF_7', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5380, c_6223])).
% 8.84/3.06  tff(c_6239, plain, (k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_160, c_6238])).
% 8.84/3.06  tff(c_14, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.84/3.06  tff(c_127, plain, (![A_73]: (v1_xboole_0(A_73) | r2_hidden('#skF_1'(A_73), A_73))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.84/3.06  tff(c_44, plain, (![B_35, A_34]: (~r1_tarski(B_35, A_34) | ~r2_hidden(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.84/3.06  tff(c_136, plain, (![A_74]: (~r1_tarski(A_74, '#skF_1'(A_74)) | v1_xboole_0(A_74))), inference(resolution, [status(thm)], [c_127, c_44])).
% 8.84/3.06  tff(c_141, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_136])).
% 8.84/3.06  tff(c_20, plain, (![A_14]: (k2_zfmisc_1(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.84/3.06  tff(c_759, plain, (![C_169, A_170, B_171]: (r1_tarski(k2_zfmisc_1(C_169, A_170), k2_zfmisc_1(C_169, B_171)) | ~r1_tarski(A_170, B_171))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.84/3.06  tff(c_802, plain, (![A_174, A_175]: (r1_tarski(k2_zfmisc_1(A_174, A_175), k1_xboole_0) | ~r1_tarski(A_175, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_759])).
% 8.84/3.06  tff(c_36, plain, (![A_29, B_30]: (m1_subset_1(A_29, k1_zfmisc_1(B_30)) | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.84/3.06  tff(c_196, plain, (![B_87, A_88]: (v1_xboole_0(B_87) | ~m1_subset_1(B_87, k1_zfmisc_1(A_88)) | ~v1_xboole_0(A_88))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.84/3.06  tff(c_203, plain, (![A_29, B_30]: (v1_xboole_0(A_29) | ~v1_xboole_0(B_30) | ~r1_tarski(A_29, B_30))), inference(resolution, [status(thm)], [c_36, c_196])).
% 8.84/3.06  tff(c_813, plain, (![A_174, A_175]: (v1_xboole_0(k2_zfmisc_1(A_174, A_175)) | ~v1_xboole_0(k1_xboole_0) | ~r1_tarski(A_175, k1_xboole_0))), inference(resolution, [status(thm)], [c_802, c_203])).
% 8.84/3.06  tff(c_826, plain, (![A_174, A_175]: (v1_xboole_0(k2_zfmisc_1(A_174, A_175)) | ~r1_tarski(A_175, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_813])).
% 8.84/3.06  tff(c_172, plain, (![A_81, B_82]: (r2_hidden('#skF_2'(A_81, B_82), A_81) | r1_tarski(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.84/3.06  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.84/3.06  tff(c_180, plain, (![A_81, B_82]: (~v1_xboole_0(A_81) | r1_tarski(A_81, B_82))), inference(resolution, [status(thm)], [c_172, c_2])).
% 8.84/3.06  tff(c_279, plain, (![C_100, A_101, B_102]: (v4_relat_1(C_100, A_101) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.84/3.06  tff(c_414, plain, (![A_130, A_131, B_132]: (v4_relat_1(A_130, A_131) | ~r1_tarski(A_130, k2_zfmisc_1(A_131, B_132)))), inference(resolution, [status(thm)], [c_36, c_279])).
% 8.84/3.06  tff(c_437, plain, (![A_81, A_131]: (v4_relat_1(A_81, A_131) | ~v1_xboole_0(A_81))), inference(resolution, [status(thm)], [c_180, c_414])).
% 8.84/3.06  tff(c_22, plain, (![B_15]: (k2_zfmisc_1(k1_xboole_0, B_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.84/3.06  tff(c_647, plain, (![A_160, C_161, B_162]: (r1_tarski(k2_zfmisc_1(A_160, C_161), k2_zfmisc_1(B_162, C_161)) | ~r1_tarski(A_160, B_162))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.84/3.06  tff(c_682, plain, (![A_163, B_164]: (r1_tarski(k2_zfmisc_1(A_163, B_164), k1_xboole_0) | ~r1_tarski(A_163, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_647])).
% 8.84/3.06  tff(c_691, plain, (![A_163, B_164]: (v1_xboole_0(k2_zfmisc_1(A_163, B_164)) | ~v1_xboole_0(k1_xboole_0) | ~r1_tarski(A_163, k1_xboole_0))), inference(resolution, [status(thm)], [c_682, c_203])).
% 8.84/3.06  tff(c_707, plain, (![A_165, B_166]: (v1_xboole_0(k2_zfmisc_1(A_165, B_166)) | ~r1_tarski(A_165, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_691])).
% 8.84/3.06  tff(c_204, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_88, c_196])).
% 8.84/3.06  tff(c_205, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_204])).
% 8.84/3.06  tff(c_727, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_707, c_205])).
% 8.84/3.06  tff(c_736, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_180, c_727])).
% 8.84/3.06  tff(c_225, plain, (![C_91, A_92, B_93]: (v1_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.84/3.06  tff(c_238, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_88, c_225])).
% 8.84/3.06  tff(c_40, plain, (![B_32, A_31]: (r1_tarski(k1_relat_1(B_32), A_31) | ~v4_relat_1(B_32, A_31) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.84/3.06  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.84/3.06  tff(c_334, plain, (![C_109, B_110, A_111]: (r2_hidden(C_109, B_110) | ~r2_hidden(C_109, A_111) | ~r1_tarski(A_111, B_110))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.84/3.06  tff(c_572, plain, (![A_156, B_157]: (r2_hidden('#skF_1'(A_156), B_157) | ~r1_tarski(A_156, B_157) | v1_xboole_0(A_156))), inference(resolution, [status(thm)], [c_4, c_334])).
% 8.84/3.06  tff(c_187, plain, (![A_85, B_86]: (r2_hidden('#skF_3'(A_85, B_86), B_86) | ~r2_hidden(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.84/3.06  tff(c_373, plain, (![B_124, A_125]: (~r1_tarski(B_124, '#skF_3'(A_125, B_124)) | ~r2_hidden(A_125, B_124))), inference(resolution, [status(thm)], [c_187, c_44])).
% 8.84/3.06  tff(c_383, plain, (![A_125]: (~r2_hidden(A_125, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_373])).
% 8.84/3.06  tff(c_589, plain, (![A_158]: (~r1_tarski(A_158, k1_xboole_0) | v1_xboole_0(A_158))), inference(resolution, [status(thm)], [c_572, c_383])).
% 8.84/3.06  tff(c_606, plain, (![B_32]: (v1_xboole_0(k1_relat_1(B_32)) | ~v4_relat_1(B_32, k1_xboole_0) | ~v1_relat_1(B_32))), inference(resolution, [status(thm)], [c_40, c_589])).
% 8.84/3.06  tff(c_4115, plain, (v1_xboole_0('#skF_4') | ~v4_relat_1('#skF_7', k1_xboole_0) | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_4106, c_606])).
% 8.84/3.06  tff(c_4141, plain, (v1_xboole_0('#skF_4') | ~v4_relat_1('#skF_7', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_238, c_4115])).
% 8.84/3.06  tff(c_4142, plain, (~v4_relat_1('#skF_7', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_736, c_4141])).
% 8.84/3.06  tff(c_4164, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_437, c_4142])).
% 8.84/3.06  tff(c_34, plain, (![A_29, B_30]: (r1_tarski(A_29, B_30) | ~m1_subset_1(A_29, k1_zfmisc_1(B_30)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.84/3.06  tff(c_4346, plain, (![B_378]: (r1_tarski('#skF_7', k2_zfmisc_1('#skF_4', B_378)) | ~r1_tarski(k2_relat_1('#skF_7'), B_378))), inference(resolution, [status(thm)], [c_4011, c_34])).
% 8.84/3.06  tff(c_4362, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_965, c_4346])).
% 8.84/3.06  tff(c_4378, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_4362, c_203])).
% 8.84/3.06  tff(c_4387, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_4164, c_4378])).
% 8.84/3.06  tff(c_4403, plain, (~r1_tarski('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_826, c_4387])).
% 8.84/3.06  tff(c_6274, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6239, c_4403])).
% 8.84/3.06  tff(c_6333, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_261, c_6274])).
% 8.84/3.06  tff(c_6334, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_204])).
% 8.84/3.06  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.84/3.06  tff(c_6342, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_6334, c_12])).
% 8.84/3.06  tff(c_6345, plain, ('#skF_7'!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_6342, c_123])).
% 8.84/3.06  tff(c_6335, plain, (v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_204])).
% 8.84/3.06  tff(c_6376, plain, (![A_478]: (A_478='#skF_7' | ~v1_xboole_0(A_478))), inference(demodulation, [status(thm), theory('equality')], [c_6342, c_12])).
% 8.84/3.06  tff(c_6383, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_7'), inference(resolution, [status(thm)], [c_6335, c_6376])).
% 8.84/3.06  tff(c_18, plain, (![B_15, A_14]: (k1_xboole_0=B_15 | k1_xboole_0=A_14 | k2_zfmisc_1(A_14, B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.84/3.06  tff(c_6768, plain, (![B_543, A_544]: (B_543='#skF_7' | A_544='#skF_7' | k2_zfmisc_1(A_544, B_543)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6342, c_6342, c_6342, c_18])).
% 8.84/3.06  tff(c_6771, plain, ('#skF_7'='#skF_5' | '#skF_7'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_6383, c_6768])).
% 8.84/3.06  tff(c_6780, plain, ('#skF_7'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_6345, c_6771])).
% 8.84/3.06  tff(c_6363, plain, (![C_475, A_476, B_477]: (v1_relat_1(C_475) | ~m1_subset_1(C_475, k1_zfmisc_1(k2_zfmisc_1(A_476, B_477))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.84/3.06  tff(c_6372, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_88, c_6363])).
% 8.84/3.06  tff(c_6800, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6780, c_6372])).
% 8.84/3.06  tff(c_6413, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_6383, c_88])).
% 8.84/3.06  tff(c_6348, plain, (![A_14]: (k2_zfmisc_1(A_14, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6342, c_6342, c_20])).
% 8.84/3.06  tff(c_6526, plain, (![C_494, A_495, B_496]: (v4_relat_1(C_494, A_495) | ~m1_subset_1(C_494, k1_zfmisc_1(k2_zfmisc_1(A_495, B_496))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.84/3.06  tff(c_6542, plain, (![C_497, A_498]: (v4_relat_1(C_497, A_498) | ~m1_subset_1(C_497, k1_zfmisc_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_6348, c_6526])).
% 8.84/3.06  tff(c_6548, plain, (![A_498]: (v4_relat_1('#skF_7', A_498))), inference(resolution, [status(thm)], [c_6413, c_6542])).
% 8.84/3.06  tff(c_6791, plain, (![A_498]: (v4_relat_1('#skF_4', A_498))), inference(demodulation, [status(thm), theory('equality')], [c_6780, c_6548])).
% 8.84/3.06  tff(c_6630, plain, (![C_517, B_518, A_519]: (r2_hidden(C_517, B_518) | ~r2_hidden(C_517, A_519) | ~r1_tarski(A_519, B_518))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.84/3.06  tff(c_7414, plain, (![A_613, B_614]: (r2_hidden('#skF_1'(A_613), B_614) | ~r1_tarski(A_613, B_614) | v1_xboole_0(A_613))), inference(resolution, [status(thm)], [c_4, c_6630])).
% 8.84/3.06  tff(c_6349, plain, (![A_11]: (r1_tarski('#skF_7', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_6342, c_14])).
% 8.84/3.06  tff(c_6552, plain, (![B_502, A_503]: (~r1_tarski(B_502, '#skF_3'(A_503, B_502)) | ~r2_hidden(A_503, B_502))), inference(resolution, [status(thm)], [c_187, c_44])).
% 8.84/3.06  tff(c_6561, plain, (![A_503]: (~r2_hidden(A_503, '#skF_7'))), inference(resolution, [status(thm)], [c_6349, c_6552])).
% 8.84/3.06  tff(c_6789, plain, (![A_503]: (~r2_hidden(A_503, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6780, c_6561])).
% 8.84/3.06  tff(c_7469, plain, (![A_616]: (~r1_tarski(A_616, '#skF_4') | v1_xboole_0(A_616))), inference(resolution, [status(thm)], [c_7414, c_6789])).
% 8.84/3.06  tff(c_7500, plain, (![B_617]: (v1_xboole_0(k1_relat_1(B_617)) | ~v4_relat_1(B_617, '#skF_4') | ~v1_relat_1(B_617))), inference(resolution, [status(thm)], [c_40, c_7469])).
% 8.84/3.06  tff(c_6346, plain, (![A_10]: (A_10='#skF_7' | ~v1_xboole_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_6342, c_12])).
% 8.84/3.06  tff(c_6799, plain, (![A_10]: (A_10='#skF_4' | ~v1_xboole_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_6780, c_6346])).
% 8.84/3.06  tff(c_7521, plain, (![B_618]: (k1_relat_1(B_618)='#skF_4' | ~v4_relat_1(B_618, '#skF_4') | ~v1_relat_1(B_618))), inference(resolution, [status(thm)], [c_7500, c_6799])).
% 8.84/3.06  tff(c_7533, plain, (k1_relat_1('#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6791, c_7521])).
% 8.84/3.06  tff(c_7548, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6800, c_7533])).
% 8.84/3.06  tff(c_6801, plain, (![A_11]: (r1_tarski('#skF_4', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_6780, c_6349])).
% 8.84/3.06  tff(c_7340, plain, (![A_603, B_604, C_605]: (k1_relset_1(A_603, B_604, C_605)=k1_relat_1(C_605) | ~m1_subset_1(C_605, k1_zfmisc_1(k2_zfmisc_1(A_603, B_604))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.84/3.06  tff(c_9291, plain, (![A_709, B_710, A_711]: (k1_relset_1(A_709, B_710, A_711)=k1_relat_1(A_711) | ~r1_tarski(A_711, k2_zfmisc_1(A_709, B_710)))), inference(resolution, [status(thm)], [c_36, c_7340])).
% 8.84/3.06  tff(c_9319, plain, (![A_709, B_710]: (k1_relset_1(A_709, B_710, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_6801, c_9291])).
% 8.84/3.06  tff(c_9338, plain, (![A_709, B_710]: (k1_relset_1(A_709, B_710, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7548, c_9319])).
% 8.84/3.06  tff(c_6795, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6780, c_6780, c_6413])).
% 8.84/3.06  tff(c_6803, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6780, c_6342])).
% 8.84/3.06  tff(c_68, plain, (![C_61, B_60]: (v1_funct_2(C_61, k1_xboole_0, B_60) | k1_relset_1(k1_xboole_0, B_60, C_61)!=k1_xboole_0 | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_60))))), inference(cnfTransformation, [status(thm)], [f_162])).
% 8.84/3.06  tff(c_96, plain, (![C_61, B_60]: (v1_funct_2(C_61, k1_xboole_0, B_60) | k1_relset_1(k1_xboole_0, B_60, C_61)!=k1_xboole_0 | ~m1_subset_1(C_61, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_68])).
% 8.84/3.06  tff(c_7690, plain, (![C_623, B_624]: (v1_funct_2(C_623, '#skF_4', B_624) | k1_relset_1('#skF_4', B_624, C_623)!='#skF_4' | ~m1_subset_1(C_623, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_6803, c_6803, c_6803, c_6803, c_96])).
% 8.84/3.06  tff(c_7783, plain, (![B_630]: (v1_funct_2('#skF_4', '#skF_4', B_630) | k1_relset_1('#skF_4', B_630, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_6795, c_7690])).
% 8.84/3.06  tff(c_6805, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6780, c_160])).
% 8.84/3.06  tff(c_7794, plain, (k1_relset_1('#skF_4', '#skF_6', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_7783, c_6805])).
% 8.84/3.06  tff(c_9349, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9338, c_7794])).
% 8.84/3.06  tff(c_9350, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_6')))), inference(splitRight, [status(thm)], [c_94])).
% 8.84/3.06  tff(c_11424, plain, (~r1_tarski(k2_relat_1('#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_11395, c_9350])).
% 8.84/3.06  tff(c_11458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10558, c_11424])).
% 8.84/3.06  tff(c_11459, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_84])).
% 8.84/3.06  tff(c_11464, plain, (![A_11]: (r1_tarski('#skF_4', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_11459, c_14])).
% 8.84/3.06  tff(c_11503, plain, (![A_902]: (v1_xboole_0(A_902) | r2_hidden('#skF_1'(A_902), A_902))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.84/3.06  tff(c_11513, plain, (![A_905]: (~r1_tarski(A_905, '#skF_1'(A_905)) | v1_xboole_0(A_905))), inference(resolution, [status(thm)], [c_11503, c_44])).
% 8.84/3.06  tff(c_11518, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_11464, c_11513])).
% 8.84/3.06  tff(c_11462, plain, (![B_15]: (k2_zfmisc_1('#skF_4', B_15)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11459, c_11459, c_22])).
% 8.84/3.06  tff(c_11460, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_84])).
% 8.84/3.06  tff(c_11469, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11459, c_11460])).
% 8.84/3.06  tff(c_11500, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11462, c_11469, c_88])).
% 8.84/3.06  tff(c_11537, plain, (![B_910, A_911]: (v1_xboole_0(B_910) | ~m1_subset_1(B_910, k1_zfmisc_1(A_911)) | ~v1_xboole_0(A_911))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.84/3.06  tff(c_11543, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_11500, c_11537])).
% 8.84/3.06  tff(c_11547, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_11518, c_11543])).
% 8.84/3.06  tff(c_11461, plain, (![A_10]: (A_10='#skF_4' | ~v1_xboole_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_11459, c_12])).
% 8.84/3.06  tff(c_11556, plain, ('#skF_7'='#skF_4'), inference(resolution, [status(thm)], [c_11547, c_11461])).
% 8.84/3.06  tff(c_11561, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11556, c_11500])).
% 8.84/3.06  tff(c_11463, plain, (![A_14]: (k2_zfmisc_1(A_14, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11459, c_11459, c_20])).
% 8.84/3.06  tff(c_11582, plain, (![C_912, A_913, B_914]: (v1_relat_1(C_912) | ~m1_subset_1(C_912, k1_zfmisc_1(k2_zfmisc_1(A_913, B_914))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.84/3.06  tff(c_11592, plain, (![C_915]: (v1_relat_1(C_915) | ~m1_subset_1(C_915, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_11463, c_11582])).
% 8.84/3.06  tff(c_11600, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_11561, c_11592])).
% 8.84/3.06  tff(c_11675, plain, (![A_929, B_930]: (~r2_hidden('#skF_2'(A_929, B_930), B_930) | r1_tarski(A_929, B_930))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.84/3.06  tff(c_11680, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_11675])).
% 8.84/3.06  tff(c_11906, plain, (![C_971, A_972, B_973]: (v4_relat_1(C_971, A_972) | ~m1_subset_1(C_971, k1_zfmisc_1(k2_zfmisc_1(A_972, B_973))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.84/3.06  tff(c_11928, plain, (![A_979, A_980, B_981]: (v4_relat_1(A_979, A_980) | ~r1_tarski(A_979, k2_zfmisc_1(A_980, B_981)))), inference(resolution, [status(thm)], [c_36, c_11906])).
% 8.84/3.06  tff(c_11956, plain, (![A_980, B_981]: (v4_relat_1(k2_zfmisc_1(A_980, B_981), A_980))), inference(resolution, [status(thm)], [c_11680, c_11928])).
% 8.84/3.06  tff(c_11895, plain, (![C_967, B_968, A_969]: (r2_hidden(C_967, B_968) | ~r2_hidden(C_967, A_969) | ~r1_tarski(A_969, B_968))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.84/3.06  tff(c_12089, plain, (![A_1001, B_1002]: (r2_hidden('#skF_1'(A_1001), B_1002) | ~r1_tarski(A_1001, B_1002) | v1_xboole_0(A_1001))), inference(resolution, [status(thm)], [c_4, c_11895])).
% 8.84/3.06  tff(c_11666, plain, (![A_927, B_928]: (r2_hidden('#skF_3'(A_927, B_928), B_928) | ~r2_hidden(A_927, B_928))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.84/3.06  tff(c_11716, plain, (![B_936, A_937]: (~r1_tarski(B_936, '#skF_3'(A_937, B_936)) | ~r2_hidden(A_937, B_936))), inference(resolution, [status(thm)], [c_11666, c_44])).
% 8.84/3.06  tff(c_11726, plain, (![A_937]: (~r2_hidden(A_937, '#skF_4'))), inference(resolution, [status(thm)], [c_11464, c_11716])).
% 8.84/3.06  tff(c_12106, plain, (![A_1003]: (~r1_tarski(A_1003, '#skF_4') | v1_xboole_0(A_1003))), inference(resolution, [status(thm)], [c_12089, c_11726])).
% 8.84/3.06  tff(c_12133, plain, (![B_1004]: (v1_xboole_0(k1_relat_1(B_1004)) | ~v4_relat_1(B_1004, '#skF_4') | ~v1_relat_1(B_1004))), inference(resolution, [status(thm)], [c_40, c_12106])).
% 8.84/3.06  tff(c_12181, plain, (![B_1008]: (k1_relat_1(B_1008)='#skF_4' | ~v4_relat_1(B_1008, '#skF_4') | ~v1_relat_1(B_1008))), inference(resolution, [status(thm)], [c_12133, c_11461])).
% 8.84/3.06  tff(c_12193, plain, (![B_981]: (k1_relat_1(k2_zfmisc_1('#skF_4', B_981))='#skF_4' | ~v1_relat_1(k2_zfmisc_1('#skF_4', B_981)))), inference(resolution, [status(thm)], [c_11956, c_12181])).
% 8.84/3.06  tff(c_12208, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11600, c_11462, c_11462, c_12193])).
% 8.84/3.06  tff(c_12733, plain, (![A_1050, B_1051, C_1052]: (k1_relset_1(A_1050, B_1051, C_1052)=k1_relat_1(C_1052) | ~m1_subset_1(C_1052, k1_zfmisc_1(k2_zfmisc_1(A_1050, B_1051))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.84/3.06  tff(c_13642, plain, (![B_1100, C_1101]: (k1_relset_1('#skF_4', B_1100, C_1101)=k1_relat_1(C_1101) | ~m1_subset_1(C_1101, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_11462, c_12733])).
% 8.84/3.06  tff(c_13644, plain, (![B_1100]: (k1_relset_1('#skF_4', B_1100, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_11561, c_13642])).
% 8.84/3.06  tff(c_13649, plain, (![B_1100]: (k1_relset_1('#skF_4', B_1100, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12208, c_13644])).
% 8.84/3.06  tff(c_13457, plain, (![C_1082, B_1083]: (v1_funct_2(C_1082, '#skF_4', B_1083) | k1_relset_1('#skF_4', B_1083, C_1082)!='#skF_4' | ~m1_subset_1(C_1082, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_11459, c_11459, c_11459, c_11459, c_96])).
% 8.84/3.06  tff(c_13511, plain, (![B_1089]: (v1_funct_2('#skF_4', '#skF_4', B_1089) | k1_relset_1('#skF_4', B_1089, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_11561, c_13457])).
% 8.84/3.06  tff(c_11549, plain, (~v1_funct_2('#skF_7', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11500, c_11462, c_94])).
% 8.84/3.06  tff(c_11558, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11556, c_11549])).
% 8.84/3.06  tff(c_13522, plain, (k1_relset_1('#skF_4', '#skF_6', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_13511, c_11558])).
% 8.84/3.06  tff(c_13656, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13649, c_13522])).
% 8.84/3.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.84/3.06  
% 8.84/3.06  Inference rules
% 8.84/3.06  ----------------------
% 8.84/3.06  #Ref     : 0
% 8.84/3.06  #Sup     : 3092
% 8.84/3.06  #Fact    : 0
% 8.84/3.06  #Define  : 0
% 8.84/3.06  #Split   : 23
% 8.84/3.06  #Chain   : 0
% 8.84/3.06  #Close   : 0
% 8.84/3.06  
% 8.84/3.06  Ordering : KBO
% 8.84/3.06  
% 8.84/3.06  Simplification rules
% 8.84/3.06  ----------------------
% 8.84/3.06  #Subsume      : 666
% 8.84/3.06  #Demod        : 2189
% 8.84/3.06  #Tautology    : 1421
% 8.84/3.06  #SimpNegUnit  : 22
% 8.84/3.06  #BackRed      : 281
% 8.84/3.06  
% 8.84/3.06  #Partial instantiations: 0
% 8.84/3.06  #Strategies tried      : 1
% 8.84/3.06  
% 8.84/3.06  Timing (in seconds)
% 8.84/3.06  ----------------------
% 8.84/3.07  Preprocessing        : 0.46
% 8.84/3.07  Parsing              : 0.23
% 8.84/3.07  CNF conversion       : 0.03
% 8.84/3.07  Main loop            : 1.76
% 8.84/3.07  Inferencing          : 0.57
% 9.12/3.07  Reduction            : 0.58
% 9.12/3.07  Demodulation         : 0.40
% 9.12/3.07  BG Simplification    : 0.06
% 9.12/3.07  Subsumption          : 0.40
% 9.12/3.07  Abstraction          : 0.07
% 9.12/3.07  MUC search           : 0.00
% 9.12/3.07  Cooper               : 0.00
% 9.12/3.07  Total                : 2.28
% 9.12/3.07  Index Insertion      : 0.00
% 9.12/3.07  Index Deletion       : 0.00
% 9.12/3.07  Index Matching       : 0.00
% 9.12/3.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
