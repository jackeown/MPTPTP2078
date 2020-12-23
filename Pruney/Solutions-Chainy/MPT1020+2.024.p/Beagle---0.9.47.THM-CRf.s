%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:53 EST 2020

% Result     : Theorem 5.57s
% Output     : CNFRefutation 5.89s
% Verified   : 
% Statistics : Number of formulae       :  262 (4339 expanded)
%              Number of leaves         :   48 (1418 expanded)
%              Depth                    :   17
%              Number of atoms          :  535 (12723 expanded)
%              Number of equality atoms :  179 (2595 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_191,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & v3_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,C),k6_partfun1(A))
             => r2_relset_1(A,A,C,k2_funct_2(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_131,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_123,axiom,(
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

tff(f_169,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(B) = k1_relat_1(A)
              & k5_relat_1(B,A) = k6_relat_1(k2_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_157,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_147,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_143,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_167,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_27,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_36,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_74,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_78,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_249,plain,(
    ! [A_81,B_82,D_83] :
      ( r2_relset_1(A_81,B_82,D_83,D_83)
      | ~ m1_subset_1(D_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_261,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_249])).

tff(c_115,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_131,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_115])).

tff(c_173,plain,(
    ! [C_59,B_60,A_61] :
      ( v5_relat_1(C_59,B_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_61,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_189,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_173])).

tff(c_263,plain,(
    ! [B_84,A_85] :
      ( k2_relat_1(B_84) = A_85
      | ~ v2_funct_2(B_84,A_85)
      | ~ v5_relat_1(B_84,A_85)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_272,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_189,c_263])).

tff(c_284,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_272])).

tff(c_295,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_284])).

tff(c_560,plain,(
    ! [C_129,B_130,A_131] :
      ( v2_funct_2(C_129,B_130)
      | ~ v3_funct_2(C_129,A_131,B_130)
      | ~ v1_funct_1(C_129)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_131,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_569,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_560])).

tff(c_580,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_569])).

tff(c_582,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_295,c_580])).

tff(c_583,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_284])).

tff(c_810,plain,(
    ! [C_164,A_165,B_166] :
      ( v2_funct_1(C_164)
      | ~ v3_funct_2(C_164,A_165,B_166)
      | ~ v1_funct_1(C_164)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_819,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_810])).

tff(c_830,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_819])).

tff(c_10,plain,(
    ! [A_5] :
      ( k2_relat_1(A_5) != k1_xboole_0
      | k1_xboole_0 = A_5
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_162,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_131,c_10])).

tff(c_172,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_585,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_583,c_172])).

tff(c_76,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_735,plain,(
    ! [A_154,B_155,C_156] :
      ( k1_relset_1(A_154,B_155,C_156) = k1_relat_1(C_156)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_751,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_735])).

tff(c_926,plain,(
    ! [B_184,A_185,C_186] :
      ( k1_xboole_0 = B_184
      | k1_relset_1(A_185,B_184,C_186) = A_185
      | ~ v1_funct_2(C_186,A_185,B_184)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_185,B_184))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_935,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_926])).

tff(c_948,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_751,c_935])).

tff(c_949,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_585,c_948])).

tff(c_86,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_80,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_130,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_115])).

tff(c_188,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_173])).

tff(c_275,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_188,c_263])).

tff(c_287,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_275])).

tff(c_595,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_287])).

tff(c_82,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_713,plain,(
    ! [C_151,B_152,A_153] :
      ( v2_funct_2(C_151,B_152)
      | ~ v3_funct_2(C_151,A_153,B_152)
      | ~ v1_funct_1(C_151)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_153,B_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_719,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_713])).

tff(c_730,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_719])).

tff(c_732,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_595,c_730])).

tff(c_733,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_287])).

tff(c_66,plain,(
    ! [A_46] : k6_relat_1(A_46) = k6_partfun1(A_46) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_18,plain,(
    ! [A_7,B_9] :
      ( k2_funct_1(A_7) = B_9
      | k6_relat_1(k2_relat_1(A_7)) != k5_relat_1(B_9,A_7)
      | k2_relat_1(B_9) != k1_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1049,plain,(
    ! [A_197,B_198] :
      ( k2_funct_1(A_197) = B_198
      | k6_partfun1(k2_relat_1(A_197)) != k5_relat_1(B_198,A_197)
      | k2_relat_1(B_198) != k1_relat_1(A_197)
      | ~ v2_funct_1(A_197)
      | ~ v1_funct_1(B_198)
      | ~ v1_relat_1(B_198)
      | ~ v1_funct_1(A_197)
      | ~ v1_relat_1(A_197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_18])).

tff(c_1057,plain,(
    ! [B_198] :
      ( k2_funct_1('#skF_3') = B_198
      | k5_relat_1(B_198,'#skF_3') != k6_partfun1('#skF_1')
      | k2_relat_1(B_198) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_198)
      | ~ v1_relat_1(B_198)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_583,c_1049])).

tff(c_1347,plain,(
    ! [B_232] :
      ( k2_funct_1('#skF_3') = B_232
      | k5_relat_1(B_232,'#skF_3') != k6_partfun1('#skF_1')
      | k2_relat_1(B_232) != '#skF_1'
      | ~ v1_funct_1(B_232)
      | ~ v1_relat_1(B_232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_78,c_830,c_949,c_1057])).

tff(c_1359,plain,
    ( k2_funct_1('#skF_3') = '#skF_2'
    | k5_relat_1('#skF_2','#skF_3') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_2') != '#skF_1'
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_130,c_1347])).

tff(c_1368,plain,
    ( k2_funct_1('#skF_3') = '#skF_2'
    | k5_relat_1('#skF_2','#skF_3') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_733,c_1359])).

tff(c_1388,plain,(
    k5_relat_1('#skF_2','#skF_3') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1368])).

tff(c_1166,plain,(
    ! [B_211,D_215,E_212,F_213,A_210,C_214] :
      ( k1_partfun1(A_210,B_211,C_214,D_215,E_212,F_213) = k5_relat_1(E_212,F_213)
      | ~ m1_subset_1(F_213,k1_zfmisc_1(k2_zfmisc_1(C_214,D_215)))
      | ~ v1_funct_1(F_213)
      | ~ m1_subset_1(E_212,k1_zfmisc_1(k2_zfmisc_1(A_210,B_211)))
      | ~ v1_funct_1(E_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1172,plain,(
    ! [A_210,B_211,E_212] :
      ( k1_partfun1(A_210,B_211,'#skF_1','#skF_1',E_212,'#skF_3') = k5_relat_1(E_212,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_212,k1_zfmisc_1(k2_zfmisc_1(A_210,B_211)))
      | ~ v1_funct_1(E_212) ) ),
    inference(resolution,[status(thm)],[c_72,c_1166])).

tff(c_1210,plain,(
    ! [A_223,B_224,E_225] :
      ( k1_partfun1(A_223,B_224,'#skF_1','#skF_1',E_225,'#skF_3') = k5_relat_1(E_225,'#skF_3')
      | ~ m1_subset_1(E_225,k1_zfmisc_1(k2_zfmisc_1(A_223,B_224)))
      | ~ v1_funct_1(E_225) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1172])).

tff(c_1216,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_1210])).

tff(c_1227,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1216])).

tff(c_60,plain,(
    ! [A_37] : m1_subset_1(k6_partfun1(A_37),k1_zfmisc_1(k2_zfmisc_1(A_37,A_37))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_70,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_997,plain,(
    ! [D_191,C_192,A_193,B_194] :
      ( D_191 = C_192
      | ~ r2_relset_1(A_193,B_194,C_192,D_191)
      | ~ m1_subset_1(D_191,k1_zfmisc_1(k2_zfmisc_1(A_193,B_194)))
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(A_193,B_194))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1007,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_70,c_997])).

tff(c_1026,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1007])).

tff(c_1077,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1026])).

tff(c_1233,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1227,c_1077])).

tff(c_1239,plain,(
    ! [D_226,A_229,E_228,C_231,B_227,F_230] :
      ( m1_subset_1(k1_partfun1(A_229,B_227,C_231,D_226,E_228,F_230),k1_zfmisc_1(k2_zfmisc_1(A_229,D_226)))
      | ~ m1_subset_1(F_230,k1_zfmisc_1(k2_zfmisc_1(C_231,D_226)))
      | ~ v1_funct_1(F_230)
      | ~ m1_subset_1(E_228,k1_zfmisc_1(k2_zfmisc_1(A_229,B_227)))
      | ~ v1_funct_1(E_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1299,plain,
    ( m1_subset_1(k5_relat_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1227,c_1239])).

tff(c_1320,plain,(
    m1_subset_1(k5_relat_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_80,c_78,c_72,c_1299])).

tff(c_1337,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1233,c_1320])).

tff(c_1338,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1026])).

tff(c_1434,plain,(
    ! [F_247,B_245,A_244,D_249,C_248,E_246] :
      ( k1_partfun1(A_244,B_245,C_248,D_249,E_246,F_247) = k5_relat_1(E_246,F_247)
      | ~ m1_subset_1(F_247,k1_zfmisc_1(k2_zfmisc_1(C_248,D_249)))
      | ~ v1_funct_1(F_247)
      | ~ m1_subset_1(E_246,k1_zfmisc_1(k2_zfmisc_1(A_244,B_245)))
      | ~ v1_funct_1(E_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1440,plain,(
    ! [A_244,B_245,E_246] :
      ( k1_partfun1(A_244,B_245,'#skF_1','#skF_1',E_246,'#skF_3') = k5_relat_1(E_246,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_246,k1_zfmisc_1(k2_zfmisc_1(A_244,B_245)))
      | ~ v1_funct_1(E_246) ) ),
    inference(resolution,[status(thm)],[c_72,c_1434])).

tff(c_1566,plain,(
    ! [A_262,B_263,E_264] :
      ( k1_partfun1(A_262,B_263,'#skF_1','#skF_1',E_264,'#skF_3') = k5_relat_1(E_264,'#skF_3')
      | ~ m1_subset_1(E_264,k1_zfmisc_1(k2_zfmisc_1(A_262,B_263)))
      | ~ v1_funct_1(E_264) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1440])).

tff(c_1575,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_1566])).

tff(c_1587,plain,(
    k5_relat_1('#skF_2','#skF_3') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1338,c_1575])).

tff(c_1589,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1388,c_1587])).

tff(c_1590,plain,(
    k2_funct_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1368])).

tff(c_16,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k2_funct_1(A_6)) = k6_relat_1(k1_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_88,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k2_funct_1(A_6)) = k6_partfun1(k1_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_16])).

tff(c_1600,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = k5_relat_1('#skF_3','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1590,c_88])).

tff(c_1606,plain,(
    k5_relat_1('#skF_3','#skF_2') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_78,c_830,c_949,c_1600])).

tff(c_816,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_810])).

tff(c_827,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_816])).

tff(c_84,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_750,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_735])).

tff(c_932,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_926])).

tff(c_944,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_750,c_932])).

tff(c_945,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_585,c_944])).

tff(c_1055,plain,(
    ! [B_198] :
      ( k2_funct_1('#skF_2') = B_198
      | k5_relat_1(B_198,'#skF_2') != k6_partfun1('#skF_1')
      | k2_relat_1(B_198) != k1_relat_1('#skF_2')
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1(B_198)
      | ~ v1_relat_1(B_198)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_733,c_1049])).

tff(c_1662,plain,(
    ! [B_272] :
      ( k2_funct_1('#skF_2') = B_272
      | k5_relat_1(B_272,'#skF_2') != k6_partfun1('#skF_1')
      | k2_relat_1(B_272) != '#skF_1'
      | ~ v1_funct_1(B_272)
      | ~ v1_relat_1(B_272) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_86,c_827,c_945,c_1055])).

tff(c_1668,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_2') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_1'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_131,c_1662])).

tff(c_1678,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_583,c_1606,c_1668])).

tff(c_1027,plain,(
    ! [A_195,B_196] :
      ( k2_funct_2(A_195,B_196) = k2_funct_1(B_196)
      | ~ m1_subset_1(B_196,k1_zfmisc_1(k2_zfmisc_1(A_195,A_195)))
      | ~ v3_funct_2(B_196,A_195,A_195)
      | ~ v1_funct_2(B_196,A_195,A_195)
      | ~ v1_funct_1(B_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_1033,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_1027])).

tff(c_1044,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_1033])).

tff(c_68,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_1068,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1044,c_68])).

tff(c_1685,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1678,c_1068])).

tff(c_1689,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_1685])).

tff(c_1690,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_2,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1741,plain,(
    ! [A_1] : m1_subset_1('#skF_3',k1_zfmisc_1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1690,c_2])).

tff(c_2426,plain,(
    ! [C_397,B_398,A_399] :
      ( v2_funct_2(C_397,B_398)
      | ~ v3_funct_2(C_397,A_399,B_398)
      | ~ v1_funct_1(C_397)
      | ~ m1_subset_1(C_397,k1_zfmisc_1(k2_zfmisc_1(A_399,B_398))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2430,plain,(
    ! [B_398,A_399] :
      ( v2_funct_2('#skF_3',B_398)
      | ~ v3_funct_2('#skF_3',A_399,B_398)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1741,c_2426])).

tff(c_2438,plain,(
    ! [B_400,A_401] :
      ( v2_funct_2('#skF_3',B_400)
      | ~ v3_funct_2('#skF_3',A_401,B_400) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2430])).

tff(c_2442,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_2438])).

tff(c_1691,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_1758,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1690,c_1691])).

tff(c_2250,plain,(
    ! [A_361] : m1_subset_1('#skF_3',k1_zfmisc_1(A_361)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1690,c_2])).

tff(c_22,plain,(
    ! [C_15,B_14,A_13] :
      ( v5_relat_1(C_15,B_14)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2266,plain,(
    ! [B_14] : v5_relat_1('#skF_3',B_14) ),
    inference(resolution,[status(thm)],[c_2250,c_22])).

tff(c_2320,plain,(
    ! [B_373,A_374] :
      ( k2_relat_1(B_373) = A_374
      | ~ v2_funct_2(B_373,A_374)
      | ~ v5_relat_1(B_373,A_374)
      | ~ v1_relat_1(B_373) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2323,plain,(
    ! [B_14] :
      ( k2_relat_1('#skF_3') = B_14
      | ~ v2_funct_2('#skF_3',B_14)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2266,c_2320])).

tff(c_2329,plain,(
    ! [B_14] :
      ( B_14 = '#skF_3'
      | ~ v2_funct_2('#skF_3',B_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_1758,c_2323])).

tff(c_2446,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2442,c_2329])).

tff(c_2339,plain,(
    ! [A_376,B_377,D_378] :
      ( r2_relset_1(A_376,B_377,D_378,D_378)
      | ~ m1_subset_1(D_378,k1_zfmisc_1(k2_zfmisc_1(A_376,B_377))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2345,plain,(
    ! [A_376,B_377] : r2_relset_1(A_376,B_377,'#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_1741,c_2339])).

tff(c_2453,plain,(
    ! [A_376,B_377] : r2_relset_1(A_376,B_377,'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2446,c_2446,c_2345])).

tff(c_2473,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2446,c_78])).

tff(c_2466,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2446,c_2446,c_1758])).

tff(c_2470,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2446,c_131])).

tff(c_2395,plain,(
    ! [C_391,A_392,B_393] :
      ( v2_funct_1(C_391)
      | ~ v3_funct_2(C_391,A_392,B_393)
      | ~ v1_funct_1(C_391)
      | ~ m1_subset_1(C_391,k1_zfmisc_1(k2_zfmisc_1(A_392,B_393))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2399,plain,(
    ! [A_392,B_393] :
      ( v2_funct_1('#skF_3')
      | ~ v3_funct_2('#skF_3',A_392,B_393)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1741,c_2395])).

tff(c_2405,plain,(
    ! [A_392,B_393] :
      ( v2_funct_1('#skF_3')
      | ~ v3_funct_2('#skF_3',A_392,B_393) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2399])).

tff(c_2407,plain,(
    ! [A_392,B_393] : ~ v3_funct_2('#skF_3',A_392,B_393) ),
    inference(splitLeft,[status(thm)],[c_2405])).

tff(c_2409,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2407,c_74])).

tff(c_2410,plain,(
    v2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2405])).

tff(c_2450,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2446,c_2410])).

tff(c_8,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1699,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1690,c_1690,c_8])).

tff(c_12,plain,(
    ! [A_5] :
      ( k1_relat_1(A_5) != k1_xboole_0
      | k1_xboole_0 = A_5
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_161,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_131,c_12])).

tff(c_1692,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_161])).

tff(c_1716,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1699,c_1690,c_1692])).

tff(c_1718,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_1753,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1690,c_1718])).

tff(c_2467,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2446,c_2446,c_1753])).

tff(c_2982,plain,(
    ! [A_507,B_508] :
      ( k2_funct_1(A_507) = B_508
      | k6_partfun1(k2_relat_1(A_507)) != k5_relat_1(B_508,A_507)
      | k2_relat_1(B_508) != k1_relat_1(A_507)
      | ~ v2_funct_1(A_507)
      | ~ v1_funct_1(B_508)
      | ~ v1_relat_1(B_508)
      | ~ v1_funct_1(A_507)
      | ~ v1_relat_1(A_507) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_18])).

tff(c_2984,plain,(
    ! [B_508] :
      ( k2_funct_1('#skF_1') = B_508
      | k5_relat_1(B_508,'#skF_1') != k6_partfun1('#skF_1')
      | k2_relat_1(B_508) != k1_relat_1('#skF_1')
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1(B_508)
      | ~ v1_relat_1(B_508)
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2466,c_2982])).

tff(c_2998,plain,(
    ! [B_509] :
      ( k2_funct_1('#skF_1') = B_509
      | k5_relat_1(B_509,'#skF_1') != k6_partfun1('#skF_1')
      | k2_relat_1(B_509) != '#skF_1'
      | ~ v1_funct_1(B_509)
      | ~ v1_relat_1(B_509) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2470,c_2473,c_2450,c_2467,c_2984])).

tff(c_3001,plain,
    ( k2_funct_1('#skF_1') = '#skF_1'
    | k5_relat_1('#skF_1','#skF_1') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_1') != '#skF_1'
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2470,c_2998])).

tff(c_3007,plain,
    ( k2_funct_1('#skF_1') = '#skF_1'
    | k5_relat_1('#skF_1','#skF_1') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2473,c_2466,c_3001])).

tff(c_3009,plain,(
    k5_relat_1('#skF_1','#skF_1') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3007])).

tff(c_2464,plain,(
    ! [A_1] : m1_subset_1('#skF_1',k1_zfmisc_1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2446,c_1741])).

tff(c_3032,plain,(
    ! [D_528,E_525,A_523,C_527,B_524,F_526] :
      ( k1_partfun1(A_523,B_524,C_527,D_528,E_525,F_526) = k5_relat_1(E_525,F_526)
      | ~ m1_subset_1(F_526,k1_zfmisc_1(k2_zfmisc_1(C_527,D_528)))
      | ~ v1_funct_1(F_526)
      | ~ m1_subset_1(E_525,k1_zfmisc_1(k2_zfmisc_1(A_523,B_524)))
      | ~ v1_funct_1(E_525) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_3035,plain,(
    ! [D_528,E_525,A_523,C_527,B_524] :
      ( k1_partfun1(A_523,B_524,C_527,D_528,E_525,'#skF_1') = k5_relat_1(E_525,'#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ m1_subset_1(E_525,k1_zfmisc_1(k2_zfmisc_1(A_523,B_524)))
      | ~ v1_funct_1(E_525) ) ),
    inference(resolution,[status(thm)],[c_2464,c_3032])).

tff(c_3051,plain,(
    ! [A_540,C_536,D_537,E_538,B_539] :
      ( k1_partfun1(A_540,B_539,C_536,D_537,E_538,'#skF_1') = k5_relat_1(E_538,'#skF_1')
      | ~ m1_subset_1(E_538,k1_zfmisc_1(k2_zfmisc_1(A_540,B_539)))
      | ~ v1_funct_1(E_538) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2473,c_3035])).

tff(c_3054,plain,(
    ! [A_540,B_539,C_536,D_537] :
      ( k1_partfun1(A_540,B_539,C_536,D_537,'#skF_1','#skF_1') = k5_relat_1('#skF_1','#skF_1')
      | ~ v1_funct_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_2464,c_3051])).

tff(c_3062,plain,(
    ! [A_541,B_542,C_543,D_544] : k1_partfun1(A_541,B_542,C_543,D_544,'#skF_1','#skF_1') = k5_relat_1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2473,c_3054])).

tff(c_2845,plain,(
    ! [A_494,E_493,B_492,D_491,F_495,C_496] :
      ( m1_subset_1(k1_partfun1(A_494,B_492,C_496,D_491,E_493,F_495),k1_zfmisc_1(k2_zfmisc_1(A_494,D_491)))
      | ~ m1_subset_1(F_495,k1_zfmisc_1(k2_zfmisc_1(C_496,D_491)))
      | ~ v1_funct_1(F_495)
      | ~ m1_subset_1(E_493,k1_zfmisc_1(k2_zfmisc_1(A_494,B_492)))
      | ~ v1_funct_1(E_493) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1765,plain,(
    ! [C_277,B_278,A_279] :
      ( v5_relat_1(C_277,B_278)
      | ~ m1_subset_1(C_277,k1_zfmisc_1(k2_zfmisc_1(A_279,B_278))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1776,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_1765])).

tff(c_1869,plain,(
    ! [B_298,A_299] :
      ( k2_relat_1(B_298) = A_299
      | ~ v2_funct_2(B_298,A_299)
      | ~ v5_relat_1(B_298,A_299)
      | ~ v1_relat_1(B_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1878,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1776,c_1869])).

tff(c_1887,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_1878])).

tff(c_1888,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1887])).

tff(c_2014,plain,(
    ! [C_324,B_325,A_326] :
      ( v2_funct_2(C_324,B_325)
      | ~ v3_funct_2(C_324,A_326,B_325)
      | ~ v1_funct_1(C_324)
      | ~ m1_subset_1(C_324,k1_zfmisc_1(k2_zfmisc_1(A_326,B_325))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2024,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_2014])).

tff(c_2031,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_2024])).

tff(c_2033,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1888,c_2031])).

tff(c_2034,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1887])).

tff(c_140,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_130,c_10])).

tff(c_1803,plain,
    ( k2_relat_1('#skF_2') != '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1690,c_1690,c_140])).

tff(c_1804,plain,(
    k2_relat_1('#skF_2') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1803])).

tff(c_2036,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2034,c_1804])).

tff(c_2173,plain,(
    ! [C_352,B_353,A_354] :
      ( v2_funct_2(C_352,B_353)
      | ~ v3_funct_2(C_352,A_354,B_353)
      | ~ v1_funct_1(C_352)
      | ~ m1_subset_1(C_352,k1_zfmisc_1(k2_zfmisc_1(A_354,B_353))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2177,plain,(
    ! [B_353,A_354] :
      ( v2_funct_2('#skF_3',B_353)
      | ~ v3_funct_2('#skF_3',A_354,B_353)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1741,c_2173])).

tff(c_2191,plain,(
    ! [B_355,A_356] :
      ( v2_funct_2('#skF_3',B_355)
      | ~ v3_funct_2('#skF_3',A_356,B_355) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2177])).

tff(c_2195,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_2191])).

tff(c_1783,plain,(
    ! [A_282] : m1_subset_1('#skF_3',k1_zfmisc_1(A_282)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1690,c_2])).

tff(c_1796,plain,(
    ! [B_14] : v5_relat_1('#skF_3',B_14) ),
    inference(resolution,[status(thm)],[c_1783,c_22])).

tff(c_1872,plain,(
    ! [B_14] :
      ( k2_relat_1('#skF_3') = B_14
      | ~ v2_funct_2('#skF_3',B_14)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1796,c_1869])).

tff(c_1881,plain,(
    ! [B_14] :
      ( B_14 = '#skF_3'
      | ~ v2_funct_2('#skF_3',B_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_1758,c_1872])).

tff(c_2198,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2195,c_1881])).

tff(c_2202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2036,c_2198])).

tff(c_2203,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1803])).

tff(c_139,plain,
    ( k1_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_130,c_12])).

tff(c_1779,plain,
    ( k1_relat_1('#skF_2') != '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1690,c_1690,c_139])).

tff(c_1780,plain,(
    k1_relat_1('#skF_2') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1779])).

tff(c_2205,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2203,c_1780])).

tff(c_2217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1753,c_2205])).

tff(c_2218,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1779])).

tff(c_2223,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2218,c_70])).

tff(c_2452,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2446,c_2446,c_2223])).

tff(c_2677,plain,(
    ! [D_433,C_434,A_435,B_436] :
      ( D_433 = C_434
      | ~ r2_relset_1(A_435,B_436,C_434,D_433)
      | ~ m1_subset_1(D_433,k1_zfmisc_1(k2_zfmisc_1(A_435,B_436)))
      | ~ m1_subset_1(C_434,k1_zfmisc_1(k2_zfmisc_1(A_435,B_436))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2679,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2452,c_2677])).

tff(c_2686,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2679])).

tff(c_2702,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2686])).

tff(c_2870,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2845,c_2702])).

tff(c_2914,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2473,c_2464,c_2870])).

tff(c_2915,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2686])).

tff(c_3066,plain,(
    k5_relat_1('#skF_1','#skF_1') = k6_partfun1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3062,c_2915])).

tff(c_3073,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3009,c_3066])).

tff(c_3074,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3007])).

tff(c_2350,plain,(
    ! [A_383,B_384,C_385] :
      ( k1_relset_1(A_383,B_384,C_385) = k1_relat_1(C_385)
      | ~ m1_subset_1(C_385,k1_zfmisc_1(k2_zfmisc_1(A_383,B_384))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2354,plain,(
    ! [A_383,B_384] : k1_relset_1(A_383,B_384,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1741,c_2350])).

tff(c_2359,plain,(
    ! [A_383,B_384] : k1_relset_1(A_383,B_384,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1753,c_2354])).

tff(c_2451,plain,(
    ! [A_383,B_384] : k1_relset_1(A_383,B_384,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2446,c_2446,c_2359])).

tff(c_2469,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2446,c_1690])).

tff(c_42,plain,(
    ! [C_28,B_27] :
      ( v1_funct_2(C_28,k1_xboole_0,B_27)
      | k1_relset_1(k1_xboole_0,B_27,C_28) != k1_xboole_0
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2941,plain,(
    ! [C_501,B_502] :
      ( v1_funct_2(C_501,'#skF_1',B_502)
      | k1_relset_1('#skF_1',B_502,C_501) != '#skF_1'
      | ~ m1_subset_1(C_501,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_502))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2469,c_2469,c_2469,c_2469,c_42])).

tff(c_2945,plain,(
    ! [B_502] :
      ( v1_funct_2('#skF_1','#skF_1',B_502)
      | k1_relset_1('#skF_1',B_502,'#skF_1') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_2464,c_2941])).

tff(c_2952,plain,(
    ! [B_502] : v1_funct_2('#skF_1','#skF_1',B_502) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2451,c_2945])).

tff(c_2472,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2446,c_74])).

tff(c_2963,plain,(
    ! [A_504,B_505] :
      ( k2_funct_2(A_504,B_505) = k2_funct_1(B_505)
      | ~ m1_subset_1(B_505,k1_zfmisc_1(k2_zfmisc_1(A_504,A_504)))
      | ~ v3_funct_2(B_505,A_504,A_504)
      | ~ v1_funct_2(B_505,A_504,A_504)
      | ~ v1_funct_1(B_505) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_2967,plain,(
    ! [A_504] :
      ( k2_funct_2(A_504,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_504,A_504)
      | ~ v1_funct_2('#skF_1',A_504,A_504)
      | ~ v1_funct_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_2464,c_2963])).

tff(c_2975,plain,(
    ! [A_506] :
      ( k2_funct_2(A_506,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_506,A_506)
      | ~ v1_funct_2('#skF_1',A_506,A_506) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2473,c_2967])).

tff(c_2978,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_2472,c_2975])).

tff(c_2981,plain,(
    k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2952,c_2978])).

tff(c_2224,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2218,c_68])).

tff(c_2462,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2446,c_2446,c_2224])).

tff(c_2993,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2981,c_2462])).

tff(c_3077,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3074,c_2993])).

tff(c_3082,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2453,c_3077])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:22:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.57/2.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.75/2.11  
% 5.75/2.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.75/2.11  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.75/2.11  
% 5.75/2.11  %Foreground sorts:
% 5.75/2.11  
% 5.75/2.11  
% 5.75/2.11  %Background operators:
% 5.75/2.11  
% 5.75/2.11  
% 5.75/2.11  %Foreground operators:
% 5.75/2.11  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.75/2.11  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.75/2.11  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.75/2.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.75/2.11  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.75/2.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.75/2.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.75/2.11  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.75/2.11  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.75/2.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.75/2.11  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.75/2.11  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.75/2.11  tff('#skF_2', type, '#skF_2': $i).
% 5.75/2.11  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.75/2.11  tff('#skF_3', type, '#skF_3': $i).
% 5.75/2.11  tff('#skF_1', type, '#skF_1': $i).
% 5.75/2.11  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.75/2.11  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.75/2.11  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.75/2.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.75/2.11  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.75/2.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.75/2.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.75/2.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.75/2.11  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.75/2.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.75/2.11  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.75/2.11  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.75/2.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.75/2.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.75/2.11  
% 5.89/2.15  tff(f_191, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_2)).
% 5.89/2.15  tff(f_93, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.89/2.15  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.89/2.15  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.89/2.15  tff(f_131, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 5.89/2.15  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.89/2.15  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 5.89/2.15  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.89/2.15  tff(f_123, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.89/2.15  tff(f_169, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.89/2.15  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 5.89/2.15  tff(f_157, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.89/2.15  tff(f_147, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.89/2.15  tff(f_143, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.89/2.15  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 5.89/2.15  tff(f_167, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.89/2.15  tff(f_27, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.89/2.15  tff(f_36, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 5.89/2.15  tff(c_74, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.89/2.15  tff(c_78, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.89/2.15  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.89/2.15  tff(c_249, plain, (![A_81, B_82, D_83]: (r2_relset_1(A_81, B_82, D_83, D_83) | ~m1_subset_1(D_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.89/2.15  tff(c_261, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_72, c_249])).
% 5.89/2.15  tff(c_115, plain, (![C_55, A_56, B_57]: (v1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.89/2.15  tff(c_131, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_115])).
% 5.89/2.15  tff(c_173, plain, (![C_59, B_60, A_61]: (v5_relat_1(C_59, B_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_61, B_60))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.89/2.15  tff(c_189, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_173])).
% 5.89/2.15  tff(c_263, plain, (![B_84, A_85]: (k2_relat_1(B_84)=A_85 | ~v2_funct_2(B_84, A_85) | ~v5_relat_1(B_84, A_85) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.89/2.15  tff(c_272, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_189, c_263])).
% 5.89/2.15  tff(c_284, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_272])).
% 5.89/2.15  tff(c_295, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_284])).
% 5.89/2.15  tff(c_560, plain, (![C_129, B_130, A_131]: (v2_funct_2(C_129, B_130) | ~v3_funct_2(C_129, A_131, B_130) | ~v1_funct_1(C_129) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_131, B_130))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.89/2.15  tff(c_569, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_560])).
% 5.89/2.15  tff(c_580, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_569])).
% 5.89/2.15  tff(c_582, plain, $false, inference(negUnitSimplification, [status(thm)], [c_295, c_580])).
% 5.89/2.15  tff(c_583, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_284])).
% 5.89/2.15  tff(c_810, plain, (![C_164, A_165, B_166]: (v2_funct_1(C_164) | ~v3_funct_2(C_164, A_165, B_166) | ~v1_funct_1(C_164) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.89/2.15  tff(c_819, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_810])).
% 5.89/2.15  tff(c_830, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_819])).
% 5.89/2.15  tff(c_10, plain, (![A_5]: (k2_relat_1(A_5)!=k1_xboole_0 | k1_xboole_0=A_5 | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.89/2.15  tff(c_162, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_131, c_10])).
% 5.89/2.15  tff(c_172, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_162])).
% 5.89/2.15  tff(c_585, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_583, c_172])).
% 5.89/2.15  tff(c_76, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.89/2.15  tff(c_735, plain, (![A_154, B_155, C_156]: (k1_relset_1(A_154, B_155, C_156)=k1_relat_1(C_156) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.89/2.15  tff(c_751, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_735])).
% 5.89/2.15  tff(c_926, plain, (![B_184, A_185, C_186]: (k1_xboole_0=B_184 | k1_relset_1(A_185, B_184, C_186)=A_185 | ~v1_funct_2(C_186, A_185, B_184) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_185, B_184))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.89/2.15  tff(c_935, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_926])).
% 5.89/2.15  tff(c_948, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_751, c_935])).
% 5.89/2.15  tff(c_949, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_585, c_948])).
% 5.89/2.15  tff(c_86, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.89/2.15  tff(c_80, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.89/2.15  tff(c_130, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_115])).
% 5.89/2.15  tff(c_188, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_80, c_173])).
% 5.89/2.15  tff(c_275, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_188, c_263])).
% 5.89/2.15  tff(c_287, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_275])).
% 5.89/2.15  tff(c_595, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_287])).
% 5.89/2.15  tff(c_82, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.89/2.15  tff(c_713, plain, (![C_151, B_152, A_153]: (v2_funct_2(C_151, B_152) | ~v3_funct_2(C_151, A_153, B_152) | ~v1_funct_1(C_151) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_153, B_152))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.89/2.15  tff(c_719, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_713])).
% 5.89/2.15  tff(c_730, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_719])).
% 5.89/2.15  tff(c_732, plain, $false, inference(negUnitSimplification, [status(thm)], [c_595, c_730])).
% 5.89/2.15  tff(c_733, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_287])).
% 5.89/2.15  tff(c_66, plain, (![A_46]: (k6_relat_1(A_46)=k6_partfun1(A_46))), inference(cnfTransformation, [status(thm)], [f_169])).
% 5.89/2.15  tff(c_18, plain, (![A_7, B_9]: (k2_funct_1(A_7)=B_9 | k6_relat_1(k2_relat_1(A_7))!=k5_relat_1(B_9, A_7) | k2_relat_1(B_9)!=k1_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.89/2.15  tff(c_1049, plain, (![A_197, B_198]: (k2_funct_1(A_197)=B_198 | k6_partfun1(k2_relat_1(A_197))!=k5_relat_1(B_198, A_197) | k2_relat_1(B_198)!=k1_relat_1(A_197) | ~v2_funct_1(A_197) | ~v1_funct_1(B_198) | ~v1_relat_1(B_198) | ~v1_funct_1(A_197) | ~v1_relat_1(A_197))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_18])).
% 5.89/2.15  tff(c_1057, plain, (![B_198]: (k2_funct_1('#skF_3')=B_198 | k5_relat_1(B_198, '#skF_3')!=k6_partfun1('#skF_1') | k2_relat_1(B_198)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_198) | ~v1_relat_1(B_198) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_583, c_1049])).
% 5.89/2.15  tff(c_1347, plain, (![B_232]: (k2_funct_1('#skF_3')=B_232 | k5_relat_1(B_232, '#skF_3')!=k6_partfun1('#skF_1') | k2_relat_1(B_232)!='#skF_1' | ~v1_funct_1(B_232) | ~v1_relat_1(B_232))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_78, c_830, c_949, c_1057])).
% 5.89/2.15  tff(c_1359, plain, (k2_funct_1('#skF_3')='#skF_2' | k5_relat_1('#skF_2', '#skF_3')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_2')!='#skF_1' | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_130, c_1347])).
% 5.89/2.15  tff(c_1368, plain, (k2_funct_1('#skF_3')='#skF_2' | k5_relat_1('#skF_2', '#skF_3')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_733, c_1359])).
% 5.89/2.15  tff(c_1388, plain, (k5_relat_1('#skF_2', '#skF_3')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_1368])).
% 5.89/2.15  tff(c_1166, plain, (![B_211, D_215, E_212, F_213, A_210, C_214]: (k1_partfun1(A_210, B_211, C_214, D_215, E_212, F_213)=k5_relat_1(E_212, F_213) | ~m1_subset_1(F_213, k1_zfmisc_1(k2_zfmisc_1(C_214, D_215))) | ~v1_funct_1(F_213) | ~m1_subset_1(E_212, k1_zfmisc_1(k2_zfmisc_1(A_210, B_211))) | ~v1_funct_1(E_212))), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.89/2.15  tff(c_1172, plain, (![A_210, B_211, E_212]: (k1_partfun1(A_210, B_211, '#skF_1', '#skF_1', E_212, '#skF_3')=k5_relat_1(E_212, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_212, k1_zfmisc_1(k2_zfmisc_1(A_210, B_211))) | ~v1_funct_1(E_212))), inference(resolution, [status(thm)], [c_72, c_1166])).
% 5.89/2.15  tff(c_1210, plain, (![A_223, B_224, E_225]: (k1_partfun1(A_223, B_224, '#skF_1', '#skF_1', E_225, '#skF_3')=k5_relat_1(E_225, '#skF_3') | ~m1_subset_1(E_225, k1_zfmisc_1(k2_zfmisc_1(A_223, B_224))) | ~v1_funct_1(E_225))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1172])).
% 5.89/2.15  tff(c_1216, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_1210])).
% 5.89/2.15  tff(c_1227, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1216])).
% 5.89/2.15  tff(c_60, plain, (![A_37]: (m1_subset_1(k6_partfun1(A_37), k1_zfmisc_1(k2_zfmisc_1(A_37, A_37))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.89/2.15  tff(c_70, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.89/2.15  tff(c_997, plain, (![D_191, C_192, A_193, B_194]: (D_191=C_192 | ~r2_relset_1(A_193, B_194, C_192, D_191) | ~m1_subset_1(D_191, k1_zfmisc_1(k2_zfmisc_1(A_193, B_194))) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(A_193, B_194))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.89/2.15  tff(c_1007, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_70, c_997])).
% 5.89/2.15  tff(c_1026, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1007])).
% 5.89/2.15  tff(c_1077, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1026])).
% 5.89/2.15  tff(c_1233, plain, (~m1_subset_1(k5_relat_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1227, c_1077])).
% 5.89/2.15  tff(c_1239, plain, (![D_226, A_229, E_228, C_231, B_227, F_230]: (m1_subset_1(k1_partfun1(A_229, B_227, C_231, D_226, E_228, F_230), k1_zfmisc_1(k2_zfmisc_1(A_229, D_226))) | ~m1_subset_1(F_230, k1_zfmisc_1(k2_zfmisc_1(C_231, D_226))) | ~v1_funct_1(F_230) | ~m1_subset_1(E_228, k1_zfmisc_1(k2_zfmisc_1(A_229, B_227))) | ~v1_funct_1(E_228))), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.89/2.15  tff(c_1299, plain, (m1_subset_1(k5_relat_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1227, c_1239])).
% 5.89/2.15  tff(c_1320, plain, (m1_subset_1(k5_relat_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_80, c_78, c_72, c_1299])).
% 5.89/2.15  tff(c_1337, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1233, c_1320])).
% 5.89/2.15  tff(c_1338, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1026])).
% 5.89/2.15  tff(c_1434, plain, (![F_247, B_245, A_244, D_249, C_248, E_246]: (k1_partfun1(A_244, B_245, C_248, D_249, E_246, F_247)=k5_relat_1(E_246, F_247) | ~m1_subset_1(F_247, k1_zfmisc_1(k2_zfmisc_1(C_248, D_249))) | ~v1_funct_1(F_247) | ~m1_subset_1(E_246, k1_zfmisc_1(k2_zfmisc_1(A_244, B_245))) | ~v1_funct_1(E_246))), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.89/2.15  tff(c_1440, plain, (![A_244, B_245, E_246]: (k1_partfun1(A_244, B_245, '#skF_1', '#skF_1', E_246, '#skF_3')=k5_relat_1(E_246, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_246, k1_zfmisc_1(k2_zfmisc_1(A_244, B_245))) | ~v1_funct_1(E_246))), inference(resolution, [status(thm)], [c_72, c_1434])).
% 5.89/2.15  tff(c_1566, plain, (![A_262, B_263, E_264]: (k1_partfun1(A_262, B_263, '#skF_1', '#skF_1', E_264, '#skF_3')=k5_relat_1(E_264, '#skF_3') | ~m1_subset_1(E_264, k1_zfmisc_1(k2_zfmisc_1(A_262, B_263))) | ~v1_funct_1(E_264))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1440])).
% 5.89/2.15  tff(c_1575, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_1566])).
% 5.89/2.15  tff(c_1587, plain, (k5_relat_1('#skF_2', '#skF_3')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1338, c_1575])).
% 5.89/2.15  tff(c_1589, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1388, c_1587])).
% 5.89/2.15  tff(c_1590, plain, (k2_funct_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_1368])).
% 5.89/2.15  tff(c_16, plain, (![A_6]: (k5_relat_1(A_6, k2_funct_1(A_6))=k6_relat_1(k1_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.89/2.15  tff(c_88, plain, (![A_6]: (k5_relat_1(A_6, k2_funct_1(A_6))=k6_partfun1(k1_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_16])).
% 5.89/2.15  tff(c_1600, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k5_relat_1('#skF_3', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1590, c_88])).
% 5.89/2.15  tff(c_1606, plain, (k5_relat_1('#skF_3', '#skF_2')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_78, c_830, c_949, c_1600])).
% 5.89/2.15  tff(c_816, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_810])).
% 5.89/2.15  tff(c_827, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_816])).
% 5.89/2.15  tff(c_84, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.89/2.15  tff(c_750, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_735])).
% 5.89/2.15  tff(c_932, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_80, c_926])).
% 5.89/2.15  tff(c_944, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_750, c_932])).
% 5.89/2.15  tff(c_945, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_585, c_944])).
% 5.89/2.15  tff(c_1055, plain, (![B_198]: (k2_funct_1('#skF_2')=B_198 | k5_relat_1(B_198, '#skF_2')!=k6_partfun1('#skF_1') | k2_relat_1(B_198)!=k1_relat_1('#skF_2') | ~v2_funct_1('#skF_2') | ~v1_funct_1(B_198) | ~v1_relat_1(B_198) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_733, c_1049])).
% 5.89/2.15  tff(c_1662, plain, (![B_272]: (k2_funct_1('#skF_2')=B_272 | k5_relat_1(B_272, '#skF_2')!=k6_partfun1('#skF_1') | k2_relat_1(B_272)!='#skF_1' | ~v1_funct_1(B_272) | ~v1_relat_1(B_272))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_86, c_827, c_945, c_1055])).
% 5.89/2.15  tff(c_1668, plain, (k2_funct_1('#skF_2')='#skF_3' | k5_relat_1('#skF_3', '#skF_2')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_1' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_131, c_1662])).
% 5.89/2.15  tff(c_1678, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_583, c_1606, c_1668])).
% 5.89/2.15  tff(c_1027, plain, (![A_195, B_196]: (k2_funct_2(A_195, B_196)=k2_funct_1(B_196) | ~m1_subset_1(B_196, k1_zfmisc_1(k2_zfmisc_1(A_195, A_195))) | ~v3_funct_2(B_196, A_195, A_195) | ~v1_funct_2(B_196, A_195, A_195) | ~v1_funct_1(B_196))), inference(cnfTransformation, [status(thm)], [f_167])).
% 5.89/2.15  tff(c_1033, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_1027])).
% 5.89/2.15  tff(c_1044, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_1033])).
% 5.89/2.15  tff(c_68, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.89/2.15  tff(c_1068, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1044, c_68])).
% 5.89/2.15  tff(c_1685, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1678, c_1068])).
% 5.89/2.15  tff(c_1689, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_261, c_1685])).
% 5.89/2.15  tff(c_1690, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_162])).
% 5.89/2.15  tff(c_2, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.89/2.15  tff(c_1741, plain, (![A_1]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_1690, c_2])).
% 5.89/2.15  tff(c_2426, plain, (![C_397, B_398, A_399]: (v2_funct_2(C_397, B_398) | ~v3_funct_2(C_397, A_399, B_398) | ~v1_funct_1(C_397) | ~m1_subset_1(C_397, k1_zfmisc_1(k2_zfmisc_1(A_399, B_398))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.89/2.15  tff(c_2430, plain, (![B_398, A_399]: (v2_funct_2('#skF_3', B_398) | ~v3_funct_2('#skF_3', A_399, B_398) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1741, c_2426])).
% 5.89/2.15  tff(c_2438, plain, (![B_400, A_401]: (v2_funct_2('#skF_3', B_400) | ~v3_funct_2('#skF_3', A_401, B_400))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2430])).
% 5.89/2.15  tff(c_2442, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_74, c_2438])).
% 5.89/2.15  tff(c_1691, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_162])).
% 5.89/2.15  tff(c_1758, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1690, c_1691])).
% 5.89/2.15  tff(c_2250, plain, (![A_361]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_361)))), inference(demodulation, [status(thm), theory('equality')], [c_1690, c_2])).
% 5.89/2.15  tff(c_22, plain, (![C_15, B_14, A_13]: (v5_relat_1(C_15, B_14) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.89/2.15  tff(c_2266, plain, (![B_14]: (v5_relat_1('#skF_3', B_14))), inference(resolution, [status(thm)], [c_2250, c_22])).
% 5.89/2.15  tff(c_2320, plain, (![B_373, A_374]: (k2_relat_1(B_373)=A_374 | ~v2_funct_2(B_373, A_374) | ~v5_relat_1(B_373, A_374) | ~v1_relat_1(B_373))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.89/2.15  tff(c_2323, plain, (![B_14]: (k2_relat_1('#skF_3')=B_14 | ~v2_funct_2('#skF_3', B_14) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_2266, c_2320])).
% 5.89/2.15  tff(c_2329, plain, (![B_14]: (B_14='#skF_3' | ~v2_funct_2('#skF_3', B_14))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_1758, c_2323])).
% 5.89/2.15  tff(c_2446, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_2442, c_2329])).
% 5.89/2.15  tff(c_2339, plain, (![A_376, B_377, D_378]: (r2_relset_1(A_376, B_377, D_378, D_378) | ~m1_subset_1(D_378, k1_zfmisc_1(k2_zfmisc_1(A_376, B_377))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.89/2.15  tff(c_2345, plain, (![A_376, B_377]: (r2_relset_1(A_376, B_377, '#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_1741, c_2339])).
% 5.89/2.15  tff(c_2453, plain, (![A_376, B_377]: (r2_relset_1(A_376, B_377, '#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2446, c_2446, c_2345])).
% 5.89/2.15  tff(c_2473, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2446, c_78])).
% 5.89/2.15  tff(c_2466, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2446, c_2446, c_1758])).
% 5.89/2.15  tff(c_2470, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2446, c_131])).
% 5.89/2.15  tff(c_2395, plain, (![C_391, A_392, B_393]: (v2_funct_1(C_391) | ~v3_funct_2(C_391, A_392, B_393) | ~v1_funct_1(C_391) | ~m1_subset_1(C_391, k1_zfmisc_1(k2_zfmisc_1(A_392, B_393))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.89/2.15  tff(c_2399, plain, (![A_392, B_393]: (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', A_392, B_393) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1741, c_2395])).
% 5.89/2.15  tff(c_2405, plain, (![A_392, B_393]: (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', A_392, B_393))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2399])).
% 5.89/2.15  tff(c_2407, plain, (![A_392, B_393]: (~v3_funct_2('#skF_3', A_392, B_393))), inference(splitLeft, [status(thm)], [c_2405])).
% 5.89/2.15  tff(c_2409, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2407, c_74])).
% 5.89/2.15  tff(c_2410, plain, (v2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_2405])).
% 5.89/2.15  tff(c_2450, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2446, c_2410])).
% 5.89/2.15  tff(c_8, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.89/2.15  tff(c_1699, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1690, c_1690, c_8])).
% 5.89/2.15  tff(c_12, plain, (![A_5]: (k1_relat_1(A_5)!=k1_xboole_0 | k1_xboole_0=A_5 | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.89/2.15  tff(c_161, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_131, c_12])).
% 5.89/2.15  tff(c_1692, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_161])).
% 5.89/2.15  tff(c_1716, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1699, c_1690, c_1692])).
% 5.89/2.15  tff(c_1718, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_161])).
% 5.89/2.15  tff(c_1753, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1690, c_1718])).
% 5.89/2.15  tff(c_2467, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2446, c_2446, c_1753])).
% 5.89/2.15  tff(c_2982, plain, (![A_507, B_508]: (k2_funct_1(A_507)=B_508 | k6_partfun1(k2_relat_1(A_507))!=k5_relat_1(B_508, A_507) | k2_relat_1(B_508)!=k1_relat_1(A_507) | ~v2_funct_1(A_507) | ~v1_funct_1(B_508) | ~v1_relat_1(B_508) | ~v1_funct_1(A_507) | ~v1_relat_1(A_507))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_18])).
% 5.89/2.15  tff(c_2984, plain, (![B_508]: (k2_funct_1('#skF_1')=B_508 | k5_relat_1(B_508, '#skF_1')!=k6_partfun1('#skF_1') | k2_relat_1(B_508)!=k1_relat_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1(B_508) | ~v1_relat_1(B_508) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2466, c_2982])).
% 5.89/2.15  tff(c_2998, plain, (![B_509]: (k2_funct_1('#skF_1')=B_509 | k5_relat_1(B_509, '#skF_1')!=k6_partfun1('#skF_1') | k2_relat_1(B_509)!='#skF_1' | ~v1_funct_1(B_509) | ~v1_relat_1(B_509))), inference(demodulation, [status(thm), theory('equality')], [c_2470, c_2473, c_2450, c_2467, c_2984])).
% 5.89/2.15  tff(c_3001, plain, (k2_funct_1('#skF_1')='#skF_1' | k5_relat_1('#skF_1', '#skF_1')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_1')!='#skF_1' | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_2470, c_2998])).
% 5.89/2.15  tff(c_3007, plain, (k2_funct_1('#skF_1')='#skF_1' | k5_relat_1('#skF_1', '#skF_1')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2473, c_2466, c_3001])).
% 5.89/2.15  tff(c_3009, plain, (k5_relat_1('#skF_1', '#skF_1')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_3007])).
% 5.89/2.15  tff(c_2464, plain, (![A_1]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_2446, c_1741])).
% 5.89/2.15  tff(c_3032, plain, (![D_528, E_525, A_523, C_527, B_524, F_526]: (k1_partfun1(A_523, B_524, C_527, D_528, E_525, F_526)=k5_relat_1(E_525, F_526) | ~m1_subset_1(F_526, k1_zfmisc_1(k2_zfmisc_1(C_527, D_528))) | ~v1_funct_1(F_526) | ~m1_subset_1(E_525, k1_zfmisc_1(k2_zfmisc_1(A_523, B_524))) | ~v1_funct_1(E_525))), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.89/2.15  tff(c_3035, plain, (![D_528, E_525, A_523, C_527, B_524]: (k1_partfun1(A_523, B_524, C_527, D_528, E_525, '#skF_1')=k5_relat_1(E_525, '#skF_1') | ~v1_funct_1('#skF_1') | ~m1_subset_1(E_525, k1_zfmisc_1(k2_zfmisc_1(A_523, B_524))) | ~v1_funct_1(E_525))), inference(resolution, [status(thm)], [c_2464, c_3032])).
% 5.89/2.15  tff(c_3051, plain, (![A_540, C_536, D_537, E_538, B_539]: (k1_partfun1(A_540, B_539, C_536, D_537, E_538, '#skF_1')=k5_relat_1(E_538, '#skF_1') | ~m1_subset_1(E_538, k1_zfmisc_1(k2_zfmisc_1(A_540, B_539))) | ~v1_funct_1(E_538))), inference(demodulation, [status(thm), theory('equality')], [c_2473, c_3035])).
% 5.89/2.15  tff(c_3054, plain, (![A_540, B_539, C_536, D_537]: (k1_partfun1(A_540, B_539, C_536, D_537, '#skF_1', '#skF_1')=k5_relat_1('#skF_1', '#skF_1') | ~v1_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_2464, c_3051])).
% 5.89/2.15  tff(c_3062, plain, (![A_541, B_542, C_543, D_544]: (k1_partfun1(A_541, B_542, C_543, D_544, '#skF_1', '#skF_1')=k5_relat_1('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2473, c_3054])).
% 5.89/2.15  tff(c_2845, plain, (![A_494, E_493, B_492, D_491, F_495, C_496]: (m1_subset_1(k1_partfun1(A_494, B_492, C_496, D_491, E_493, F_495), k1_zfmisc_1(k2_zfmisc_1(A_494, D_491))) | ~m1_subset_1(F_495, k1_zfmisc_1(k2_zfmisc_1(C_496, D_491))) | ~v1_funct_1(F_495) | ~m1_subset_1(E_493, k1_zfmisc_1(k2_zfmisc_1(A_494, B_492))) | ~v1_funct_1(E_493))), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.89/2.15  tff(c_1765, plain, (![C_277, B_278, A_279]: (v5_relat_1(C_277, B_278) | ~m1_subset_1(C_277, k1_zfmisc_1(k2_zfmisc_1(A_279, B_278))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.89/2.15  tff(c_1776, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_80, c_1765])).
% 5.89/2.15  tff(c_1869, plain, (![B_298, A_299]: (k2_relat_1(B_298)=A_299 | ~v2_funct_2(B_298, A_299) | ~v5_relat_1(B_298, A_299) | ~v1_relat_1(B_298))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.89/2.15  tff(c_1878, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1776, c_1869])).
% 5.89/2.15  tff(c_1887, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_1878])).
% 5.89/2.15  tff(c_1888, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_1887])).
% 5.89/2.15  tff(c_2014, plain, (![C_324, B_325, A_326]: (v2_funct_2(C_324, B_325) | ~v3_funct_2(C_324, A_326, B_325) | ~v1_funct_1(C_324) | ~m1_subset_1(C_324, k1_zfmisc_1(k2_zfmisc_1(A_326, B_325))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.89/2.15  tff(c_2024, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_2014])).
% 5.89/2.15  tff(c_2031, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_2024])).
% 5.89/2.15  tff(c_2033, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1888, c_2031])).
% 5.89/2.15  tff(c_2034, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_1887])).
% 5.89/2.15  tff(c_140, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_130, c_10])).
% 5.89/2.15  tff(c_1803, plain, (k2_relat_1('#skF_2')!='#skF_3' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1690, c_1690, c_140])).
% 5.89/2.15  tff(c_1804, plain, (k2_relat_1('#skF_2')!='#skF_3'), inference(splitLeft, [status(thm)], [c_1803])).
% 5.89/2.15  tff(c_2036, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2034, c_1804])).
% 5.89/2.15  tff(c_2173, plain, (![C_352, B_353, A_354]: (v2_funct_2(C_352, B_353) | ~v3_funct_2(C_352, A_354, B_353) | ~v1_funct_1(C_352) | ~m1_subset_1(C_352, k1_zfmisc_1(k2_zfmisc_1(A_354, B_353))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.89/2.15  tff(c_2177, plain, (![B_353, A_354]: (v2_funct_2('#skF_3', B_353) | ~v3_funct_2('#skF_3', A_354, B_353) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1741, c_2173])).
% 5.89/2.15  tff(c_2191, plain, (![B_355, A_356]: (v2_funct_2('#skF_3', B_355) | ~v3_funct_2('#skF_3', A_356, B_355))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2177])).
% 5.89/2.15  tff(c_2195, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_74, c_2191])).
% 5.89/2.15  tff(c_1783, plain, (![A_282]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_282)))), inference(demodulation, [status(thm), theory('equality')], [c_1690, c_2])).
% 5.89/2.15  tff(c_1796, plain, (![B_14]: (v5_relat_1('#skF_3', B_14))), inference(resolution, [status(thm)], [c_1783, c_22])).
% 5.89/2.15  tff(c_1872, plain, (![B_14]: (k2_relat_1('#skF_3')=B_14 | ~v2_funct_2('#skF_3', B_14) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1796, c_1869])).
% 5.89/2.15  tff(c_1881, plain, (![B_14]: (B_14='#skF_3' | ~v2_funct_2('#skF_3', B_14))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_1758, c_1872])).
% 5.89/2.15  tff(c_2198, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_2195, c_1881])).
% 5.89/2.15  tff(c_2202, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2036, c_2198])).
% 5.89/2.15  tff(c_2203, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_1803])).
% 5.89/2.15  tff(c_139, plain, (k1_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_130, c_12])).
% 5.89/2.15  tff(c_1779, plain, (k1_relat_1('#skF_2')!='#skF_3' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1690, c_1690, c_139])).
% 5.89/2.15  tff(c_1780, plain, (k1_relat_1('#skF_2')!='#skF_3'), inference(splitLeft, [status(thm)], [c_1779])).
% 5.89/2.15  tff(c_2205, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2203, c_1780])).
% 5.89/2.15  tff(c_2217, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1753, c_2205])).
% 5.89/2.15  tff(c_2218, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_1779])).
% 5.89/2.15  tff(c_2223, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_3'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2218, c_70])).
% 5.89/2.15  tff(c_2452, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2446, c_2446, c_2223])).
% 5.89/2.15  tff(c_2677, plain, (![D_433, C_434, A_435, B_436]: (D_433=C_434 | ~r2_relset_1(A_435, B_436, C_434, D_433) | ~m1_subset_1(D_433, k1_zfmisc_1(k2_zfmisc_1(A_435, B_436))) | ~m1_subset_1(C_434, k1_zfmisc_1(k2_zfmisc_1(A_435, B_436))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.89/2.15  tff(c_2679, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_2452, c_2677])).
% 5.89/2.15  tff(c_2686, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2679])).
% 5.89/2.15  tff(c_2702, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2686])).
% 5.89/2.15  tff(c_2870, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_2845, c_2702])).
% 5.89/2.15  tff(c_2914, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2473, c_2464, c_2870])).
% 5.89/2.15  tff(c_2915, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2686])).
% 5.89/2.15  tff(c_3066, plain, (k5_relat_1('#skF_1', '#skF_1')=k6_partfun1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3062, c_2915])).
% 5.89/2.15  tff(c_3073, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3009, c_3066])).
% 5.89/2.15  tff(c_3074, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_3007])).
% 5.89/2.15  tff(c_2350, plain, (![A_383, B_384, C_385]: (k1_relset_1(A_383, B_384, C_385)=k1_relat_1(C_385) | ~m1_subset_1(C_385, k1_zfmisc_1(k2_zfmisc_1(A_383, B_384))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.89/2.15  tff(c_2354, plain, (![A_383, B_384]: (k1_relset_1(A_383, B_384, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1741, c_2350])).
% 5.89/2.15  tff(c_2359, plain, (![A_383, B_384]: (k1_relset_1(A_383, B_384, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1753, c_2354])).
% 5.89/2.15  tff(c_2451, plain, (![A_383, B_384]: (k1_relset_1(A_383, B_384, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2446, c_2446, c_2359])).
% 5.89/2.15  tff(c_2469, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2446, c_1690])).
% 5.89/2.15  tff(c_42, plain, (![C_28, B_27]: (v1_funct_2(C_28, k1_xboole_0, B_27) | k1_relset_1(k1_xboole_0, B_27, C_28)!=k1_xboole_0 | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_27))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.89/2.15  tff(c_2941, plain, (![C_501, B_502]: (v1_funct_2(C_501, '#skF_1', B_502) | k1_relset_1('#skF_1', B_502, C_501)!='#skF_1' | ~m1_subset_1(C_501, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_502))))), inference(demodulation, [status(thm), theory('equality')], [c_2469, c_2469, c_2469, c_2469, c_42])).
% 5.89/2.15  tff(c_2945, plain, (![B_502]: (v1_funct_2('#skF_1', '#skF_1', B_502) | k1_relset_1('#skF_1', B_502, '#skF_1')!='#skF_1')), inference(resolution, [status(thm)], [c_2464, c_2941])).
% 5.89/2.15  tff(c_2952, plain, (![B_502]: (v1_funct_2('#skF_1', '#skF_1', B_502))), inference(demodulation, [status(thm), theory('equality')], [c_2451, c_2945])).
% 5.89/2.15  tff(c_2472, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2446, c_74])).
% 5.89/2.15  tff(c_2963, plain, (![A_504, B_505]: (k2_funct_2(A_504, B_505)=k2_funct_1(B_505) | ~m1_subset_1(B_505, k1_zfmisc_1(k2_zfmisc_1(A_504, A_504))) | ~v3_funct_2(B_505, A_504, A_504) | ~v1_funct_2(B_505, A_504, A_504) | ~v1_funct_1(B_505))), inference(cnfTransformation, [status(thm)], [f_167])).
% 5.89/2.15  tff(c_2967, plain, (![A_504]: (k2_funct_2(A_504, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_504, A_504) | ~v1_funct_2('#skF_1', A_504, A_504) | ~v1_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_2464, c_2963])).
% 5.89/2.15  tff(c_2975, plain, (![A_506]: (k2_funct_2(A_506, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_506, A_506) | ~v1_funct_2('#skF_1', A_506, A_506))), inference(demodulation, [status(thm), theory('equality')], [c_2473, c_2967])).
% 5.89/2.15  tff(c_2978, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_2472, c_2975])).
% 5.89/2.15  tff(c_2981, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2952, c_2978])).
% 5.89/2.15  tff(c_2224, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2218, c_68])).
% 5.89/2.15  tff(c_2462, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2446, c_2446, c_2224])).
% 5.89/2.15  tff(c_2993, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2981, c_2462])).
% 5.89/2.15  tff(c_3077, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3074, c_2993])).
% 5.89/2.15  tff(c_3082, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2453, c_3077])).
% 5.89/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.89/2.15  
% 5.89/2.15  Inference rules
% 5.89/2.15  ----------------------
% 5.89/2.15  #Ref     : 0
% 5.89/2.15  #Sup     : 584
% 5.89/2.15  #Fact    : 0
% 5.89/2.15  #Define  : 0
% 5.89/2.15  #Split   : 37
% 5.89/2.15  #Chain   : 0
% 5.89/2.15  #Close   : 0
% 5.89/2.15  
% 5.89/2.15  Ordering : KBO
% 5.89/2.15  
% 5.89/2.15  Simplification rules
% 5.89/2.15  ----------------------
% 5.89/2.15  #Subsume      : 45
% 5.89/2.15  #Demod        : 507
% 5.89/2.15  #Tautology    : 258
% 5.89/2.15  #SimpNegUnit  : 21
% 5.89/2.15  #BackRed      : 91
% 5.89/2.15  
% 5.89/2.15  #Partial instantiations: 0
% 5.89/2.15  #Strategies tried      : 1
% 5.89/2.15  
% 5.89/2.15  Timing (in seconds)
% 5.89/2.15  ----------------------
% 5.89/2.15  Preprocessing        : 0.40
% 5.89/2.15  Parsing              : 0.22
% 5.89/2.15  CNF conversion       : 0.02
% 5.89/2.15  Main loop            : 0.85
% 5.89/2.15  Inferencing          : 0.33
% 5.89/2.15  Reduction            : 0.27
% 5.89/2.15  Demodulation         : 0.19
% 5.89/2.15  BG Simplification    : 0.04
% 5.89/2.15  Subsumption          : 0.14
% 5.89/2.15  Abstraction          : 0.04
% 5.89/2.15  MUC search           : 0.00
% 5.89/2.15  Cooper               : 0.00
% 5.89/2.15  Total                : 1.33
% 5.89/2.15  Index Insertion      : 0.00
% 5.89/2.15  Index Deletion       : 0.00
% 5.89/2.15  Index Matching       : 0.00
% 5.89/2.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
