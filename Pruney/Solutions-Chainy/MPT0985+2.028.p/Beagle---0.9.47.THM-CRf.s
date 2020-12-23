%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:29 EST 2020

% Result     : Theorem 8.77s
% Output     : CNFRefutation 9.17s
% Verified   : 
% Statistics : Number of formulae       :  472 (12531 expanded)
%              Number of leaves         :   45 (3946 expanded)
%              Depth                    :   18
%              Number of atoms          :  762 (32600 expanded)
%              Number of equality atoms :  280 (12468 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_160,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_143,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_120,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_47,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_133,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_88,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_12061,plain,(
    ! [C_1096,A_1097,B_1098] :
      ( v1_relat_1(C_1096)
      | ~ m1_subset_1(C_1096,k1_zfmisc_1(k2_zfmisc_1(A_1097,B_1098))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_12082,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_12061])).

tff(c_92,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_86,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_84,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_12692,plain,(
    ! [A_1172,B_1173,C_1174] :
      ( k2_relset_1(A_1172,B_1173,C_1174) = k2_relat_1(C_1174)
      | ~ m1_subset_1(C_1174,k1_zfmisc_1(k2_zfmisc_1(A_1172,B_1173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_12705,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_12692])).

tff(c_12720,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_12705])).

tff(c_44,plain,(
    ! [A_20] :
      ( k1_relat_1(k2_funct_1(A_20)) = k2_relat_1(A_20)
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_90,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_184,plain,(
    ! [A_61] :
      ( v1_funct_1(k2_funct_1(A_61))
      | ~ v1_funct_1(A_61)
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_82,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_149,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_187,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_184,c_149])).

tff(c_190,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_187])).

tff(c_235,plain,(
    ! [C_74,A_75,B_76] :
      ( v1_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_245,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_235])).

tff(c_260,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_190,c_245])).

tff(c_261,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_263,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_261])).

tff(c_347,plain,(
    ! [C_97,A_98,B_99] :
      ( v1_relat_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_369,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_347])).

tff(c_912,plain,(
    ! [A_163,B_164,C_165] :
      ( k2_relset_1(A_163,B_164,C_165) = k2_relat_1(C_165)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_925,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_912])).

tff(c_940,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_925])).

tff(c_40,plain,(
    ! [A_19] :
      ( v1_relat_1(k2_funct_1(A_19))
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_262,plain,(
    v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_626,plain,(
    ! [A_133] :
      ( k1_relat_1(k2_funct_1(A_133)) = k2_relat_1(A_133)
      | ~ v2_funct_1(A_133)
      | ~ v1_funct_1(A_133)
      | ~ v1_relat_1(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_78,plain,(
    ! [A_36] :
      ( v1_funct_2(A_36,k1_relat_1(A_36),k2_relat_1(A_36))
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_3527,plain,(
    ! [A_361] :
      ( v1_funct_2(k2_funct_1(A_361),k2_relat_1(A_361),k2_relat_1(k2_funct_1(A_361)))
      | ~ v1_funct_1(k2_funct_1(A_361))
      | ~ v1_relat_1(k2_funct_1(A_361))
      | ~ v2_funct_1(A_361)
      | ~ v1_funct_1(A_361)
      | ~ v1_relat_1(A_361) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_626,c_78])).

tff(c_3536,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_940,c_3527])).

tff(c_3547,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_92,c_86,c_262,c_3536])).

tff(c_3573,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_3547])).

tff(c_3607,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_3573])).

tff(c_3611,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_92,c_3607])).

tff(c_3613,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_3547])).

tff(c_32,plain,(
    ! [A_17] :
      ( k2_relat_1(A_17) != k1_xboole_0
      | k1_xboole_0 = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_378,plain,
    ( k2_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_369,c_32])).

tff(c_404,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_378])).

tff(c_942,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_940,c_404])).

tff(c_728,plain,(
    ! [A_141,B_142,C_143] :
      ( k1_relset_1(A_141,B_142,C_143) = k1_relat_1(C_143)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_751,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_728])).

tff(c_1223,plain,(
    ! [B_191,A_192,C_193] :
      ( k1_xboole_0 = B_191
      | k1_relset_1(A_192,B_191,C_193) = A_192
      | ~ v1_funct_2(C_193,A_192,B_191)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(A_192,B_191))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1239,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_1223])).

tff(c_1261,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_751,c_1239])).

tff(c_1262,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_942,c_1261])).

tff(c_42,plain,(
    ! [A_20] :
      ( k2_relat_1(k2_funct_1(A_20)) = k1_relat_1(A_20)
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_855,plain,(
    ! [A_152] :
      ( m1_subset_1(A_152,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_152),k2_relat_1(A_152))))
      | ~ v1_funct_1(A_152)
      | ~ v1_relat_1(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_3841,plain,(
    ! [A_387] :
      ( m1_subset_1(k2_funct_1(A_387),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_387)),k1_relat_1(A_387))))
      | ~ v1_funct_1(k2_funct_1(A_387))
      | ~ v1_relat_1(k2_funct_1(A_387))
      | ~ v2_funct_1(A_387)
      | ~ v1_funct_1(A_387)
      | ~ v1_relat_1(A_387) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_855])).

tff(c_3870,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1262,c_3841])).

tff(c_3892,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_92,c_86,c_3613,c_262,c_3870])).

tff(c_3917,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'),'#skF_3')))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_3892])).

tff(c_3932,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_92,c_86,c_940,c_3917])).

tff(c_3934,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_263,c_3932])).

tff(c_3935,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_378])).

tff(c_3936,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_378])).

tff(c_3962,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3935,c_3936])).

tff(c_4407,plain,(
    ! [A_439,B_440,C_441] :
      ( k2_relset_1(A_439,B_440,C_441) = k2_relat_1(C_441)
      | ~ m1_subset_1(C_441,k1_zfmisc_1(k2_zfmisc_1(A_439,B_440))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_4423,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_4407])).

tff(c_4431,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3962,c_84,c_4423])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3950,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3935,c_8])).

tff(c_4454,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4431,c_3950])).

tff(c_18,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3947,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3935,c_3935,c_18])).

tff(c_4450,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4431,c_4431,c_3947])).

tff(c_4095,plain,(
    ! [C_401,B_402,A_403] :
      ( ~ v1_xboole_0(C_401)
      | ~ m1_subset_1(B_402,k1_zfmisc_1(C_401))
      | ~ r2_hidden(A_403,B_402) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4116,plain,(
    ! [A_403] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_403,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_88,c_4095])).

tff(c_4136,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4116])).

tff(c_4595,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4450,c_4136])).

tff(c_4598,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4454,c_4595])).

tff(c_4600,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4116])).

tff(c_22,plain,(
    ! [A_10] : k2_subset_1(A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [A_11] : m1_subset_1(k2_subset_1(A_11),k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_93,plain,(
    ! [A_11] : m1_subset_1(A_11,k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24])).

tff(c_4118,plain,(
    ! [A_404,A_405] :
      ( ~ v1_xboole_0(A_404)
      | ~ r2_hidden(A_405,A_404) ) ),
    inference(resolution,[status(thm)],[c_93,c_4095])).

tff(c_4122,plain,(
    ! [A_1,B_2] :
      ( ~ v1_xboole_0(A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_4118])).

tff(c_264,plain,(
    ! [A_77,B_78] :
      ( r1_tarski(A_77,B_78)
      | ~ m1_subset_1(A_77,k1_zfmisc_1(B_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_271,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_88,c_264])).

tff(c_4035,plain,(
    ! [B_395,A_396] :
      ( B_395 = A_396
      | ~ r1_tarski(B_395,A_396)
      | ~ r1_tarski(A_396,B_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4049,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_271,c_4035])).

tff(c_4626,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4049])).

tff(c_4640,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_4122,c_4626])).

tff(c_4644,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4600,c_4640])).

tff(c_4645,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_4049])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( k1_xboole_0 = B_9
      | k1_xboole_0 = A_8
      | k2_zfmisc_1(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_5059,plain,(
    ! [B_493,A_494] :
      ( B_493 = '#skF_5'
      | A_494 = '#skF_5'
      | k2_zfmisc_1(A_494,B_493) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3935,c_3935,c_3935,c_16])).

tff(c_5069,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_4645,c_5059])).

tff(c_5101,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5069])).

tff(c_34,plain,(
    ! [A_17] :
      ( k1_relat_1(A_17) != k1_xboole_0
      | k1_xboole_0 = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_377,plain,
    ( k1_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_369,c_34])).

tff(c_379,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_377])).

tff(c_3938,plain,(
    k1_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3935,c_379])).

tff(c_5125,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5101,c_5101,c_3938])).

tff(c_20,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_304,plain,(
    ! [A_87,B_88] : m1_subset_1('#skF_2'(A_87,B_88),k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_321,plain,(
    ! [B_91] : m1_subset_1('#skF_2'(k1_xboole_0,B_91),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_304])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_325,plain,(
    ! [B_91] : r1_tarski('#skF_2'(k1_xboole_0,B_91),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_321,c_26])).

tff(c_3940,plain,(
    ! [B_91] : r1_tarski('#skF_2'('#skF_5',B_91),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3935,c_3935,c_325])).

tff(c_4605,plain,(
    ! [A_453] : ~ r2_hidden(A_453,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_4116])).

tff(c_4612,plain,(
    ! [B_454] : r1_tarski('#skF_5',B_454) ),
    inference(resolution,[status(thm)],[c_6,c_4605])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4745,plain,(
    ! [B_463] :
      ( B_463 = '#skF_5'
      | ~ r1_tarski(B_463,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4612,c_10])).

tff(c_4767,plain,(
    ! [B_91] : '#skF_2'('#skF_5',B_91) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3940,c_4745])).

tff(c_5313,plain,(
    ! [B_507] : '#skF_2'('#skF_3',B_507) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5101,c_5101,c_4767])).

tff(c_64,plain,(
    ! [A_33,B_34] : v1_funct_2('#skF_2'(A_33,B_34),A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_5397,plain,(
    ! [B_510] : v1_funct_2('#skF_3','#skF_3',B_510) ),
    inference(superposition,[status(thm),theory(equality)],[c_5313,c_64])).

tff(c_5128,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5101,c_3935])).

tff(c_60,plain,(
    ! [B_31,C_32] :
      ( k1_relset_1(k1_xboole_0,B_31,C_32) = k1_xboole_0
      | ~ v1_funct_2(C_32,k1_xboole_0,B_31)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_94,plain,(
    ! [B_31,C_32] :
      ( k1_relset_1(k1_xboole_0,B_31,C_32) = k1_xboole_0
      | ~ v1_funct_2(C_32,k1_xboole_0,B_31)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_60])).

tff(c_5267,plain,(
    ! [B_31,C_32] :
      ( k1_relset_1('#skF_3',B_31,C_32) = '#skF_3'
      | ~ v1_funct_2(C_32,'#skF_3',B_31)
      | ~ m1_subset_1(C_32,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5128,c_5128,c_5128,c_5128,c_94])).

tff(c_5399,plain,(
    ! [B_510] :
      ( k1_relset_1('#skF_3',B_510,'#skF_3') = '#skF_3'
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_5397,c_5267])).

tff(c_5402,plain,(
    ! [B_510] : k1_relset_1('#skF_3',B_510,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_5399])).

tff(c_4891,plain,(
    ! [A_472,B_473,C_474] :
      ( k1_relset_1(A_472,B_473,C_474) = k1_relat_1(C_474)
      | ~ m1_subset_1(C_474,k1_zfmisc_1(k2_zfmisc_1(A_472,B_473))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_5022,plain,(
    ! [C_484] :
      ( k1_relset_1('#skF_3','#skF_4',C_484) = k1_relat_1(C_484)
      | ~ m1_subset_1(C_484,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4645,c_4891])).

tff(c_5032,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_93,c_5022])).

tff(c_5103,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5101,c_5101,c_5032])).

tff(c_5559,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5402,c_5103])).

tff(c_5560,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5125,c_5559])).

tff(c_5561,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5069])).

tff(c_5586,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5561,c_5561,c_3938])).

tff(c_5820,plain,(
    ! [B_538] : '#skF_2'('#skF_4',B_538) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5561,c_5561,c_4767])).

tff(c_5902,plain,(
    ! [B_540] : v1_funct_2('#skF_4','#skF_4',B_540) ),
    inference(superposition,[status(thm),theory(equality)],[c_5820,c_64])).

tff(c_5589,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5561,c_3935])).

tff(c_5808,plain,(
    ! [B_31,C_32] :
      ( k1_relset_1('#skF_4',B_31,C_32) = '#skF_4'
      | ~ v1_funct_2(C_32,'#skF_4',B_31)
      | ~ m1_subset_1(C_32,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5589,c_5589,c_5589,c_5589,c_94])).

tff(c_5904,plain,(
    ! [B_540] :
      ( k1_relset_1('#skF_4',B_540,'#skF_4') = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_5902,c_5808])).

tff(c_5907,plain,(
    ! [B_540] : k1_relset_1('#skF_4',B_540,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_5904])).

tff(c_5574,plain,(
    ! [B_91] : '#skF_2'('#skF_4',B_91) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5561,c_5561,c_4767])).

tff(c_74,plain,(
    ! [A_33,B_34] : m1_subset_1('#skF_2'(A_33,B_34),k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_6237,plain,(
    ! [A_574,B_575] : k1_relset_1(A_574,B_575,'#skF_2'(A_574,B_575)) = k1_relat_1('#skF_2'(A_574,B_575)) ),
    inference(resolution,[status(thm)],[c_74,c_4891])).

tff(c_6249,plain,(
    ! [B_91] : k1_relat_1('#skF_2'('#skF_4',B_91)) = k1_relset_1('#skF_4',B_91,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5574,c_6237])).

tff(c_6253,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5907,c_5574,c_6249])).

tff(c_6255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5586,c_6253])).

tff(c_6256,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_377])).

tff(c_6257,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_377])).

tff(c_6280,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6256,c_6257])).

tff(c_6788,plain,(
    ! [A_635,B_636,C_637] :
      ( k1_relset_1(A_635,B_636,C_637) = k1_relat_1(C_637)
      | ~ m1_subset_1(C_637,k1_zfmisc_1(k2_zfmisc_1(A_635,B_636))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_6804,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_6788])).

tff(c_6812,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6280,c_6804])).

tff(c_62,plain,(
    ! [B_31,A_30,C_32] :
      ( k1_xboole_0 = B_31
      | k1_relset_1(A_30,B_31,C_32) = A_30
      | ~ v1_funct_2(C_32,A_30,B_31)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_6952,plain,(
    ! [B_649,A_650,C_651] :
      ( B_649 = '#skF_5'
      | k1_relset_1(A_650,B_649,C_651) = A_650
      | ~ v1_funct_2(C_651,A_650,B_649)
      | ~ m1_subset_1(C_651,k1_zfmisc_1(k2_zfmisc_1(A_650,B_649))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6256,c_62])).

tff(c_6971,plain,
    ( '#skF_5' = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_6952])).

tff(c_6984,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_6812,c_6971])).

tff(c_6986,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_6984])).

tff(c_6269,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6256,c_8])).

tff(c_7010,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6986,c_6269])).

tff(c_6267,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_5',B_9) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6256,c_6256,c_20])).

tff(c_7008,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_3',B_9) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6986,c_6986,c_6267])).

tff(c_6481,plain,(
    ! [C_599,B_600,A_601] :
      ( ~ v1_xboole_0(C_599)
      | ~ m1_subset_1(B_600,k1_zfmisc_1(C_599))
      | ~ r2_hidden(A_601,B_600) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6502,plain,(
    ! [A_601] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_601,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_88,c_6481])).

tff(c_6531,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_6502])).

tff(c_7143,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7008,c_6531])).

tff(c_7146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7010,c_7143])).

tff(c_7147,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6984])).

tff(c_7172,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7147,c_6269])).

tff(c_6266,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6256,c_6256,c_18])).

tff(c_7169,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7147,c_7147,c_6266])).

tff(c_7280,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7169,c_6531])).

tff(c_7283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7172,c_7280])).

tff(c_7285,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_6502])).

tff(c_6504,plain,(
    ! [A_602,A_603] :
      ( ~ v1_xboole_0(A_602)
      | ~ r2_hidden(A_603,A_602) ) ),
    inference(resolution,[status(thm)],[c_93,c_6481])).

tff(c_6509,plain,(
    ! [A_604,B_605] :
      ( ~ v1_xboole_0(A_604)
      | r1_tarski(A_604,B_605) ) ),
    inference(resolution,[status(thm)],[c_6,c_6504])).

tff(c_6333,plain,(
    ! [B_582,A_583] :
      ( B_582 = A_583
      | ~ r1_tarski(B_582,A_583)
      | ~ r1_tarski(A_583,B_582) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6347,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_271,c_6333])).

tff(c_6367,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_6347])).

tff(c_6528,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_6509,c_6367])).

tff(c_7320,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7285,c_6528])).

tff(c_7321,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_6347])).

tff(c_7471,plain,(
    ! [B_686,A_687] :
      ( B_686 = '#skF_5'
      | A_687 = '#skF_5'
      | k2_zfmisc_1(A_687,B_686) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6256,c_6256,c_6256,c_16])).

tff(c_7481,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_7321,c_7471])).

tff(c_7486,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_7481])).

tff(c_7503,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7486,c_6269])).

tff(c_7502,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7486,c_7486,c_6280])).

tff(c_7505,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7486,c_369])).

tff(c_7512,plain,(
    v1_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7486,c_92])).

tff(c_7511,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7486,c_86])).

tff(c_7508,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7486,c_262])).

tff(c_7667,plain,(
    ! [A_702] :
      ( k2_relat_1(k2_funct_1(A_702)) = k1_relat_1(A_702)
      | ~ v2_funct_1(A_702)
      | ~ v1_funct_1(A_702)
      | ~ v1_relat_1(A_702) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_9522,plain,(
    ! [A_876] :
      ( v1_funct_2(k2_funct_1(A_876),k1_relat_1(k2_funct_1(A_876)),k1_relat_1(A_876))
      | ~ v1_funct_1(k2_funct_1(A_876))
      | ~ v1_relat_1(k2_funct_1(A_876))
      | ~ v2_funct_1(A_876)
      | ~ v1_funct_1(A_876)
      | ~ v1_relat_1(A_876) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7667,c_78])).

tff(c_9537,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7502,c_9522])).

tff(c_9543,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7505,c_7512,c_7511,c_7508,c_9537])).

tff(c_9624,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_9543])).

tff(c_9627,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_9624])).

tff(c_9631,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7505,c_7512,c_9627])).

tff(c_9633,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_9543])).

tff(c_6264,plain,(
    ! [A_17] :
      ( k2_relat_1(A_17) != '#skF_5'
      | A_17 = '#skF_5'
      | ~ v1_relat_1(A_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6256,c_6256,c_32])).

tff(c_7488,plain,(
    ! [A_17] :
      ( k2_relat_1(A_17) != '#skF_3'
      | A_17 = '#skF_3'
      | ~ v1_relat_1(A_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7486,c_7486,c_6264])).

tff(c_9641,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) != '#skF_3'
    | k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_9633,c_7488])).

tff(c_9676,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_9641])).

tff(c_9684,plain,
    ( k1_relat_1('#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_9676])).

tff(c_9687,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7505,c_7512,c_7511,c_7502,c_9684])).

tff(c_9688,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_9641])).

tff(c_6263,plain,(
    ! [A_17] :
      ( k1_relat_1(A_17) != '#skF_5'
      | A_17 = '#skF_5'
      | ~ v1_relat_1(A_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6256,c_6256,c_34])).

tff(c_7489,plain,(
    ! [A_17] :
      ( k1_relat_1(A_17) != '#skF_3'
      | A_17 = '#skF_3'
      | ~ v1_relat_1(A_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7486,c_7486,c_6263])).

tff(c_9640,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) != '#skF_3'
    | k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_9633,c_7489])).

tff(c_9653,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_9640])).

tff(c_9690,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9688,c_9653])).

tff(c_9700,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7502,c_9690])).

tff(c_9701,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_9640])).

tff(c_7522,plain,(
    ! [C_688,B_689,A_690] :
      ( ~ v1_xboole_0(C_688)
      | ~ m1_subset_1(B_689,k1_zfmisc_1(C_688))
      | ~ r2_hidden(A_690,B_689) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_7589,plain,(
    ! [A_693,A_694] :
      ( ~ v1_xboole_0(A_693)
      | ~ r2_hidden(A_694,A_693) ) ),
    inference(resolution,[status(thm)],[c_93,c_7522])).

tff(c_7593,plain,(
    ! [A_1,B_2] :
      ( ~ v1_xboole_0(A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_7589])).

tff(c_28,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_7500,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7486,c_7486,c_6266])).

tff(c_7507,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7486,c_263])).

tff(c_7631,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7500,c_7507])).

tff(c_7635,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_7631])).

tff(c_7639,plain,(
    ~ v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_7593,c_7635])).

tff(c_9706,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9701,c_7639])).

tff(c_9715,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7503,c_9706])).

tff(c_9716,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_7481])).

tff(c_9734,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9716,c_6269])).

tff(c_9736,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9716,c_369])).

tff(c_9743,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9716,c_92])).

tff(c_9742,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9716,c_86])).

tff(c_310,plain,(
    ! [A_8] : m1_subset_1('#skF_2'(A_8,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_304])).

tff(c_6262,plain,(
    ! [A_8] : m1_subset_1('#skF_2'(A_8,'#skF_5'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6256,c_6256,c_310])).

tff(c_9993,plain,(
    ! [A_904] : m1_subset_1('#skF_2'(A_904,'#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9716,c_9716,c_6262])).

tff(c_30,plain,(
    ! [C_16,B_15,A_14] :
      ( ~ v1_xboole_0(C_16)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(C_16))
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_9995,plain,(
    ! [A_14,A_904] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_14,'#skF_2'(A_904,'#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_9993,c_30])).

tff(c_10019,plain,(
    ! [A_907,A_908] : ~ r2_hidden(A_907,'#skF_2'(A_908,'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9734,c_9995])).

tff(c_10024,plain,(
    ! [A_908,B_2] : r1_tarski('#skF_2'(A_908,'#skF_4'),B_2) ),
    inference(resolution,[status(thm)],[c_6,c_10019])).

tff(c_9749,plain,(
    ! [C_881,B_882,A_883] :
      ( ~ v1_xboole_0(C_881)
      | ~ m1_subset_1(B_882,k1_zfmisc_1(C_881))
      | ~ r2_hidden(A_883,B_882) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_9831,plain,(
    ! [A_887,A_888] :
      ( ~ v1_xboole_0(A_887)
      | ~ r2_hidden(A_888,A_887) ) ),
    inference(resolution,[status(thm)],[c_93,c_9749])).

tff(c_9835,plain,(
    ! [A_1,B_2] :
      ( ~ v1_xboole_0(A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_9831])).

tff(c_314,plain,(
    ! [A_87,B_88] : r1_tarski('#skF_2'(A_87,B_88),k2_zfmisc_1(A_87,B_88)) ),
    inference(resolution,[status(thm)],[c_304,c_26])).

tff(c_7334,plain,(
    r1_tarski('#skF_2'('#skF_3','#skF_4'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7321,c_314])).

tff(c_7367,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_5'
    | ~ r1_tarski('#skF_5','#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_7334,c_10])).

tff(c_10065,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9716,c_9716,c_7367])).

tff(c_10066,plain,(
    ~ r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_10065])).

tff(c_10069,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_9835,c_10066])).

tff(c_10073,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9734,c_10069])).

tff(c_10074,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_10065])).

tff(c_10138,plain,(
    ! [B_916] : r1_tarski('#skF_4',B_916) ),
    inference(superposition,[status(thm),theory(equality)],[c_10074,c_10024])).

tff(c_10158,plain,(
    ! [B_917] :
      ( B_917 = '#skF_4'
      | ~ r1_tarski(B_917,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10138,c_10])).

tff(c_10181,plain,(
    ! [A_908] : '#skF_2'(A_908,'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10024,c_10158])).

tff(c_10336,plain,(
    ! [A_926,B_927,C_928] :
      ( k2_relset_1(A_926,B_927,C_928) = k2_relat_1(C_928)
      | ~ m1_subset_1(C_928,k1_zfmisc_1(k2_zfmisc_1(A_926,B_927))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_10720,plain,(
    ! [A_975,B_976] : k2_relset_1(A_975,B_976,'#skF_2'(A_975,B_976)) = k2_relat_1('#skF_2'(A_975,B_976)) ),
    inference(resolution,[status(thm)],[c_74,c_10336])).

tff(c_10732,plain,(
    ! [A_908] : k2_relat_1('#skF_2'(A_908,'#skF_4')) = k2_relset_1(A_908,'#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10181,c_10720])).

tff(c_10762,plain,(
    ! [A_980] : k2_relset_1(A_980,'#skF_4','#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10181,c_10732])).

tff(c_9740,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9716,c_84])).

tff(c_10769,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_10762,c_9740])).

tff(c_9739,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9716,c_262])).

tff(c_9733,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9716,c_9716,c_6280])).

tff(c_9871,plain,(
    ! [A_893] :
      ( k2_relat_1(k2_funct_1(A_893)) = k1_relat_1(A_893)
      | ~ v2_funct_1(A_893)
      | ~ v1_funct_1(A_893)
      | ~ v1_relat_1(A_893) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_11908,plain,(
    ! [A_1080] :
      ( v1_funct_2(k2_funct_1(A_1080),k1_relat_1(k2_funct_1(A_1080)),k1_relat_1(A_1080))
      | ~ v1_funct_1(k2_funct_1(A_1080))
      | ~ v1_relat_1(k2_funct_1(A_1080))
      | ~ v2_funct_1(A_1080)
      | ~ v1_funct_1(A_1080)
      | ~ v1_relat_1(A_1080) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9871,c_78])).

tff(c_11923,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_9733,c_11908])).

tff(c_11929,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9736,c_9743,c_9742,c_9739,c_11923])).

tff(c_11952,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_11929])).

tff(c_11955,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_11952])).

tff(c_11959,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9736,c_9743,c_11955])).

tff(c_11961,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_11929])).

tff(c_9720,plain,(
    ! [A_17] :
      ( k1_relat_1(A_17) != '#skF_4'
      | A_17 = '#skF_4'
      | ~ v1_relat_1(A_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9716,c_9716,c_6263])).

tff(c_11968,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_11961,c_9720])).

tff(c_11984,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_11968])).

tff(c_11987,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_11984])).

tff(c_11990,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9736,c_9743,c_9742,c_10769,c_11987])).

tff(c_11991,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_11968])).

tff(c_9732,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_4',B_9) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9716,c_9716,c_6267])).

tff(c_9738,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9716,c_263])).

tff(c_9902,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9732,c_9738])).

tff(c_9906,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_9902])).

tff(c_9910,plain,(
    ~ v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_9835,c_9906])).

tff(c_11996,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11991,c_9910])).

tff(c_12005,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9734,c_11996])).

tff(c_12006,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_261])).

tff(c_12090,plain,
    ( k2_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_12082,c_32])).

tff(c_12092,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_12090])).

tff(c_12722,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12720,c_12092])).

tff(c_12747,plain,(
    ! [A_1177,B_1178,C_1179] :
      ( k1_relset_1(A_1177,B_1178,C_1179) = k1_relat_1(C_1179)
      | ~ m1_subset_1(C_1179,k1_zfmisc_1(k2_zfmisc_1(A_1177,B_1178))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_12774,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_12747])).

tff(c_13034,plain,(
    ! [B_1202,A_1203,C_1204] :
      ( k1_xboole_0 = B_1202
      | k1_relset_1(A_1203,B_1202,C_1204) = A_1203
      | ~ v1_funct_2(C_1204,A_1203,B_1202)
      | ~ m1_subset_1(C_1204,k1_zfmisc_1(k2_zfmisc_1(A_1203,B_1202))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_13053,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_13034])).

tff(c_13077,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_12774,c_13053])).

tff(c_13078,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_12722,c_13077])).

tff(c_12091,plain,
    ( k1_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_12082,c_34])).

tff(c_12136,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_12091])).

tff(c_13089,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13078,c_12136])).

tff(c_12007,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_261])).

tff(c_12772,plain,(
    k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) = k1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_12007,c_12747])).

tff(c_13146,plain,(
    ! [B_1207,C_1208,A_1209] :
      ( k1_xboole_0 = B_1207
      | v1_funct_2(C_1208,A_1209,B_1207)
      | k1_relset_1(A_1209,B_1207,C_1208) != A_1209
      | ~ m1_subset_1(C_1208,k1_zfmisc_1(k2_zfmisc_1(A_1209,B_1207))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_13155,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_12007,c_13146])).

tff(c_13177,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12772,c_13155])).

tff(c_13178,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_12006,c_13089,c_13177])).

tff(c_13188,plain,
    ( k2_relat_1('#skF_5') != '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_13178])).

tff(c_13191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12082,c_92,c_86,c_12720,c_13188])).

tff(c_13192,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_12091])).

tff(c_13196,plain,(
    k2_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13192,c_12092])).

tff(c_13193,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_12091])).

tff(c_13216,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13192,c_13193])).

tff(c_13657,plain,(
    ! [A_1262] :
      ( k2_relat_1(k2_funct_1(A_1262)) = k1_relat_1(A_1262)
      | ~ v2_funct_1(A_1262)
      | ~ v1_funct_1(A_1262)
      | ~ v1_relat_1(A_1262) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_12080,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_12007,c_12061])).

tff(c_12099,plain,
    ( k2_relat_1(k2_funct_1('#skF_5')) != k1_xboole_0
    | k2_funct_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12080,c_32])).

tff(c_13290,plain,
    ( k2_relat_1(k2_funct_1('#skF_5')) != '#skF_5'
    | k2_funct_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13192,c_13192,c_12099])).

tff(c_13291,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_13290])).

tff(c_13666,plain,
    ( k1_relat_1('#skF_5') != '#skF_5'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_13657,c_13291])).

tff(c_13673,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12082,c_92,c_86,c_13216,c_13666])).

tff(c_13674,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_13290])).

tff(c_13675,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_13290])).

tff(c_13697,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13674,c_13675])).

tff(c_13698,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13196,c_13697])).

tff(c_13699,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_12090])).

tff(c_13700,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_12090])).

tff(c_13719,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13699,c_13700])).

tff(c_15160,plain,(
    ! [A_1403] :
      ( k1_relat_1(k2_funct_1(A_1403)) = k2_relat_1(A_1403)
      | ~ v2_funct_1(A_1403)
      | ~ v1_funct_1(A_1403)
      | ~ v1_relat_1(A_1403) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_14860,plain,(
    ! [A_1371] :
      ( k1_relat_1(A_1371) != '#skF_5'
      | A_1371 = '#skF_5'
      | ~ v1_relat_1(A_1371) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13699,c_13699,c_34])).

tff(c_14877,plain,
    ( k1_relat_1(k2_funct_1('#skF_5')) != '#skF_5'
    | k2_funct_1('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_12080,c_14860])).

tff(c_15010,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_14877])).

tff(c_15169,plain,
    ( k2_relat_1('#skF_5') != '#skF_5'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_15160,c_15010])).

tff(c_15176,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12082,c_92,c_86,c_13719,c_15169])).

tff(c_15177,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_14877])).

tff(c_14542,plain,(
    ! [A_1352,B_1353,C_1354] :
      ( k2_relset_1(A_1352,B_1353,C_1354) = k2_relat_1(C_1354)
      | ~ m1_subset_1(C_1354,k1_zfmisc_1(k2_zfmisc_1(A_1352,B_1353))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_14561,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_14542])).

tff(c_14571,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_13719,c_14561])).

tff(c_13707,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13699,c_8])).

tff(c_14598,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14571,c_13707])).

tff(c_13705,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_5',B_9) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13699,c_13699,c_20])).

tff(c_14596,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_4',B_9) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14571,c_14571,c_13705])).

tff(c_14267,plain,(
    ! [C_1322,B_1323,A_1324] :
      ( ~ v1_xboole_0(C_1322)
      | ~ m1_subset_1(B_1323,k1_zfmisc_1(C_1322))
      | ~ r2_hidden(A_1324,B_1323) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14293,plain,(
    ! [A_1325,A_1326] :
      ( ~ v1_xboole_0(A_1325)
      | ~ r2_hidden(A_1326,A_1325) ) ),
    inference(resolution,[status(thm)],[c_93,c_14267])).

tff(c_14298,plain,(
    ! [A_1327,B_1328] :
      ( ~ v1_xboole_0(A_1327)
      | r1_tarski(A_1327,B_1328) ) ),
    inference(resolution,[status(thm)],[c_6,c_14293])).

tff(c_14190,plain,(
    ! [A_1318] :
      ( k1_relat_1(k2_funct_1(A_1318)) = k2_relat_1(A_1318)
      | ~ v2_funct_1(A_1318)
      | ~ v1_funct_1(A_1318)
      | ~ v1_relat_1(A_1318) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_13916,plain,(
    ! [A_1286] :
      ( k1_relat_1(A_1286) != '#skF_5'
      | A_1286 = '#skF_5'
      | ~ v1_relat_1(A_1286) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13699,c_13699,c_34])).

tff(c_13933,plain,
    ( k1_relat_1(k2_funct_1('#skF_5')) != '#skF_5'
    | k2_funct_1('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_12080,c_13916])).

tff(c_13939,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_13933])).

tff(c_14199,plain,
    ( k2_relat_1('#skF_5') != '#skF_5'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_14190,c_13939])).

tff(c_14206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12082,c_92,c_86,c_13719,c_14199])).

tff(c_14207,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_13933])).

tff(c_13885,plain,(
    ! [A_1283] :
      ( k2_relat_1(A_1283) != '#skF_5'
      | A_1283 = '#skF_5'
      | ~ v1_relat_1(A_1283) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13699,c_13699,c_32])).

tff(c_13902,plain,
    ( k2_relat_1(k2_funct_1('#skF_5')) != '#skF_5'
    | k2_funct_1('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_12080,c_13885])).

tff(c_13938,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_13902])).

tff(c_14209,plain,(
    k2_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14207,c_13938])).

tff(c_14218,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13719,c_14209])).

tff(c_14219,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_13902])).

tff(c_12027,plain,(
    r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_12007,c_26])).

tff(c_12047,plain,(
    ! [B_1092,A_1093] :
      ( B_1092 = A_1093
      | ~ r1_tarski(B_1092,A_1093)
      | ~ r1_tarski(A_1093,B_1092) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12054,plain,
    ( k2_zfmisc_1('#skF_4','#skF_3') = k2_funct_1('#skF_5')
    | ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_3'),k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_12027,c_12047])).

tff(c_13846,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_3'),k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_12054])).

tff(c_14221,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_3'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14219,c_13846])).

tff(c_14315,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_14298,c_14221])).

tff(c_14750,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14596,c_14315])).

tff(c_14753,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14598,c_14750])).

tff(c_14754,plain,(
    k2_zfmisc_1('#skF_4','#skF_3') = k2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_12054])).

tff(c_15182,plain,(
    k2_zfmisc_1('#skF_4','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15177,c_14754])).

tff(c_13815,plain,(
    ! [B_9,A_8] :
      ( B_9 = '#skF_5'
      | A_8 = '#skF_5'
      | k2_zfmisc_1(A_8,B_9) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13699,c_13699,c_13699,c_16])).

tff(c_15225,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_15182,c_13815])).

tff(c_15228,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_15225])).

tff(c_15249,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15228,c_13707])).

tff(c_13704,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13699,c_13699,c_18])).

tff(c_15246,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15228,c_15228,c_13704])).

tff(c_14887,plain,(
    ! [C_1372,B_1373,A_1374] :
      ( ~ v1_xboole_0(C_1372)
      | ~ m1_subset_1(B_1373,k1_zfmisc_1(C_1372))
      | ~ r2_hidden(A_1374,B_1373) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14911,plain,(
    ! [A_1374] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_1374,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_88,c_14887])).

tff(c_14947,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_14911])).

tff(c_15347,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15246,c_14947])).

tff(c_15350,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15249,c_15347])).

tff(c_15351,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_15225])).

tff(c_15373,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15351,c_13707])).

tff(c_15371,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_3',B_9) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15351,c_15351,c_13705])).

tff(c_15434,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15371,c_14947])).

tff(c_15437,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15373,c_15434])).

tff(c_15439,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_14911])).

tff(c_14913,plain,(
    ! [A_1375,A_1376] :
      ( ~ v1_xboole_0(A_1375)
      | ~ r2_hidden(A_1376,A_1375) ) ),
    inference(resolution,[status(thm)],[c_93,c_14887])).

tff(c_14918,plain,(
    ! [A_1377,B_1378] :
      ( ~ v1_xboole_0(A_1377)
      | r1_tarski(A_1377,B_1378) ) ),
    inference(resolution,[status(thm)],[c_6,c_14913])).

tff(c_12010,plain,(
    ! [A_1087,B_1088] :
      ( r1_tarski(A_1087,B_1088)
      | ~ m1_subset_1(A_1087,k1_zfmisc_1(B_1088)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12021,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_88,c_12010])).

tff(c_12055,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_12021,c_12047])).

tff(c_13793,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_12055])).

tff(c_14938,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_14918,c_13793])).

tff(c_15483,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15439,c_14938])).

tff(c_15484,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_12055])).

tff(c_15525,plain,(
    ! [B_1416,A_1417] :
      ( B_1416 = '#skF_5'
      | A_1417 = '#skF_5'
      | k2_zfmisc_1(A_1417,B_1416) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13699,c_13699,c_13699,c_16])).

tff(c_15535,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_15484,c_15525])).

tff(c_15540,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_15535])).

tff(c_52,plain,(
    ! [A_30] :
      ( v1_funct_2(k1_xboole_0,A_30,k1_xboole_0)
      | k1_xboole_0 = A_30
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_30,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_96,plain,(
    ! [A_30] :
      ( v1_funct_2(k1_xboole_0,A_30,k1_xboole_0)
      | k1_xboole_0 = A_30
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_52])).

tff(c_99,plain,(
    ! [A_30] :
      ( v1_funct_2(k1_xboole_0,A_30,k1_xboole_0)
      | k1_xboole_0 = A_30 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_96])).

tff(c_13703,plain,(
    ! [A_30] :
      ( v1_funct_2('#skF_5',A_30,'#skF_5')
      | A_30 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13699,c_13699,c_13699,c_99])).

tff(c_15544,plain,(
    ! [A_30] :
      ( v1_funct_2('#skF_3',A_30,'#skF_3')
      | A_30 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15540,c_15540,c_15540,c_13703])).

tff(c_15552,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15540,c_13707])).

tff(c_15725,plain,(
    ! [C_1431,B_1432,A_1433] :
      ( ~ v1_xboole_0(C_1431)
      | ~ m1_subset_1(B_1432,k1_zfmisc_1(C_1431))
      | ~ r2_hidden(A_1433,B_1432) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_15767,plain,(
    ! [A_1436,A_1437] :
      ( ~ v1_xboole_0(A_1436)
      | ~ r2_hidden(A_1437,A_1436) ) ),
    inference(resolution,[status(thm)],[c_93,c_15725])).

tff(c_15771,plain,(
    ! [A_1,B_2] :
      ( ~ v1_xboole_0(A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_15767])).

tff(c_15548,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15540,c_15540,c_13704])).

tff(c_15844,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15548,c_15540,c_15548,c_15540,c_12054])).

tff(c_15845,plain,(
    ~ r1_tarski('#skF_3',k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_15844])).

tff(c_15848,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_15771,c_15845])).

tff(c_15852,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15552,c_15848])).

tff(c_15853,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_15844])).

tff(c_15557,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15540,c_12006])).

tff(c_15858,plain,(
    ~ v1_funct_2('#skF_3','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15853,c_15557])).

tff(c_15926,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_15544,c_15858])).

tff(c_15560,plain,(
    v1_funct_2('#skF_3','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15540,c_90])).

tff(c_15945,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15926,c_15926,c_15560])).

tff(c_15927,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15926,c_15926,c_15858])).

tff(c_16056,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15945,c_15927])).

tff(c_16057,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_15535])).

tff(c_16070,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16057,c_13707])).

tff(c_13737,plain,(
    ! [A_1266,B_1267] : m1_subset_1('#skF_2'(A_1266,B_1267),k1_zfmisc_1(k2_zfmisc_1(A_1266,B_1267))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_13746,plain,(
    ! [B_9] : m1_subset_1('#skF_2'('#skF_5',B_9),k1_zfmisc_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13705,c_13737])).

tff(c_16061,plain,(
    ! [B_9] : m1_subset_1('#skF_2'('#skF_4',B_9),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16057,c_16057,c_13746])).

tff(c_16229,plain,(
    ! [C_1469,B_1470,A_1471] :
      ( ~ v1_xboole_0(C_1469)
      | ~ m1_subset_1(B_1470,k1_zfmisc_1(C_1469))
      | ~ r2_hidden(A_1471,B_1470) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16235,plain,(
    ! [A_1471,B_9] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_1471,'#skF_2'('#skF_4',B_9)) ) ),
    inference(resolution,[status(thm)],[c_16061,c_16229])).

tff(c_16298,plain,(
    ! [A_1480,B_1481] : ~ r2_hidden(A_1480,'#skF_2'('#skF_4',B_1481)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16070,c_16235])).

tff(c_16303,plain,(
    ! [B_1481,B_2] : r1_tarski('#skF_2'('#skF_4',B_1481),B_2) ),
    inference(resolution,[status(thm)],[c_6,c_16298])).

tff(c_16271,plain,(
    ! [A_1474,A_1475] :
      ( ~ v1_xboole_0(A_1474)
      | ~ r2_hidden(A_1475,A_1474) ) ),
    inference(resolution,[status(thm)],[c_93,c_16229])).

tff(c_16275,plain,(
    ! [A_1,B_2] :
      ( ~ v1_xboole_0(A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_16271])).

tff(c_16067,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_4',B_9) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16057,c_16057,c_13705])).

tff(c_16333,plain,
    ( k2_funct_1('#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16067,c_16057,c_16067,c_16057,c_12054])).

tff(c_16334,plain,(
    ~ r1_tarski('#skF_4',k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_16333])).

tff(c_16337,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_16275,c_16334])).

tff(c_16341,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16070,c_16337])).

tff(c_16342,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_16333])).

tff(c_16074,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16057,c_12007])).

tff(c_16175,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16067,c_16074])).

tff(c_16233,plain,(
    ! [A_1471] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_1471,k2_funct_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_16175,c_16229])).

tff(c_16254,plain,(
    ! [A_1472] : ~ r2_hidden(A_1472,k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16070,c_16233])).

tff(c_16259,plain,(
    ! [B_2] : r1_tarski(k2_funct_1('#skF_4'),B_2) ),
    inference(resolution,[status(thm)],[c_6,c_16254])).

tff(c_16373,plain,(
    ! [B_1488] : r1_tarski('#skF_4',B_1488) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16342,c_16259])).

tff(c_16415,plain,(
    ! [B_1490] :
      ( B_1490 = '#skF_4'
      | ~ r1_tarski(B_1490,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16373,c_10])).

tff(c_16448,plain,(
    ! [B_1491] : '#skF_2'('#skF_4',B_1491) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_16303,c_16415])).

tff(c_16456,plain,(
    ! [B_1491] : v1_funct_2('#skF_4','#skF_4',B_1491) ),
    inference(superposition,[status(thm),theory(equality)],[c_16448,c_64])).

tff(c_16075,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16057,c_12006])).

tff(c_16347,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16342,c_16075])).

tff(c_16533,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16456,c_16347])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:18:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.77/3.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.85/3.33  
% 8.85/3.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.85/3.33  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 8.85/3.33  
% 8.85/3.33  %Foreground sorts:
% 8.85/3.33  
% 8.85/3.33  
% 8.85/3.33  %Background operators:
% 8.85/3.33  
% 8.85/3.33  
% 8.85/3.33  %Foreground operators:
% 8.85/3.33  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.85/3.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.85/3.33  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.85/3.33  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.85/3.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.85/3.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.85/3.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.85/3.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.85/3.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.85/3.33  tff('#skF_5', type, '#skF_5': $i).
% 8.85/3.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.85/3.33  tff('#skF_3', type, '#skF_3': $i).
% 8.85/3.33  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.85/3.33  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.85/3.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.85/3.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.85/3.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.85/3.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.85/3.33  tff('#skF_4', type, '#skF_4': $i).
% 8.85/3.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.85/3.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.85/3.33  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.85/3.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.85/3.33  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 8.85/3.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.85/3.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.85/3.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.85/3.33  
% 9.17/3.38  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.17/3.38  tff(f_160, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 9.17/3.38  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.17/3.38  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.17/3.38  tff(f_90, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 9.17/3.38  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 9.17/3.38  tff(f_143, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 9.17/3.38  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 9.17/3.38  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.17/3.38  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 9.17/3.38  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.17/3.38  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.17/3.38  tff(f_60, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 9.17/3.38  tff(f_47, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 9.17/3.38  tff(f_49, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 9.17/3.39  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.17/3.39  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.17/3.39  tff(f_133, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_funct_2)).
% 9.17/3.39  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.17/3.39  tff(c_88, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 9.17/3.39  tff(c_12061, plain, (![C_1096, A_1097, B_1098]: (v1_relat_1(C_1096) | ~m1_subset_1(C_1096, k1_zfmisc_1(k2_zfmisc_1(A_1097, B_1098))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.17/3.39  tff(c_12082, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_12061])).
% 9.17/3.39  tff(c_92, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_160])).
% 9.17/3.39  tff(c_86, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_160])).
% 9.17/3.39  tff(c_84, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_160])).
% 9.17/3.39  tff(c_12692, plain, (![A_1172, B_1173, C_1174]: (k2_relset_1(A_1172, B_1173, C_1174)=k2_relat_1(C_1174) | ~m1_subset_1(C_1174, k1_zfmisc_1(k2_zfmisc_1(A_1172, B_1173))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.17/3.39  tff(c_12705, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_12692])).
% 9.17/3.39  tff(c_12720, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_12705])).
% 9.17/3.39  tff(c_44, plain, (![A_20]: (k1_relat_1(k2_funct_1(A_20))=k2_relat_1(A_20) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.17/3.39  tff(c_90, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_160])).
% 9.17/3.39  tff(c_184, plain, (![A_61]: (v1_funct_1(k2_funct_1(A_61)) | ~v1_funct_1(A_61) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.17/3.39  tff(c_82, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 9.17/3.39  tff(c_149, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_82])).
% 9.17/3.39  tff(c_187, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_184, c_149])).
% 9.17/3.39  tff(c_190, plain, (~v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_187])).
% 9.17/3.39  tff(c_235, plain, (![C_74, A_75, B_76]: (v1_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.17/3.39  tff(c_245, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_235])).
% 9.17/3.39  tff(c_260, plain, $false, inference(negUnitSimplification, [status(thm)], [c_190, c_245])).
% 9.17/3.39  tff(c_261, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_82])).
% 9.17/3.39  tff(c_263, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_261])).
% 9.17/3.39  tff(c_347, plain, (![C_97, A_98, B_99]: (v1_relat_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.17/3.39  tff(c_369, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_347])).
% 9.17/3.39  tff(c_912, plain, (![A_163, B_164, C_165]: (k2_relset_1(A_163, B_164, C_165)=k2_relat_1(C_165) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_163, B_164))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.17/3.39  tff(c_925, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_912])).
% 9.17/3.39  tff(c_940, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_925])).
% 9.17/3.39  tff(c_40, plain, (![A_19]: (v1_relat_1(k2_funct_1(A_19)) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.17/3.39  tff(c_262, plain, (v1_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_82])).
% 9.17/3.39  tff(c_626, plain, (![A_133]: (k1_relat_1(k2_funct_1(A_133))=k2_relat_1(A_133) | ~v2_funct_1(A_133) | ~v1_funct_1(A_133) | ~v1_relat_1(A_133))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.17/3.39  tff(c_78, plain, (![A_36]: (v1_funct_2(A_36, k1_relat_1(A_36), k2_relat_1(A_36)) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_143])).
% 9.17/3.39  tff(c_3527, plain, (![A_361]: (v1_funct_2(k2_funct_1(A_361), k2_relat_1(A_361), k2_relat_1(k2_funct_1(A_361))) | ~v1_funct_1(k2_funct_1(A_361)) | ~v1_relat_1(k2_funct_1(A_361)) | ~v2_funct_1(A_361) | ~v1_funct_1(A_361) | ~v1_relat_1(A_361))), inference(superposition, [status(thm), theory('equality')], [c_626, c_78])).
% 9.17/3.39  tff(c_3536, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_940, c_3527])).
% 9.17/3.39  tff(c_3547, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_369, c_92, c_86, c_262, c_3536])).
% 9.17/3.39  tff(c_3573, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_3547])).
% 9.17/3.39  tff(c_3607, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_3573])).
% 9.17/3.39  tff(c_3611, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_369, c_92, c_3607])).
% 9.17/3.39  tff(c_3613, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_3547])).
% 9.17/3.39  tff(c_32, plain, (![A_17]: (k2_relat_1(A_17)!=k1_xboole_0 | k1_xboole_0=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.17/3.39  tff(c_378, plain, (k2_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_369, c_32])).
% 9.17/3.39  tff(c_404, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_378])).
% 9.17/3.39  tff(c_942, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_940, c_404])).
% 9.17/3.39  tff(c_728, plain, (![A_141, B_142, C_143]: (k1_relset_1(A_141, B_142, C_143)=k1_relat_1(C_143) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.17/3.39  tff(c_751, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_728])).
% 9.17/3.39  tff(c_1223, plain, (![B_191, A_192, C_193]: (k1_xboole_0=B_191 | k1_relset_1(A_192, B_191, C_193)=A_192 | ~v1_funct_2(C_193, A_192, B_191) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(A_192, B_191))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.17/3.39  tff(c_1239, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_88, c_1223])).
% 9.17/3.39  tff(c_1261, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_751, c_1239])).
% 9.17/3.39  tff(c_1262, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_942, c_1261])).
% 9.17/3.39  tff(c_42, plain, (![A_20]: (k2_relat_1(k2_funct_1(A_20))=k1_relat_1(A_20) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.17/3.39  tff(c_855, plain, (![A_152]: (m1_subset_1(A_152, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_152), k2_relat_1(A_152)))) | ~v1_funct_1(A_152) | ~v1_relat_1(A_152))), inference(cnfTransformation, [status(thm)], [f_143])).
% 9.17/3.39  tff(c_3841, plain, (![A_387]: (m1_subset_1(k2_funct_1(A_387), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_387)), k1_relat_1(A_387)))) | ~v1_funct_1(k2_funct_1(A_387)) | ~v1_relat_1(k2_funct_1(A_387)) | ~v2_funct_1(A_387) | ~v1_funct_1(A_387) | ~v1_relat_1(A_387))), inference(superposition, [status(thm), theory('equality')], [c_42, c_855])).
% 9.17/3.39  tff(c_3870, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1262, c_3841])).
% 9.17/3.39  tff(c_3892, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_369, c_92, c_86, c_3613, c_262, c_3870])).
% 9.17/3.39  tff(c_3917, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'), '#skF_3'))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_44, c_3892])).
% 9.17/3.39  tff(c_3932, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_369, c_92, c_86, c_940, c_3917])).
% 9.17/3.39  tff(c_3934, plain, $false, inference(negUnitSimplification, [status(thm)], [c_263, c_3932])).
% 9.17/3.39  tff(c_3935, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_378])).
% 9.17/3.39  tff(c_3936, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_378])).
% 9.17/3.39  tff(c_3962, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3935, c_3936])).
% 9.17/3.39  tff(c_4407, plain, (![A_439, B_440, C_441]: (k2_relset_1(A_439, B_440, C_441)=k2_relat_1(C_441) | ~m1_subset_1(C_441, k1_zfmisc_1(k2_zfmisc_1(A_439, B_440))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.17/3.39  tff(c_4423, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_4407])).
% 9.17/3.39  tff(c_4431, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3962, c_84, c_4423])).
% 9.17/3.39  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.17/3.39  tff(c_3950, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3935, c_8])).
% 9.17/3.39  tff(c_4454, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4431, c_3950])).
% 9.17/3.39  tff(c_18, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.17/3.39  tff(c_3947, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3935, c_3935, c_18])).
% 9.17/3.39  tff(c_4450, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4431, c_4431, c_3947])).
% 9.17/3.39  tff(c_4095, plain, (![C_401, B_402, A_403]: (~v1_xboole_0(C_401) | ~m1_subset_1(B_402, k1_zfmisc_1(C_401)) | ~r2_hidden(A_403, B_402))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.17/3.39  tff(c_4116, plain, (![A_403]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_403, '#skF_5'))), inference(resolution, [status(thm)], [c_88, c_4095])).
% 9.17/3.39  tff(c_4136, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_4116])).
% 9.17/3.39  tff(c_4595, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4450, c_4136])).
% 9.17/3.39  tff(c_4598, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4454, c_4595])).
% 9.17/3.39  tff(c_4600, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_4116])).
% 9.17/3.39  tff(c_22, plain, (![A_10]: (k2_subset_1(A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.17/3.39  tff(c_24, plain, (![A_11]: (m1_subset_1(k2_subset_1(A_11), k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.17/3.39  tff(c_93, plain, (![A_11]: (m1_subset_1(A_11, k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24])).
% 9.17/3.39  tff(c_4118, plain, (![A_404, A_405]: (~v1_xboole_0(A_404) | ~r2_hidden(A_405, A_404))), inference(resolution, [status(thm)], [c_93, c_4095])).
% 9.17/3.39  tff(c_4122, plain, (![A_1, B_2]: (~v1_xboole_0(A_1) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_4118])).
% 9.17/3.39  tff(c_264, plain, (![A_77, B_78]: (r1_tarski(A_77, B_78) | ~m1_subset_1(A_77, k1_zfmisc_1(B_78)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.17/3.39  tff(c_271, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_88, c_264])).
% 9.17/3.39  tff(c_4035, plain, (![B_395, A_396]: (B_395=A_396 | ~r1_tarski(B_395, A_396) | ~r1_tarski(A_396, B_395))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.17/3.39  tff(c_4049, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_271, c_4035])).
% 9.17/3.39  tff(c_4626, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_4049])).
% 9.17/3.39  tff(c_4640, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_4122, c_4626])).
% 9.17/3.39  tff(c_4644, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4600, c_4640])).
% 9.17/3.39  tff(c_4645, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_4049])).
% 9.17/3.39  tff(c_16, plain, (![B_9, A_8]: (k1_xboole_0=B_9 | k1_xboole_0=A_8 | k2_zfmisc_1(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.17/3.39  tff(c_5059, plain, (![B_493, A_494]: (B_493='#skF_5' | A_494='#skF_5' | k2_zfmisc_1(A_494, B_493)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3935, c_3935, c_3935, c_16])).
% 9.17/3.39  tff(c_5069, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_4645, c_5059])).
% 9.17/3.39  tff(c_5101, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_5069])).
% 9.17/3.39  tff(c_34, plain, (![A_17]: (k1_relat_1(A_17)!=k1_xboole_0 | k1_xboole_0=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.17/3.39  tff(c_377, plain, (k1_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_369, c_34])).
% 9.17/3.39  tff(c_379, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_377])).
% 9.17/3.39  tff(c_3938, plain, (k1_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3935, c_379])).
% 9.17/3.39  tff(c_5125, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5101, c_5101, c_3938])).
% 9.17/3.39  tff(c_20, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.17/3.39  tff(c_304, plain, (![A_87, B_88]: (m1_subset_1('#skF_2'(A_87, B_88), k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.17/3.39  tff(c_321, plain, (![B_91]: (m1_subset_1('#skF_2'(k1_xboole_0, B_91), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_304])).
% 9.17/3.39  tff(c_26, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.17/3.39  tff(c_325, plain, (![B_91]: (r1_tarski('#skF_2'(k1_xboole_0, B_91), k1_xboole_0))), inference(resolution, [status(thm)], [c_321, c_26])).
% 9.17/3.39  tff(c_3940, plain, (![B_91]: (r1_tarski('#skF_2'('#skF_5', B_91), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_3935, c_3935, c_325])).
% 9.17/3.39  tff(c_4605, plain, (![A_453]: (~r2_hidden(A_453, '#skF_5'))), inference(splitRight, [status(thm)], [c_4116])).
% 9.17/3.39  tff(c_4612, plain, (![B_454]: (r1_tarski('#skF_5', B_454))), inference(resolution, [status(thm)], [c_6, c_4605])).
% 9.17/3.39  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.17/3.39  tff(c_4745, plain, (![B_463]: (B_463='#skF_5' | ~r1_tarski(B_463, '#skF_5'))), inference(resolution, [status(thm)], [c_4612, c_10])).
% 9.17/3.39  tff(c_4767, plain, (![B_91]: ('#skF_2'('#skF_5', B_91)='#skF_5')), inference(resolution, [status(thm)], [c_3940, c_4745])).
% 9.17/3.39  tff(c_5313, plain, (![B_507]: ('#skF_2'('#skF_3', B_507)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5101, c_5101, c_4767])).
% 9.17/3.39  tff(c_64, plain, (![A_33, B_34]: (v1_funct_2('#skF_2'(A_33, B_34), A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.17/3.39  tff(c_5397, plain, (![B_510]: (v1_funct_2('#skF_3', '#skF_3', B_510))), inference(superposition, [status(thm), theory('equality')], [c_5313, c_64])).
% 9.17/3.39  tff(c_5128, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5101, c_3935])).
% 9.17/3.39  tff(c_60, plain, (![B_31, C_32]: (k1_relset_1(k1_xboole_0, B_31, C_32)=k1_xboole_0 | ~v1_funct_2(C_32, k1_xboole_0, B_31) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_31))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.17/3.39  tff(c_94, plain, (![B_31, C_32]: (k1_relset_1(k1_xboole_0, B_31, C_32)=k1_xboole_0 | ~v1_funct_2(C_32, k1_xboole_0, B_31) | ~m1_subset_1(C_32, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_60])).
% 9.17/3.39  tff(c_5267, plain, (![B_31, C_32]: (k1_relset_1('#skF_3', B_31, C_32)='#skF_3' | ~v1_funct_2(C_32, '#skF_3', B_31) | ~m1_subset_1(C_32, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_5128, c_5128, c_5128, c_5128, c_94])).
% 9.17/3.39  tff(c_5399, plain, (![B_510]: (k1_relset_1('#skF_3', B_510, '#skF_3')='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_5397, c_5267])).
% 9.17/3.39  tff(c_5402, plain, (![B_510]: (k1_relset_1('#skF_3', B_510, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_5399])).
% 9.17/3.39  tff(c_4891, plain, (![A_472, B_473, C_474]: (k1_relset_1(A_472, B_473, C_474)=k1_relat_1(C_474) | ~m1_subset_1(C_474, k1_zfmisc_1(k2_zfmisc_1(A_472, B_473))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.17/3.39  tff(c_5022, plain, (![C_484]: (k1_relset_1('#skF_3', '#skF_4', C_484)=k1_relat_1(C_484) | ~m1_subset_1(C_484, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_4645, c_4891])).
% 9.17/3.39  tff(c_5032, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_93, c_5022])).
% 9.17/3.39  tff(c_5103, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5101, c_5101, c_5032])).
% 9.17/3.39  tff(c_5559, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5402, c_5103])).
% 9.17/3.39  tff(c_5560, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5125, c_5559])).
% 9.17/3.39  tff(c_5561, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_5069])).
% 9.17/3.39  tff(c_5586, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5561, c_5561, c_3938])).
% 9.17/3.39  tff(c_5820, plain, (![B_538]: ('#skF_2'('#skF_4', B_538)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5561, c_5561, c_4767])).
% 9.17/3.39  tff(c_5902, plain, (![B_540]: (v1_funct_2('#skF_4', '#skF_4', B_540))), inference(superposition, [status(thm), theory('equality')], [c_5820, c_64])).
% 9.17/3.39  tff(c_5589, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5561, c_3935])).
% 9.17/3.39  tff(c_5808, plain, (![B_31, C_32]: (k1_relset_1('#skF_4', B_31, C_32)='#skF_4' | ~v1_funct_2(C_32, '#skF_4', B_31) | ~m1_subset_1(C_32, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_5589, c_5589, c_5589, c_5589, c_94])).
% 9.17/3.39  tff(c_5904, plain, (![B_540]: (k1_relset_1('#skF_4', B_540, '#skF_4')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_5902, c_5808])).
% 9.17/3.39  tff(c_5907, plain, (![B_540]: (k1_relset_1('#skF_4', B_540, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_5904])).
% 9.17/3.39  tff(c_5574, plain, (![B_91]: ('#skF_2'('#skF_4', B_91)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5561, c_5561, c_4767])).
% 9.17/3.39  tff(c_74, plain, (![A_33, B_34]: (m1_subset_1('#skF_2'(A_33, B_34), k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.17/3.39  tff(c_6237, plain, (![A_574, B_575]: (k1_relset_1(A_574, B_575, '#skF_2'(A_574, B_575))=k1_relat_1('#skF_2'(A_574, B_575)))), inference(resolution, [status(thm)], [c_74, c_4891])).
% 9.17/3.39  tff(c_6249, plain, (![B_91]: (k1_relat_1('#skF_2'('#skF_4', B_91))=k1_relset_1('#skF_4', B_91, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5574, c_6237])).
% 9.17/3.39  tff(c_6253, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5907, c_5574, c_6249])).
% 9.17/3.39  tff(c_6255, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5586, c_6253])).
% 9.17/3.39  tff(c_6256, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_377])).
% 9.17/3.39  tff(c_6257, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_377])).
% 9.17/3.39  tff(c_6280, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_6256, c_6257])).
% 9.17/3.39  tff(c_6788, plain, (![A_635, B_636, C_637]: (k1_relset_1(A_635, B_636, C_637)=k1_relat_1(C_637) | ~m1_subset_1(C_637, k1_zfmisc_1(k2_zfmisc_1(A_635, B_636))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.17/3.39  tff(c_6804, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_6788])).
% 9.17/3.39  tff(c_6812, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_6280, c_6804])).
% 9.17/3.39  tff(c_62, plain, (![B_31, A_30, C_32]: (k1_xboole_0=B_31 | k1_relset_1(A_30, B_31, C_32)=A_30 | ~v1_funct_2(C_32, A_30, B_31) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.17/3.39  tff(c_6952, plain, (![B_649, A_650, C_651]: (B_649='#skF_5' | k1_relset_1(A_650, B_649, C_651)=A_650 | ~v1_funct_2(C_651, A_650, B_649) | ~m1_subset_1(C_651, k1_zfmisc_1(k2_zfmisc_1(A_650, B_649))))), inference(demodulation, [status(thm), theory('equality')], [c_6256, c_62])).
% 9.17/3.39  tff(c_6971, plain, ('#skF_5'='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_88, c_6952])).
% 9.17/3.39  tff(c_6984, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_6812, c_6971])).
% 9.17/3.39  tff(c_6986, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_6984])).
% 9.17/3.39  tff(c_6269, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6256, c_8])).
% 9.17/3.39  tff(c_7010, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6986, c_6269])).
% 9.17/3.39  tff(c_6267, plain, (![B_9]: (k2_zfmisc_1('#skF_5', B_9)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6256, c_6256, c_20])).
% 9.17/3.39  tff(c_7008, plain, (![B_9]: (k2_zfmisc_1('#skF_3', B_9)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6986, c_6986, c_6267])).
% 9.17/3.39  tff(c_6481, plain, (![C_599, B_600, A_601]: (~v1_xboole_0(C_599) | ~m1_subset_1(B_600, k1_zfmisc_1(C_599)) | ~r2_hidden(A_601, B_600))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.17/3.39  tff(c_6502, plain, (![A_601]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_601, '#skF_5'))), inference(resolution, [status(thm)], [c_88, c_6481])).
% 9.17/3.39  tff(c_6531, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_6502])).
% 9.17/3.39  tff(c_7143, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7008, c_6531])).
% 9.17/3.39  tff(c_7146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7010, c_7143])).
% 9.17/3.39  tff(c_7147, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_6984])).
% 9.17/3.39  tff(c_7172, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7147, c_6269])).
% 9.17/3.39  tff(c_6266, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6256, c_6256, c_18])).
% 9.17/3.39  tff(c_7169, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7147, c_7147, c_6266])).
% 9.17/3.39  tff(c_7280, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7169, c_6531])).
% 9.17/3.39  tff(c_7283, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7172, c_7280])).
% 9.17/3.39  tff(c_7285, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_6502])).
% 9.17/3.39  tff(c_6504, plain, (![A_602, A_603]: (~v1_xboole_0(A_602) | ~r2_hidden(A_603, A_602))), inference(resolution, [status(thm)], [c_93, c_6481])).
% 9.17/3.39  tff(c_6509, plain, (![A_604, B_605]: (~v1_xboole_0(A_604) | r1_tarski(A_604, B_605))), inference(resolution, [status(thm)], [c_6, c_6504])).
% 9.17/3.39  tff(c_6333, plain, (![B_582, A_583]: (B_582=A_583 | ~r1_tarski(B_582, A_583) | ~r1_tarski(A_583, B_582))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.17/3.39  tff(c_6347, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_271, c_6333])).
% 9.17/3.39  tff(c_6367, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_6347])).
% 9.17/3.39  tff(c_6528, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_6509, c_6367])).
% 9.17/3.39  tff(c_7320, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7285, c_6528])).
% 9.17/3.39  tff(c_7321, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_6347])).
% 9.17/3.39  tff(c_7471, plain, (![B_686, A_687]: (B_686='#skF_5' | A_687='#skF_5' | k2_zfmisc_1(A_687, B_686)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6256, c_6256, c_6256, c_16])).
% 9.17/3.39  tff(c_7481, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_7321, c_7471])).
% 9.17/3.39  tff(c_7486, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_7481])).
% 9.17/3.39  tff(c_7503, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7486, c_6269])).
% 9.17/3.39  tff(c_7502, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7486, c_7486, c_6280])).
% 9.17/3.39  tff(c_7505, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7486, c_369])).
% 9.17/3.39  tff(c_7512, plain, (v1_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7486, c_92])).
% 9.17/3.39  tff(c_7511, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7486, c_86])).
% 9.17/3.39  tff(c_7508, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7486, c_262])).
% 9.17/3.39  tff(c_7667, plain, (![A_702]: (k2_relat_1(k2_funct_1(A_702))=k1_relat_1(A_702) | ~v2_funct_1(A_702) | ~v1_funct_1(A_702) | ~v1_relat_1(A_702))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.17/3.39  tff(c_9522, plain, (![A_876]: (v1_funct_2(k2_funct_1(A_876), k1_relat_1(k2_funct_1(A_876)), k1_relat_1(A_876)) | ~v1_funct_1(k2_funct_1(A_876)) | ~v1_relat_1(k2_funct_1(A_876)) | ~v2_funct_1(A_876) | ~v1_funct_1(A_876) | ~v1_relat_1(A_876))), inference(superposition, [status(thm), theory('equality')], [c_7667, c_78])).
% 9.17/3.39  tff(c_9537, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7502, c_9522])).
% 9.17/3.39  tff(c_9543, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7505, c_7512, c_7511, c_7508, c_9537])).
% 9.17/3.39  tff(c_9624, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_9543])).
% 9.17/3.39  tff(c_9627, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_9624])).
% 9.17/3.39  tff(c_9631, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7505, c_7512, c_9627])).
% 9.17/3.39  tff(c_9633, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_9543])).
% 9.17/3.39  tff(c_6264, plain, (![A_17]: (k2_relat_1(A_17)!='#skF_5' | A_17='#skF_5' | ~v1_relat_1(A_17))), inference(demodulation, [status(thm), theory('equality')], [c_6256, c_6256, c_32])).
% 9.17/3.39  tff(c_7488, plain, (![A_17]: (k2_relat_1(A_17)!='#skF_3' | A_17='#skF_3' | ~v1_relat_1(A_17))), inference(demodulation, [status(thm), theory('equality')], [c_7486, c_7486, c_6264])).
% 9.17/3.39  tff(c_9641, plain, (k2_relat_1(k2_funct_1('#skF_3'))!='#skF_3' | k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_9633, c_7488])).
% 9.17/3.39  tff(c_9676, plain, (k2_relat_1(k2_funct_1('#skF_3'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_9641])).
% 9.17/3.39  tff(c_9684, plain, (k1_relat_1('#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_42, c_9676])).
% 9.17/3.39  tff(c_9687, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7505, c_7512, c_7511, c_7502, c_9684])).
% 9.17/3.39  tff(c_9688, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_9641])).
% 9.17/3.39  tff(c_6263, plain, (![A_17]: (k1_relat_1(A_17)!='#skF_5' | A_17='#skF_5' | ~v1_relat_1(A_17))), inference(demodulation, [status(thm), theory('equality')], [c_6256, c_6256, c_34])).
% 9.17/3.39  tff(c_7489, plain, (![A_17]: (k1_relat_1(A_17)!='#skF_3' | A_17='#skF_3' | ~v1_relat_1(A_17))), inference(demodulation, [status(thm), theory('equality')], [c_7486, c_7486, c_6263])).
% 9.17/3.39  tff(c_9640, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_3' | k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_9633, c_7489])).
% 9.17/3.39  tff(c_9653, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_9640])).
% 9.17/3.39  tff(c_9690, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9688, c_9653])).
% 9.17/3.39  tff(c_9700, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7502, c_9690])).
% 9.17/3.39  tff(c_9701, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_9640])).
% 9.17/3.39  tff(c_7522, plain, (![C_688, B_689, A_690]: (~v1_xboole_0(C_688) | ~m1_subset_1(B_689, k1_zfmisc_1(C_688)) | ~r2_hidden(A_690, B_689))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.17/3.39  tff(c_7589, plain, (![A_693, A_694]: (~v1_xboole_0(A_693) | ~r2_hidden(A_694, A_693))), inference(resolution, [status(thm)], [c_93, c_7522])).
% 9.17/3.39  tff(c_7593, plain, (![A_1, B_2]: (~v1_xboole_0(A_1) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_7589])).
% 9.17/3.39  tff(c_28, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.17/3.39  tff(c_7500, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7486, c_7486, c_6266])).
% 9.17/3.39  tff(c_7507, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_7486, c_263])).
% 9.17/3.39  tff(c_7631, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7500, c_7507])).
% 9.17/3.39  tff(c_7635, plain, (~r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_28, c_7631])).
% 9.17/3.39  tff(c_7639, plain, (~v1_xboole_0(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_7593, c_7635])).
% 9.17/3.39  tff(c_9706, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9701, c_7639])).
% 9.17/3.39  tff(c_9715, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7503, c_9706])).
% 9.17/3.39  tff(c_9716, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_7481])).
% 9.17/3.39  tff(c_9734, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9716, c_6269])).
% 9.17/3.39  tff(c_9736, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9716, c_369])).
% 9.17/3.39  tff(c_9743, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9716, c_92])).
% 9.17/3.39  tff(c_9742, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9716, c_86])).
% 9.17/3.39  tff(c_310, plain, (![A_8]: (m1_subset_1('#skF_2'(A_8, k1_xboole_0), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_304])).
% 9.17/3.39  tff(c_6262, plain, (![A_8]: (m1_subset_1('#skF_2'(A_8, '#skF_5'), k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_6256, c_6256, c_310])).
% 9.17/3.39  tff(c_9993, plain, (![A_904]: (m1_subset_1('#skF_2'(A_904, '#skF_4'), k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_9716, c_9716, c_6262])).
% 9.17/3.39  tff(c_30, plain, (![C_16, B_15, A_14]: (~v1_xboole_0(C_16) | ~m1_subset_1(B_15, k1_zfmisc_1(C_16)) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.17/3.39  tff(c_9995, plain, (![A_14, A_904]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_14, '#skF_2'(A_904, '#skF_4')))), inference(resolution, [status(thm)], [c_9993, c_30])).
% 9.17/3.39  tff(c_10019, plain, (![A_907, A_908]: (~r2_hidden(A_907, '#skF_2'(A_908, '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_9734, c_9995])).
% 9.17/3.39  tff(c_10024, plain, (![A_908, B_2]: (r1_tarski('#skF_2'(A_908, '#skF_4'), B_2))), inference(resolution, [status(thm)], [c_6, c_10019])).
% 9.17/3.39  tff(c_9749, plain, (![C_881, B_882, A_883]: (~v1_xboole_0(C_881) | ~m1_subset_1(B_882, k1_zfmisc_1(C_881)) | ~r2_hidden(A_883, B_882))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.17/3.39  tff(c_9831, plain, (![A_887, A_888]: (~v1_xboole_0(A_887) | ~r2_hidden(A_888, A_887))), inference(resolution, [status(thm)], [c_93, c_9749])).
% 9.17/3.39  tff(c_9835, plain, (![A_1, B_2]: (~v1_xboole_0(A_1) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_9831])).
% 9.17/3.39  tff(c_314, plain, (![A_87, B_88]: (r1_tarski('#skF_2'(A_87, B_88), k2_zfmisc_1(A_87, B_88)))), inference(resolution, [status(thm)], [c_304, c_26])).
% 9.17/3.39  tff(c_7334, plain, (r1_tarski('#skF_2'('#skF_3', '#skF_4'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7321, c_314])).
% 9.17/3.39  tff(c_7367, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_5' | ~r1_tarski('#skF_5', '#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_7334, c_10])).
% 9.17/3.39  tff(c_10065, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9716, c_9716, c_7367])).
% 9.17/3.39  tff(c_10066, plain, (~r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_10065])).
% 9.17/3.39  tff(c_10069, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_9835, c_10066])).
% 9.17/3.39  tff(c_10073, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9734, c_10069])).
% 9.17/3.39  tff(c_10074, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_10065])).
% 9.17/3.39  tff(c_10138, plain, (![B_916]: (r1_tarski('#skF_4', B_916))), inference(superposition, [status(thm), theory('equality')], [c_10074, c_10024])).
% 9.17/3.39  tff(c_10158, plain, (![B_917]: (B_917='#skF_4' | ~r1_tarski(B_917, '#skF_4'))), inference(resolution, [status(thm)], [c_10138, c_10])).
% 9.17/3.39  tff(c_10181, plain, (![A_908]: ('#skF_2'(A_908, '#skF_4')='#skF_4')), inference(resolution, [status(thm)], [c_10024, c_10158])).
% 9.17/3.39  tff(c_10336, plain, (![A_926, B_927, C_928]: (k2_relset_1(A_926, B_927, C_928)=k2_relat_1(C_928) | ~m1_subset_1(C_928, k1_zfmisc_1(k2_zfmisc_1(A_926, B_927))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.17/3.39  tff(c_10720, plain, (![A_975, B_976]: (k2_relset_1(A_975, B_976, '#skF_2'(A_975, B_976))=k2_relat_1('#skF_2'(A_975, B_976)))), inference(resolution, [status(thm)], [c_74, c_10336])).
% 9.17/3.39  tff(c_10732, plain, (![A_908]: (k2_relat_1('#skF_2'(A_908, '#skF_4'))=k2_relset_1(A_908, '#skF_4', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_10181, c_10720])).
% 9.17/3.39  tff(c_10762, plain, (![A_980]: (k2_relset_1(A_980, '#skF_4', '#skF_4')=k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10181, c_10732])).
% 9.17/3.39  tff(c_9740, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9716, c_84])).
% 9.17/3.39  tff(c_10769, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_10762, c_9740])).
% 9.17/3.39  tff(c_9739, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9716, c_262])).
% 9.17/3.39  tff(c_9733, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9716, c_9716, c_6280])).
% 9.17/3.39  tff(c_9871, plain, (![A_893]: (k2_relat_1(k2_funct_1(A_893))=k1_relat_1(A_893) | ~v2_funct_1(A_893) | ~v1_funct_1(A_893) | ~v1_relat_1(A_893))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.17/3.39  tff(c_11908, plain, (![A_1080]: (v1_funct_2(k2_funct_1(A_1080), k1_relat_1(k2_funct_1(A_1080)), k1_relat_1(A_1080)) | ~v1_funct_1(k2_funct_1(A_1080)) | ~v1_relat_1(k2_funct_1(A_1080)) | ~v2_funct_1(A_1080) | ~v1_funct_1(A_1080) | ~v1_relat_1(A_1080))), inference(superposition, [status(thm), theory('equality')], [c_9871, c_78])).
% 9.17/3.39  tff(c_11923, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_9733, c_11908])).
% 9.17/3.39  tff(c_11929, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9736, c_9743, c_9742, c_9739, c_11923])).
% 9.17/3.39  tff(c_11952, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_11929])).
% 9.17/3.39  tff(c_11955, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_11952])).
% 9.17/3.39  tff(c_11959, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9736, c_9743, c_11955])).
% 9.17/3.39  tff(c_11961, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_11929])).
% 9.17/3.39  tff(c_9720, plain, (![A_17]: (k1_relat_1(A_17)!='#skF_4' | A_17='#skF_4' | ~v1_relat_1(A_17))), inference(demodulation, [status(thm), theory('equality')], [c_9716, c_9716, c_6263])).
% 9.17/3.39  tff(c_11968, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_11961, c_9720])).
% 9.17/3.39  tff(c_11984, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_11968])).
% 9.17/3.39  tff(c_11987, plain, (k2_relat_1('#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_44, c_11984])).
% 9.17/3.39  tff(c_11990, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9736, c_9743, c_9742, c_10769, c_11987])).
% 9.17/3.39  tff(c_11991, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_11968])).
% 9.17/3.39  tff(c_9732, plain, (![B_9]: (k2_zfmisc_1('#skF_4', B_9)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9716, c_9716, c_6267])).
% 9.17/3.39  tff(c_9738, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_9716, c_263])).
% 9.17/3.39  tff(c_9902, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9732, c_9738])).
% 9.17/3.39  tff(c_9906, plain, (~r1_tarski(k2_funct_1('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_28, c_9902])).
% 9.17/3.39  tff(c_9910, plain, (~v1_xboole_0(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_9835, c_9906])).
% 9.17/3.39  tff(c_11996, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11991, c_9910])).
% 9.17/3.39  tff(c_12005, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9734, c_11996])).
% 9.17/3.39  tff(c_12006, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_261])).
% 9.17/3.39  tff(c_12090, plain, (k2_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_12082, c_32])).
% 9.17/3.39  tff(c_12092, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_12090])).
% 9.17/3.39  tff(c_12722, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12720, c_12092])).
% 9.17/3.39  tff(c_12747, plain, (![A_1177, B_1178, C_1179]: (k1_relset_1(A_1177, B_1178, C_1179)=k1_relat_1(C_1179) | ~m1_subset_1(C_1179, k1_zfmisc_1(k2_zfmisc_1(A_1177, B_1178))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.17/3.39  tff(c_12774, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_12747])).
% 9.17/3.39  tff(c_13034, plain, (![B_1202, A_1203, C_1204]: (k1_xboole_0=B_1202 | k1_relset_1(A_1203, B_1202, C_1204)=A_1203 | ~v1_funct_2(C_1204, A_1203, B_1202) | ~m1_subset_1(C_1204, k1_zfmisc_1(k2_zfmisc_1(A_1203, B_1202))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.17/3.39  tff(c_13053, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_88, c_13034])).
% 9.17/3.39  tff(c_13077, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_12774, c_13053])).
% 9.17/3.39  tff(c_13078, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_12722, c_13077])).
% 9.17/3.39  tff(c_12091, plain, (k1_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_12082, c_34])).
% 9.17/3.39  tff(c_12136, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_12091])).
% 9.17/3.39  tff(c_13089, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13078, c_12136])).
% 9.17/3.39  tff(c_12007, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_261])).
% 9.17/3.39  tff(c_12772, plain, (k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))=k1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_12007, c_12747])).
% 9.17/3.39  tff(c_13146, plain, (![B_1207, C_1208, A_1209]: (k1_xboole_0=B_1207 | v1_funct_2(C_1208, A_1209, B_1207) | k1_relset_1(A_1209, B_1207, C_1208)!=A_1209 | ~m1_subset_1(C_1208, k1_zfmisc_1(k2_zfmisc_1(A_1209, B_1207))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.17/3.39  tff(c_13155, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))!='#skF_4'), inference(resolution, [status(thm)], [c_12007, c_13146])).
% 9.17/3.39  tff(c_13177, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12772, c_13155])).
% 9.17/3.39  tff(c_13178, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_12006, c_13089, c_13177])).
% 9.17/3.39  tff(c_13188, plain, (k2_relat_1('#skF_5')!='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_44, c_13178])).
% 9.17/3.39  tff(c_13191, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12082, c_92, c_86, c_12720, c_13188])).
% 9.17/3.39  tff(c_13192, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_12091])).
% 9.17/3.39  tff(c_13196, plain, (k2_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_13192, c_12092])).
% 9.17/3.39  tff(c_13193, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_12091])).
% 9.17/3.39  tff(c_13216, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_13192, c_13193])).
% 9.17/3.39  tff(c_13657, plain, (![A_1262]: (k2_relat_1(k2_funct_1(A_1262))=k1_relat_1(A_1262) | ~v2_funct_1(A_1262) | ~v1_funct_1(A_1262) | ~v1_relat_1(A_1262))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.17/3.39  tff(c_12080, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_12007, c_12061])).
% 9.17/3.39  tff(c_12099, plain, (k2_relat_1(k2_funct_1('#skF_5'))!=k1_xboole_0 | k2_funct_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_12080, c_32])).
% 9.17/3.39  tff(c_13290, plain, (k2_relat_1(k2_funct_1('#skF_5'))!='#skF_5' | k2_funct_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_13192, c_13192, c_12099])).
% 9.17/3.39  tff(c_13291, plain, (k2_relat_1(k2_funct_1('#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_13290])).
% 9.17/3.39  tff(c_13666, plain, (k1_relat_1('#skF_5')!='#skF_5' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_13657, c_13291])).
% 9.17/3.39  tff(c_13673, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12082, c_92, c_86, c_13216, c_13666])).
% 9.17/3.39  tff(c_13674, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_13290])).
% 9.17/3.39  tff(c_13675, plain, (k2_relat_1(k2_funct_1('#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_13290])).
% 9.17/3.39  tff(c_13697, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_13674, c_13675])).
% 9.17/3.39  tff(c_13698, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13196, c_13697])).
% 9.17/3.39  tff(c_13699, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_12090])).
% 9.17/3.39  tff(c_13700, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_12090])).
% 9.17/3.39  tff(c_13719, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_13699, c_13700])).
% 9.17/3.39  tff(c_15160, plain, (![A_1403]: (k1_relat_1(k2_funct_1(A_1403))=k2_relat_1(A_1403) | ~v2_funct_1(A_1403) | ~v1_funct_1(A_1403) | ~v1_relat_1(A_1403))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.17/3.39  tff(c_14860, plain, (![A_1371]: (k1_relat_1(A_1371)!='#skF_5' | A_1371='#skF_5' | ~v1_relat_1(A_1371))), inference(demodulation, [status(thm), theory('equality')], [c_13699, c_13699, c_34])).
% 9.17/3.39  tff(c_14877, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_5' | k2_funct_1('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_12080, c_14860])).
% 9.17/3.39  tff(c_15010, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_14877])).
% 9.17/3.39  tff(c_15169, plain, (k2_relat_1('#skF_5')!='#skF_5' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_15160, c_15010])).
% 9.17/3.39  tff(c_15176, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12082, c_92, c_86, c_13719, c_15169])).
% 9.17/3.39  tff(c_15177, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_14877])).
% 9.17/3.39  tff(c_14542, plain, (![A_1352, B_1353, C_1354]: (k2_relset_1(A_1352, B_1353, C_1354)=k2_relat_1(C_1354) | ~m1_subset_1(C_1354, k1_zfmisc_1(k2_zfmisc_1(A_1352, B_1353))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.17/3.39  tff(c_14561, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_14542])).
% 9.17/3.39  tff(c_14571, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_13719, c_14561])).
% 9.17/3.39  tff(c_13707, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_13699, c_8])).
% 9.17/3.39  tff(c_14598, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14571, c_13707])).
% 9.17/3.39  tff(c_13705, plain, (![B_9]: (k2_zfmisc_1('#skF_5', B_9)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_13699, c_13699, c_20])).
% 9.17/3.39  tff(c_14596, plain, (![B_9]: (k2_zfmisc_1('#skF_4', B_9)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14571, c_14571, c_13705])).
% 9.17/3.39  tff(c_14267, plain, (![C_1322, B_1323, A_1324]: (~v1_xboole_0(C_1322) | ~m1_subset_1(B_1323, k1_zfmisc_1(C_1322)) | ~r2_hidden(A_1324, B_1323))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.17/3.39  tff(c_14293, plain, (![A_1325, A_1326]: (~v1_xboole_0(A_1325) | ~r2_hidden(A_1326, A_1325))), inference(resolution, [status(thm)], [c_93, c_14267])).
% 9.17/3.39  tff(c_14298, plain, (![A_1327, B_1328]: (~v1_xboole_0(A_1327) | r1_tarski(A_1327, B_1328))), inference(resolution, [status(thm)], [c_6, c_14293])).
% 9.17/3.39  tff(c_14190, plain, (![A_1318]: (k1_relat_1(k2_funct_1(A_1318))=k2_relat_1(A_1318) | ~v2_funct_1(A_1318) | ~v1_funct_1(A_1318) | ~v1_relat_1(A_1318))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.17/3.39  tff(c_13916, plain, (![A_1286]: (k1_relat_1(A_1286)!='#skF_5' | A_1286='#skF_5' | ~v1_relat_1(A_1286))), inference(demodulation, [status(thm), theory('equality')], [c_13699, c_13699, c_34])).
% 9.17/3.39  tff(c_13933, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_5' | k2_funct_1('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_12080, c_13916])).
% 9.17/3.39  tff(c_13939, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_13933])).
% 9.17/3.39  tff(c_14199, plain, (k2_relat_1('#skF_5')!='#skF_5' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_14190, c_13939])).
% 9.17/3.39  tff(c_14206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12082, c_92, c_86, c_13719, c_14199])).
% 9.17/3.39  tff(c_14207, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_13933])).
% 9.17/3.39  tff(c_13885, plain, (![A_1283]: (k2_relat_1(A_1283)!='#skF_5' | A_1283='#skF_5' | ~v1_relat_1(A_1283))), inference(demodulation, [status(thm), theory('equality')], [c_13699, c_13699, c_32])).
% 9.17/3.39  tff(c_13902, plain, (k2_relat_1(k2_funct_1('#skF_5'))!='#skF_5' | k2_funct_1('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_12080, c_13885])).
% 9.17/3.39  tff(c_13938, plain, (k2_relat_1(k2_funct_1('#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_13902])).
% 9.17/3.39  tff(c_14209, plain, (k2_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_14207, c_13938])).
% 9.17/3.39  tff(c_14218, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13719, c_14209])).
% 9.17/3.39  tff(c_14219, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_13902])).
% 9.17/3.39  tff(c_12027, plain, (r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_12007, c_26])).
% 9.17/3.39  tff(c_12047, plain, (![B_1092, A_1093]: (B_1092=A_1093 | ~r1_tarski(B_1092, A_1093) | ~r1_tarski(A_1093, B_1092))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.17/3.39  tff(c_12054, plain, (k2_zfmisc_1('#skF_4', '#skF_3')=k2_funct_1('#skF_5') | ~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_3'), k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_12027, c_12047])).
% 9.17/3.39  tff(c_13846, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_3'), k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_12054])).
% 9.17/3.39  tff(c_14221, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_3'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14219, c_13846])).
% 9.17/3.39  tff(c_14315, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_14298, c_14221])).
% 9.17/3.39  tff(c_14750, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14596, c_14315])).
% 9.17/3.39  tff(c_14753, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14598, c_14750])).
% 9.17/3.39  tff(c_14754, plain, (k2_zfmisc_1('#skF_4', '#skF_3')=k2_funct_1('#skF_5')), inference(splitRight, [status(thm)], [c_12054])).
% 9.17/3.39  tff(c_15182, plain, (k2_zfmisc_1('#skF_4', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_15177, c_14754])).
% 9.17/3.39  tff(c_13815, plain, (![B_9, A_8]: (B_9='#skF_5' | A_8='#skF_5' | k2_zfmisc_1(A_8, B_9)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_13699, c_13699, c_13699, c_16])).
% 9.17/3.39  tff(c_15225, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_15182, c_13815])).
% 9.17/3.39  tff(c_15228, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_15225])).
% 9.17/3.39  tff(c_15249, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15228, c_13707])).
% 9.17/3.39  tff(c_13704, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_13699, c_13699, c_18])).
% 9.17/3.39  tff(c_15246, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15228, c_15228, c_13704])).
% 9.17/3.39  tff(c_14887, plain, (![C_1372, B_1373, A_1374]: (~v1_xboole_0(C_1372) | ~m1_subset_1(B_1373, k1_zfmisc_1(C_1372)) | ~r2_hidden(A_1374, B_1373))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.17/3.39  tff(c_14911, plain, (![A_1374]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_1374, '#skF_5'))), inference(resolution, [status(thm)], [c_88, c_14887])).
% 9.17/3.39  tff(c_14947, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_14911])).
% 9.17/3.39  tff(c_15347, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15246, c_14947])).
% 9.17/3.39  tff(c_15350, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15249, c_15347])).
% 9.17/3.39  tff(c_15351, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_15225])).
% 9.17/3.39  tff(c_15373, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15351, c_13707])).
% 9.17/3.39  tff(c_15371, plain, (![B_9]: (k2_zfmisc_1('#skF_3', B_9)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15351, c_15351, c_13705])).
% 9.17/3.39  tff(c_15434, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15371, c_14947])).
% 9.17/3.39  tff(c_15437, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15373, c_15434])).
% 9.17/3.39  tff(c_15439, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_14911])).
% 9.17/3.39  tff(c_14913, plain, (![A_1375, A_1376]: (~v1_xboole_0(A_1375) | ~r2_hidden(A_1376, A_1375))), inference(resolution, [status(thm)], [c_93, c_14887])).
% 9.17/3.39  tff(c_14918, plain, (![A_1377, B_1378]: (~v1_xboole_0(A_1377) | r1_tarski(A_1377, B_1378))), inference(resolution, [status(thm)], [c_6, c_14913])).
% 9.17/3.39  tff(c_12010, plain, (![A_1087, B_1088]: (r1_tarski(A_1087, B_1088) | ~m1_subset_1(A_1087, k1_zfmisc_1(B_1088)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.17/3.39  tff(c_12021, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_88, c_12010])).
% 9.17/3.39  tff(c_12055, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_12021, c_12047])).
% 9.17/3.39  tff(c_13793, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_12055])).
% 9.17/3.39  tff(c_14938, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_14918, c_13793])).
% 9.17/3.39  tff(c_15483, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15439, c_14938])).
% 9.17/3.39  tff(c_15484, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_12055])).
% 9.17/3.39  tff(c_15525, plain, (![B_1416, A_1417]: (B_1416='#skF_5' | A_1417='#skF_5' | k2_zfmisc_1(A_1417, B_1416)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_13699, c_13699, c_13699, c_16])).
% 9.17/3.39  tff(c_15535, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_15484, c_15525])).
% 9.17/3.39  tff(c_15540, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_15535])).
% 9.17/3.39  tff(c_52, plain, (![A_30]: (v1_funct_2(k1_xboole_0, A_30, k1_xboole_0) | k1_xboole_0=A_30 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_30, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.17/3.39  tff(c_96, plain, (![A_30]: (v1_funct_2(k1_xboole_0, A_30, k1_xboole_0) | k1_xboole_0=A_30 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_52])).
% 9.17/3.39  tff(c_99, plain, (![A_30]: (v1_funct_2(k1_xboole_0, A_30, k1_xboole_0) | k1_xboole_0=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_93, c_96])).
% 9.17/3.39  tff(c_13703, plain, (![A_30]: (v1_funct_2('#skF_5', A_30, '#skF_5') | A_30='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_13699, c_13699, c_13699, c_99])).
% 9.17/3.39  tff(c_15544, plain, (![A_30]: (v1_funct_2('#skF_3', A_30, '#skF_3') | A_30='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15540, c_15540, c_15540, c_13703])).
% 9.17/3.39  tff(c_15552, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15540, c_13707])).
% 9.17/3.39  tff(c_15725, plain, (![C_1431, B_1432, A_1433]: (~v1_xboole_0(C_1431) | ~m1_subset_1(B_1432, k1_zfmisc_1(C_1431)) | ~r2_hidden(A_1433, B_1432))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.17/3.39  tff(c_15767, plain, (![A_1436, A_1437]: (~v1_xboole_0(A_1436) | ~r2_hidden(A_1437, A_1436))), inference(resolution, [status(thm)], [c_93, c_15725])).
% 9.17/3.39  tff(c_15771, plain, (![A_1, B_2]: (~v1_xboole_0(A_1) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_15767])).
% 9.17/3.39  tff(c_15548, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15540, c_15540, c_13704])).
% 9.17/3.39  tff(c_15844, plain, (k2_funct_1('#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_15548, c_15540, c_15548, c_15540, c_12054])).
% 9.17/3.39  tff(c_15845, plain, (~r1_tarski('#skF_3', k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_15844])).
% 9.17/3.39  tff(c_15848, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_15771, c_15845])).
% 9.17/3.39  tff(c_15852, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15552, c_15848])).
% 9.17/3.39  tff(c_15853, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_15844])).
% 9.17/3.39  tff(c_15557, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15540, c_12006])).
% 9.17/3.39  tff(c_15858, plain, (~v1_funct_2('#skF_3', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15853, c_15557])).
% 9.17/3.39  tff(c_15926, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_15544, c_15858])).
% 9.17/3.39  tff(c_15560, plain, (v1_funct_2('#skF_3', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15540, c_90])).
% 9.17/3.39  tff(c_15945, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15926, c_15926, c_15560])).
% 9.17/3.39  tff(c_15927, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15926, c_15926, c_15858])).
% 9.17/3.39  tff(c_16056, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15945, c_15927])).
% 9.17/3.39  tff(c_16057, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_15535])).
% 9.17/3.39  tff(c_16070, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16057, c_13707])).
% 9.17/3.39  tff(c_13737, plain, (![A_1266, B_1267]: (m1_subset_1('#skF_2'(A_1266, B_1267), k1_zfmisc_1(k2_zfmisc_1(A_1266, B_1267))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.17/3.39  tff(c_13746, plain, (![B_9]: (m1_subset_1('#skF_2'('#skF_5', B_9), k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_13705, c_13737])).
% 9.17/3.39  tff(c_16061, plain, (![B_9]: (m1_subset_1('#skF_2'('#skF_4', B_9), k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_16057, c_16057, c_13746])).
% 9.17/3.39  tff(c_16229, plain, (![C_1469, B_1470, A_1471]: (~v1_xboole_0(C_1469) | ~m1_subset_1(B_1470, k1_zfmisc_1(C_1469)) | ~r2_hidden(A_1471, B_1470))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.17/3.39  tff(c_16235, plain, (![A_1471, B_9]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_1471, '#skF_2'('#skF_4', B_9)))), inference(resolution, [status(thm)], [c_16061, c_16229])).
% 9.17/3.39  tff(c_16298, plain, (![A_1480, B_1481]: (~r2_hidden(A_1480, '#skF_2'('#skF_4', B_1481)))), inference(demodulation, [status(thm), theory('equality')], [c_16070, c_16235])).
% 9.17/3.39  tff(c_16303, plain, (![B_1481, B_2]: (r1_tarski('#skF_2'('#skF_4', B_1481), B_2))), inference(resolution, [status(thm)], [c_6, c_16298])).
% 9.17/3.39  tff(c_16271, plain, (![A_1474, A_1475]: (~v1_xboole_0(A_1474) | ~r2_hidden(A_1475, A_1474))), inference(resolution, [status(thm)], [c_93, c_16229])).
% 9.17/3.39  tff(c_16275, plain, (![A_1, B_2]: (~v1_xboole_0(A_1) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_16271])).
% 9.17/3.39  tff(c_16067, plain, (![B_9]: (k2_zfmisc_1('#skF_4', B_9)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16057, c_16057, c_13705])).
% 9.17/3.39  tff(c_16333, plain, (k2_funct_1('#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_16067, c_16057, c_16067, c_16057, c_12054])).
% 9.17/3.39  tff(c_16334, plain, (~r1_tarski('#skF_4', k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_16333])).
% 9.17/3.39  tff(c_16337, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_16275, c_16334])).
% 9.17/3.39  tff(c_16341, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16070, c_16337])).
% 9.17/3.39  tff(c_16342, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_16333])).
% 9.17/3.39  tff(c_16074, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_16057, c_12007])).
% 9.17/3.39  tff(c_16175, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_16067, c_16074])).
% 9.17/3.39  tff(c_16233, plain, (![A_1471]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_1471, k2_funct_1('#skF_4')))), inference(resolution, [status(thm)], [c_16175, c_16229])).
% 9.17/3.39  tff(c_16254, plain, (![A_1472]: (~r2_hidden(A_1472, k2_funct_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_16070, c_16233])).
% 9.17/3.39  tff(c_16259, plain, (![B_2]: (r1_tarski(k2_funct_1('#skF_4'), B_2))), inference(resolution, [status(thm)], [c_6, c_16254])).
% 9.17/3.39  tff(c_16373, plain, (![B_1488]: (r1_tarski('#skF_4', B_1488))), inference(demodulation, [status(thm), theory('equality')], [c_16342, c_16259])).
% 9.17/3.39  tff(c_16415, plain, (![B_1490]: (B_1490='#skF_4' | ~r1_tarski(B_1490, '#skF_4'))), inference(resolution, [status(thm)], [c_16373, c_10])).
% 9.17/3.39  tff(c_16448, plain, (![B_1491]: ('#skF_2'('#skF_4', B_1491)='#skF_4')), inference(resolution, [status(thm)], [c_16303, c_16415])).
% 9.17/3.39  tff(c_16456, plain, (![B_1491]: (v1_funct_2('#skF_4', '#skF_4', B_1491))), inference(superposition, [status(thm), theory('equality')], [c_16448, c_64])).
% 9.17/3.39  tff(c_16075, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16057, c_12006])).
% 9.17/3.39  tff(c_16347, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16342, c_16075])).
% 9.17/3.39  tff(c_16533, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16456, c_16347])).
% 9.17/3.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.17/3.39  
% 9.17/3.39  Inference rules
% 9.17/3.39  ----------------------
% 9.17/3.39  #Ref     : 0
% 9.17/3.39  #Sup     : 3559
% 9.17/3.39  #Fact    : 0
% 9.17/3.39  #Define  : 0
% 9.17/3.39  #Split   : 55
% 9.17/3.39  #Chain   : 0
% 9.17/3.39  #Close   : 0
% 9.17/3.39  
% 9.17/3.39  Ordering : KBO
% 9.17/3.39  
% 9.17/3.39  Simplification rules
% 9.17/3.39  ----------------------
% 9.17/3.39  #Subsume      : 525
% 9.17/3.39  #Demod        : 3565
% 9.17/3.39  #Tautology    : 2001
% 9.17/3.39  #SimpNegUnit  : 33
% 9.17/3.39  #BackRed      : 602
% 9.17/3.39  
% 9.17/3.39  #Partial instantiations: 0
% 9.17/3.39  #Strategies tried      : 1
% 9.17/3.39  
% 9.17/3.39  Timing (in seconds)
% 9.17/3.39  ----------------------
% 9.17/3.39  Preprocessing        : 0.37
% 9.17/3.39  Parsing              : 0.20
% 9.17/3.39  CNF conversion       : 0.02
% 9.17/3.39  Main loop            : 2.08
% 9.17/3.39  Inferencing          : 0.70
% 9.17/3.39  Reduction            : 0.74
% 9.17/3.39  Demodulation         : 0.53
% 9.17/3.39  BG Simplification    : 0.07
% 9.17/3.39  Subsumption          : 0.39
% 9.17/3.39  Abstraction          : 0.08
% 9.17/3.39  MUC search           : 0.00
% 9.17/3.39  Cooper               : 0.00
% 9.17/3.39  Total                : 2.60
% 9.17/3.39  Index Insertion      : 0.00
% 9.17/3.39  Index Deletion       : 0.00
% 9.17/3.39  Index Matching       : 0.00
% 9.17/3.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
