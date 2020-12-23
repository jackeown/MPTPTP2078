%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:48 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.63s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 378 expanded)
%              Number of leaves         :   25 ( 132 expanded)
%              Depth                    :    9
%              Number of atoms          :  168 ( 954 expanded)
%              Number of equality atoms :   65 ( 425 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_97,axiom,(
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

tff(f_42,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_60,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1512,plain,(
    ! [C_231,A_232,B_233] :
      ( m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_232,B_233)))
      | ~ r1_tarski(k2_relat_1(C_231),B_233)
      | ~ r1_tarski(k1_relat_1(C_231),A_232)
      | ~ v1_relat_1(C_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_549,plain,(
    ! [C_89,A_90,B_91] :
      ( m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91)))
      | ~ r1_tarski(k2_relat_1(C_89),B_91)
      | ~ r1_tarski(k1_relat_1(C_89),A_90)
      | ~ v1_relat_1(C_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_40,plain,(
    ! [A_10,B_11,C_12] :
      ( k1_relset_1(A_10,B_11,C_12) = k1_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_689,plain,(
    ! [A_114,B_115,C_116] :
      ( k1_relset_1(A_114,B_115,C_116) = k1_relat_1(C_116)
      | ~ r1_tarski(k2_relat_1(C_116),B_115)
      | ~ r1_tarski(k1_relat_1(C_116),A_114)
      | ~ v1_relat_1(C_116) ) ),
    inference(resolution,[status(thm)],[c_549,c_40])).

tff(c_710,plain,(
    ! [A_119,C_120] :
      ( k1_relset_1(A_119,k2_relat_1(C_120),C_120) = k1_relat_1(C_120)
      | ~ r1_tarski(k1_relat_1(C_120),A_119)
      | ~ v1_relat_1(C_120) ) ),
    inference(resolution,[status(thm)],[c_6,c_689])).

tff(c_718,plain,(
    ! [C_120] :
      ( k1_relset_1(k1_relat_1(C_120),k2_relat_1(C_120),C_120) = k1_relat_1(C_120)
      | ~ v1_relat_1(C_120) ) ),
    inference(resolution,[status(thm)],[c_6,c_710])).

tff(c_157,plain,(
    ! [A_33] :
      ( k2_relat_1(A_33) != k1_xboole_0
      | k1_xboole_0 = A_33
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_172,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_60,c_157])).

tff(c_188,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_42,plain,(
    ! [C_15,A_13,B_14] :
      ( m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ r1_tarski(k2_relat_1(C_15),B_14)
      | ~ r1_tarski(k1_relat_1(C_15),A_13)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_613,plain,(
    ! [B_101,C_102,A_103] :
      ( k1_xboole_0 = B_101
      | v1_funct_2(C_102,A_103,B_101)
      | k1_relset_1(A_103,B_101,C_102) != A_103
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_755,plain,(
    ! [B_122,C_123,A_124] :
      ( k1_xboole_0 = B_122
      | v1_funct_2(C_123,A_124,B_122)
      | k1_relset_1(A_124,B_122,C_123) != A_124
      | ~ r1_tarski(k2_relat_1(C_123),B_122)
      | ~ r1_tarski(k1_relat_1(C_123),A_124)
      | ~ v1_relat_1(C_123) ) ),
    inference(resolution,[status(thm)],[c_42,c_613])).

tff(c_809,plain,(
    ! [C_129,A_130] :
      ( k2_relat_1(C_129) = k1_xboole_0
      | v1_funct_2(C_129,A_130,k2_relat_1(C_129))
      | k1_relset_1(A_130,k2_relat_1(C_129),C_129) != A_130
      | ~ r1_tarski(k1_relat_1(C_129),A_130)
      | ~ v1_relat_1(C_129) ) ),
    inference(resolution,[status(thm)],[c_6,c_755])).

tff(c_58,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_56,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_62,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56])).

tff(c_87,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_815,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_809,c_87])).

tff(c_822,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_6,c_815])).

tff(c_823,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_822])).

tff(c_828,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_718,c_823])).

tff(c_832,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_828])).

tff(c_833,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_18,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_848,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_833,c_18])).

tff(c_113,plain,(
    ! [A_31] :
      ( k1_relat_1(A_31) != k1_xboole_0
      | k1_xboole_0 = A_31
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_127,plain,
    ( k1_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_60,c_113])).

tff(c_154,plain,(
    k1_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_837,plain,(
    k1_relat_1('#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_154])).

tff(c_878,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_848,c_837])).

tff(c_879,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_880,plain,(
    k1_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_898,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_879,c_880])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_44,plain,(
    ! [A_16] :
      ( v1_funct_2(k1_xboole_0,A_16,k1_xboole_0)
      | k1_xboole_0 = A_16
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_16,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_65,plain,(
    ! [A_16] :
      ( v1_funct_2(k1_xboole_0,A_16,k1_xboole_0)
      | k1_xboole_0 = A_16
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_44])).

tff(c_1050,plain,(
    ! [A_16] :
      ( v1_funct_2('#skF_2',A_16,'#skF_2')
      | A_16 = '#skF_2'
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_879,c_879,c_879,c_879,c_879,c_65])).

tff(c_1051,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1050])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_889,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_879,c_8])).

tff(c_16,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_890,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_879,c_879,c_16])).

tff(c_888,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_879,c_879,c_12])).

tff(c_1164,plain,(
    ! [C_170,A_171,B_172] :
      ( m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172)))
      | ~ r1_tarski(k2_relat_1(C_170),B_172)
      | ~ r1_tarski(k1_relat_1(C_170),A_171)
      | ~ v1_relat_1(C_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1194,plain,(
    ! [C_179,A_180] :
      ( m1_subset_1(C_179,k1_zfmisc_1('#skF_2'))
      | ~ r1_tarski(k2_relat_1(C_179),'#skF_2')
      | ~ r1_tarski(k1_relat_1(C_179),A_180)
      | ~ v1_relat_1(C_179) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_888,c_1164])).

tff(c_1199,plain,(
    ! [A_180] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2'))
      | ~ r1_tarski('#skF_2','#skF_2')
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_180)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_890,c_1194])).

tff(c_1203,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_889,c_898,c_6,c_1199])).

tff(c_1205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1051,c_1203])).

tff(c_1207,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1050])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_887,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_2',B_5) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_879,c_879,c_14])).

tff(c_1043,plain,(
    ! [A_153,B_154,C_155] :
      ( k1_relset_1(A_153,B_154,C_155) = k1_relat_1(C_155)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1245,plain,(
    ! [B_190,C_191] :
      ( k1_relset_1('#skF_2',B_190,C_191) = k1_relat_1(C_191)
      | ~ m1_subset_1(C_191,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_887,c_1043])).

tff(c_1247,plain,(
    ! [B_190] : k1_relset_1('#skF_2',B_190,'#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1207,c_1245])).

tff(c_1249,plain,(
    ! [B_190] : k1_relset_1('#skF_2',B_190,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_898,c_1247])).

tff(c_48,plain,(
    ! [C_18,B_17] :
      ( v1_funct_2(C_18,k1_xboole_0,B_17)
      | k1_relset_1(k1_xboole_0,B_17,C_18) != k1_xboole_0
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_63,plain,(
    ! [C_18,B_17] :
      ( v1_funct_2(C_18,k1_xboole_0,B_17)
      | k1_relset_1(k1_xboole_0,B_17,C_18) != k1_xboole_0
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_48])).

tff(c_1320,plain,(
    ! [C_197,B_198] :
      ( v1_funct_2(C_197,'#skF_2',B_198)
      | k1_relset_1('#skF_2',B_198,C_197) != '#skF_2'
      | ~ m1_subset_1(C_197,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_879,c_879,c_879,c_879,c_63])).

tff(c_1322,plain,(
    ! [B_198] :
      ( v1_funct_2('#skF_2','#skF_2',B_198)
      | k1_relset_1('#skF_2',B_198,'#skF_2') != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_1207,c_1320])).

tff(c_1325,plain,(
    ! [B_198] : v1_funct_2('#skF_2','#skF_2',B_198) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1249,c_1322])).

tff(c_899,plain,(
    ~ v1_funct_2('#skF_2','#skF_2',k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_898,c_87])).

tff(c_956,plain,(
    ~ v1_funct_2('#skF_2','#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_890,c_899])).

tff(c_1328,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1325,c_956])).

tff(c_1329,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_1518,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_2'),k2_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1512,c_1329])).

tff(c_1529,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_6,c_6,c_1518])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:34:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.59  
% 3.28/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.59  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.28/1.59  
% 3.28/1.59  %Foreground sorts:
% 3.28/1.59  
% 3.28/1.59  
% 3.28/1.59  %Background operators:
% 3.28/1.59  
% 3.28/1.59  
% 3.28/1.59  %Foreground operators:
% 3.28/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.28/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.28/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.28/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.28/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.28/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.28/1.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.28/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.28/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.28/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.28/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.28/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.28/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.28/1.59  
% 3.63/1.61  tff(f_108, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 3.63/1.61  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.63/1.61  tff(f_79, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 3.63/1.61  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.63/1.61  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.63/1.61  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.63/1.61  tff(f_42, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.63/1.61  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.63/1.61  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.63/1.61  tff(c_60, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.63/1.61  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.63/1.61  tff(c_1512, plain, (![C_231, A_232, B_233]: (m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_232, B_233))) | ~r1_tarski(k2_relat_1(C_231), B_233) | ~r1_tarski(k1_relat_1(C_231), A_232) | ~v1_relat_1(C_231))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.63/1.61  tff(c_549, plain, (![C_89, A_90, B_91]: (m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))) | ~r1_tarski(k2_relat_1(C_89), B_91) | ~r1_tarski(k1_relat_1(C_89), A_90) | ~v1_relat_1(C_89))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.63/1.61  tff(c_40, plain, (![A_10, B_11, C_12]: (k1_relset_1(A_10, B_11, C_12)=k1_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.63/1.61  tff(c_689, plain, (![A_114, B_115, C_116]: (k1_relset_1(A_114, B_115, C_116)=k1_relat_1(C_116) | ~r1_tarski(k2_relat_1(C_116), B_115) | ~r1_tarski(k1_relat_1(C_116), A_114) | ~v1_relat_1(C_116))), inference(resolution, [status(thm)], [c_549, c_40])).
% 3.63/1.61  tff(c_710, plain, (![A_119, C_120]: (k1_relset_1(A_119, k2_relat_1(C_120), C_120)=k1_relat_1(C_120) | ~r1_tarski(k1_relat_1(C_120), A_119) | ~v1_relat_1(C_120))), inference(resolution, [status(thm)], [c_6, c_689])).
% 3.63/1.61  tff(c_718, plain, (![C_120]: (k1_relset_1(k1_relat_1(C_120), k2_relat_1(C_120), C_120)=k1_relat_1(C_120) | ~v1_relat_1(C_120))), inference(resolution, [status(thm)], [c_6, c_710])).
% 3.63/1.61  tff(c_157, plain, (![A_33]: (k2_relat_1(A_33)!=k1_xboole_0 | k1_xboole_0=A_33 | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.63/1.61  tff(c_172, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_60, c_157])).
% 3.63/1.61  tff(c_188, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_172])).
% 3.63/1.61  tff(c_42, plain, (![C_15, A_13, B_14]: (m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~r1_tarski(k2_relat_1(C_15), B_14) | ~r1_tarski(k1_relat_1(C_15), A_13) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.63/1.61  tff(c_613, plain, (![B_101, C_102, A_103]: (k1_xboole_0=B_101 | v1_funct_2(C_102, A_103, B_101) | k1_relset_1(A_103, B_101, C_102)!=A_103 | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_101))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.63/1.61  tff(c_755, plain, (![B_122, C_123, A_124]: (k1_xboole_0=B_122 | v1_funct_2(C_123, A_124, B_122) | k1_relset_1(A_124, B_122, C_123)!=A_124 | ~r1_tarski(k2_relat_1(C_123), B_122) | ~r1_tarski(k1_relat_1(C_123), A_124) | ~v1_relat_1(C_123))), inference(resolution, [status(thm)], [c_42, c_613])).
% 3.63/1.61  tff(c_809, plain, (![C_129, A_130]: (k2_relat_1(C_129)=k1_xboole_0 | v1_funct_2(C_129, A_130, k2_relat_1(C_129)) | k1_relset_1(A_130, k2_relat_1(C_129), C_129)!=A_130 | ~r1_tarski(k1_relat_1(C_129), A_130) | ~v1_relat_1(C_129))), inference(resolution, [status(thm)], [c_6, c_755])).
% 3.63/1.61  tff(c_58, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.63/1.61  tff(c_56, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2')) | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.63/1.61  tff(c_62, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56])).
% 3.63/1.61  tff(c_87, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_62])).
% 3.63/1.61  tff(c_815, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_809, c_87])).
% 3.63/1.61  tff(c_822, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_6, c_815])).
% 3.63/1.61  tff(c_823, plain, (k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_188, c_822])).
% 3.63/1.61  tff(c_828, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_718, c_823])).
% 3.63/1.61  tff(c_832, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_828])).
% 3.63/1.61  tff(c_833, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_172])).
% 3.63/1.61  tff(c_18, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.63/1.61  tff(c_848, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_833, c_833, c_18])).
% 3.63/1.61  tff(c_113, plain, (![A_31]: (k1_relat_1(A_31)!=k1_xboole_0 | k1_xboole_0=A_31 | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.63/1.61  tff(c_127, plain, (k1_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_60, c_113])).
% 3.63/1.61  tff(c_154, plain, (k1_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_127])).
% 3.63/1.61  tff(c_837, plain, (k1_relat_1('#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_833, c_154])).
% 3.63/1.61  tff(c_878, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_848, c_837])).
% 3.63/1.61  tff(c_879, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_127])).
% 3.63/1.61  tff(c_880, plain, (k1_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_127])).
% 3.63/1.61  tff(c_898, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_879, c_880])).
% 3.63/1.61  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.63/1.61  tff(c_44, plain, (![A_16]: (v1_funct_2(k1_xboole_0, A_16, k1_xboole_0) | k1_xboole_0=A_16 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_16, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.63/1.61  tff(c_65, plain, (![A_16]: (v1_funct_2(k1_xboole_0, A_16, k1_xboole_0) | k1_xboole_0=A_16 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_44])).
% 3.63/1.61  tff(c_1050, plain, (![A_16]: (v1_funct_2('#skF_2', A_16, '#skF_2') | A_16='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_879, c_879, c_879, c_879, c_879, c_65])).
% 3.63/1.61  tff(c_1051, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_1050])).
% 3.63/1.61  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.63/1.61  tff(c_889, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_879, c_8])).
% 3.63/1.61  tff(c_16, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.63/1.61  tff(c_890, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_879, c_879, c_16])).
% 3.63/1.61  tff(c_888, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_879, c_879, c_12])).
% 3.63/1.61  tff(c_1164, plain, (![C_170, A_171, B_172]: (m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))) | ~r1_tarski(k2_relat_1(C_170), B_172) | ~r1_tarski(k1_relat_1(C_170), A_171) | ~v1_relat_1(C_170))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.63/1.61  tff(c_1194, plain, (![C_179, A_180]: (m1_subset_1(C_179, k1_zfmisc_1('#skF_2')) | ~r1_tarski(k2_relat_1(C_179), '#skF_2') | ~r1_tarski(k1_relat_1(C_179), A_180) | ~v1_relat_1(C_179))), inference(superposition, [status(thm), theory('equality')], [c_888, c_1164])).
% 3.63/1.61  tff(c_1199, plain, (![A_180]: (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2')) | ~r1_tarski('#skF_2', '#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), A_180) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_890, c_1194])).
% 3.63/1.61  tff(c_1203, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_889, c_898, c_6, c_1199])).
% 3.63/1.61  tff(c_1205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1051, c_1203])).
% 3.63/1.61  tff(c_1207, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(splitRight, [status(thm)], [c_1050])).
% 3.63/1.61  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.63/1.61  tff(c_887, plain, (![B_5]: (k2_zfmisc_1('#skF_2', B_5)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_879, c_879, c_14])).
% 3.63/1.61  tff(c_1043, plain, (![A_153, B_154, C_155]: (k1_relset_1(A_153, B_154, C_155)=k1_relat_1(C_155) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.63/1.61  tff(c_1245, plain, (![B_190, C_191]: (k1_relset_1('#skF_2', B_190, C_191)=k1_relat_1(C_191) | ~m1_subset_1(C_191, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_887, c_1043])).
% 3.63/1.61  tff(c_1247, plain, (![B_190]: (k1_relset_1('#skF_2', B_190, '#skF_2')=k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_1207, c_1245])).
% 3.63/1.61  tff(c_1249, plain, (![B_190]: (k1_relset_1('#skF_2', B_190, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_898, c_1247])).
% 3.63/1.61  tff(c_48, plain, (![C_18, B_17]: (v1_funct_2(C_18, k1_xboole_0, B_17) | k1_relset_1(k1_xboole_0, B_17, C_18)!=k1_xboole_0 | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_17))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.63/1.61  tff(c_63, plain, (![C_18, B_17]: (v1_funct_2(C_18, k1_xboole_0, B_17) | k1_relset_1(k1_xboole_0, B_17, C_18)!=k1_xboole_0 | ~m1_subset_1(C_18, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_48])).
% 3.63/1.61  tff(c_1320, plain, (![C_197, B_198]: (v1_funct_2(C_197, '#skF_2', B_198) | k1_relset_1('#skF_2', B_198, C_197)!='#skF_2' | ~m1_subset_1(C_197, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_879, c_879, c_879, c_879, c_63])).
% 3.63/1.61  tff(c_1322, plain, (![B_198]: (v1_funct_2('#skF_2', '#skF_2', B_198) | k1_relset_1('#skF_2', B_198, '#skF_2')!='#skF_2')), inference(resolution, [status(thm)], [c_1207, c_1320])).
% 3.63/1.61  tff(c_1325, plain, (![B_198]: (v1_funct_2('#skF_2', '#skF_2', B_198))), inference(demodulation, [status(thm), theory('equality')], [c_1249, c_1322])).
% 3.63/1.61  tff(c_899, plain, (~v1_funct_2('#skF_2', '#skF_2', k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_898, c_87])).
% 3.63/1.61  tff(c_956, plain, (~v1_funct_2('#skF_2', '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_890, c_899])).
% 3.63/1.61  tff(c_1328, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1325, c_956])).
% 3.63/1.61  tff(c_1329, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))))), inference(splitRight, [status(thm)], [c_62])).
% 3.63/1.61  tff(c_1518, plain, (~r1_tarski(k2_relat_1('#skF_2'), k2_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1512, c_1329])).
% 3.63/1.61  tff(c_1529, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_6, c_6, c_1518])).
% 3.63/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/1.61  
% 3.63/1.61  Inference rules
% 3.63/1.61  ----------------------
% 3.63/1.61  #Ref     : 0
% 3.63/1.61  #Sup     : 296
% 3.63/1.61  #Fact    : 0
% 3.63/1.61  #Define  : 0
% 3.63/1.61  #Split   : 8
% 3.63/1.61  #Chain   : 0
% 3.63/1.61  #Close   : 0
% 3.63/1.61  
% 3.63/1.61  Ordering : KBO
% 3.63/1.61  
% 3.63/1.61  Simplification rules
% 3.63/1.61  ----------------------
% 3.63/1.61  #Subsume      : 21
% 3.63/1.61  #Demod        : 320
% 3.63/1.61  #Tautology    : 213
% 3.63/1.61  #SimpNegUnit  : 3
% 3.63/1.61  #BackRed      : 36
% 3.63/1.61  
% 3.63/1.61  #Partial instantiations: 0
% 3.63/1.61  #Strategies tried      : 1
% 3.63/1.61  
% 3.63/1.61  Timing (in seconds)
% 3.63/1.61  ----------------------
% 3.63/1.61  Preprocessing        : 0.35
% 3.63/1.61  Parsing              : 0.18
% 3.63/1.61  CNF conversion       : 0.02
% 3.63/1.61  Main loop            : 0.46
% 3.63/1.61  Inferencing          : 0.16
% 3.63/1.62  Reduction            : 0.14
% 3.63/1.62  Demodulation         : 0.10
% 3.63/1.62  BG Simplification    : 0.03
% 3.63/1.62  Subsumption          : 0.09
% 3.63/1.62  Abstraction          : 0.03
% 3.63/1.62  MUC search           : 0.00
% 3.63/1.62  Cooper               : 0.00
% 3.63/1.62  Total                : 0.85
% 3.63/1.62  Index Insertion      : 0.00
% 3.63/1.62  Index Deletion       : 0.00
% 3.63/1.62  Index Matching       : 0.00
% 3.63/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
