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
% DateTime   : Thu Dec  3 10:16:05 EST 2020

% Result     : Theorem 4.61s
% Output     : CNFRefutation 4.89s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 486 expanded)
%              Number of leaves         :   39 ( 204 expanded)
%              Depth                    :   12
%              Number of atoms          :  306 (1570 expanded)
%              Number of equality atoms :   42 ( 105 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

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

tff(f_136,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_101,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_123,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_45,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_121,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_111,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_35,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_68,plain,(
    ! [C_33,A_34,B_35] :
      ( v1_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_76,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_68])).

tff(c_54,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_50,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1606,plain,(
    ! [C_164,A_165,B_166] :
      ( v2_funct_1(C_164)
      | ~ v3_funct_2(C_164,A_165,B_166)
      | ~ v1_funct_1(C_164)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1612,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1606])).

tff(c_1616,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_1612])).

tff(c_38,plain,(
    ! [A_20] : m1_subset_1(k6_partfun1(A_20),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1629,plain,(
    ! [A_171,B_172,C_173,D_174] :
      ( r2_relset_1(A_171,B_172,C_173,C_173)
      | ~ m1_subset_1(D_174,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172)))
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1636,plain,(
    ! [A_175,C_176] :
      ( r2_relset_1(A_175,A_175,C_176,C_176)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_175,A_175))) ) ),
    inference(resolution,[status(thm)],[c_38,c_1629])).

tff(c_1641,plain,(
    ! [A_20] : r2_relset_1(A_20,A_20,k6_partfun1(A_20),k6_partfun1(A_20)) ),
    inference(resolution,[status(thm)],[c_38,c_1636])).

tff(c_1493,plain,(
    ! [C_142,B_143,A_144] :
      ( v5_relat_1(C_142,B_143)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_144,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1501,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_1493])).

tff(c_1526,plain,(
    ! [B_150,A_151] :
      ( k2_relat_1(B_150) = A_151
      | ~ v2_funct_2(B_150,A_151)
      | ~ v5_relat_1(B_150,A_151)
      | ~ v1_relat_1(B_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1532,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1501,c_1526])).

tff(c_1538,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1532])).

tff(c_1548,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1538])).

tff(c_1571,plain,(
    ! [C_159,B_160,A_161] :
      ( v2_funct_2(C_159,B_160)
      | ~ v3_funct_2(C_159,A_161,B_160)
      | ~ v1_funct_1(C_159)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_161,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1577,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1571])).

tff(c_1581,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_1577])).

tff(c_1583,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1548,c_1581])).

tff(c_1584,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1538])).

tff(c_44,plain,(
    ! [A_29] : k6_relat_1(A_29) = k6_partfun1(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_6,plain,(
    ! [A_2] :
      ( k5_relat_1(k2_funct_1(A_2),A_2) = k6_relat_1(k2_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_56,plain,(
    ! [A_2] :
      ( k5_relat_1(k2_funct_1(A_2),A_2) = k6_partfun1(k2_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_6])).

tff(c_52,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1661,plain,(
    ! [A_183,B_184] :
      ( k2_funct_2(A_183,B_184) = k2_funct_1(B_184)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(k2_zfmisc_1(A_183,A_183)))
      | ~ v3_funct_2(B_184,A_183,A_183)
      | ~ v1_funct_2(B_184,A_183,A_183)
      | ~ v1_funct_1(B_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1667,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1661])).

tff(c_1671,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_1667])).

tff(c_1645,plain,(
    ! [A_179,B_180] :
      ( v1_funct_1(k2_funct_2(A_179,B_180))
      | ~ m1_subset_1(B_180,k1_zfmisc_1(k2_zfmisc_1(A_179,A_179)))
      | ~ v3_funct_2(B_180,A_179,A_179)
      | ~ v1_funct_2(B_180,A_179,A_179)
      | ~ v1_funct_1(B_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1651,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1645])).

tff(c_1655,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_1651])).

tff(c_1672,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1671,c_1655])).

tff(c_28,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k2_funct_2(A_18,B_19),k1_zfmisc_1(k2_zfmisc_1(A_18,A_18)))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(k2_zfmisc_1(A_18,A_18)))
      | ~ v3_funct_2(B_19,A_18,A_18)
      | ~ v1_funct_2(B_19,A_18,A_18)
      | ~ v1_funct_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1803,plain,(
    ! [F_196,C_195,E_198,A_193,D_194,B_197] :
      ( k1_partfun1(A_193,B_197,C_195,D_194,E_198,F_196) = k5_relat_1(E_198,F_196)
      | ~ m1_subset_1(F_196,k1_zfmisc_1(k2_zfmisc_1(C_195,D_194)))
      | ~ v1_funct_1(F_196)
      | ~ m1_subset_1(E_198,k1_zfmisc_1(k2_zfmisc_1(A_193,B_197)))
      | ~ v1_funct_1(E_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1811,plain,(
    ! [A_193,B_197,E_198] :
      ( k1_partfun1(A_193,B_197,'#skF_1','#skF_1',E_198,'#skF_2') = k5_relat_1(E_198,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_198,k1_zfmisc_1(k2_zfmisc_1(A_193,B_197)))
      | ~ v1_funct_1(E_198) ) ),
    inference(resolution,[status(thm)],[c_48,c_1803])).

tff(c_1832,plain,(
    ! [A_199,B_200,E_201] :
      ( k1_partfun1(A_199,B_200,'#skF_1','#skF_1',E_201,'#skF_2') = k5_relat_1(E_201,'#skF_2')
      | ~ m1_subset_1(E_201,k1_zfmisc_1(k2_zfmisc_1(A_199,B_200)))
      | ~ v1_funct_1(E_201) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1811])).

tff(c_2109,plain,(
    ! [A_208,B_209] :
      ( k1_partfun1(A_208,A_208,'#skF_1','#skF_1',k2_funct_2(A_208,B_209),'#skF_2') = k5_relat_1(k2_funct_2(A_208,B_209),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_208,B_209))
      | ~ m1_subset_1(B_209,k1_zfmisc_1(k2_zfmisc_1(A_208,A_208)))
      | ~ v3_funct_2(B_209,A_208,A_208)
      | ~ v1_funct_2(B_209,A_208,A_208)
      | ~ v1_funct_1(B_209) ) ),
    inference(resolution,[status(thm)],[c_28,c_1832])).

tff(c_2121,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_2109])).

tff(c_2135,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_1672,c_1671,c_1671,c_1671,c_2121])).

tff(c_230,plain,(
    ! [C_64,A_65,B_66] :
      ( v2_funct_1(C_64)
      | ~ v3_funct_2(C_64,A_65,B_66)
      | ~ v1_funct_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_236,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_230])).

tff(c_240,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_236])).

tff(c_254,plain,(
    ! [A_72,B_73,C_74,D_75] :
      ( r2_relset_1(A_72,B_73,C_74,C_74)
      | ~ m1_subset_1(D_75,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73)))
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_261,plain,(
    ! [A_76,C_77] :
      ( r2_relset_1(A_76,A_76,C_77,C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_76,A_76))) ) ),
    inference(resolution,[status(thm)],[c_38,c_254])).

tff(c_266,plain,(
    ! [A_20] : r2_relset_1(A_20,A_20,k6_partfun1(A_20),k6_partfun1(A_20)) ),
    inference(resolution,[status(thm)],[c_38,c_261])).

tff(c_285,plain,(
    ! [A_83,B_84] :
      ( k2_funct_2(A_83,B_84) = k2_funct_1(B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(k2_zfmisc_1(A_83,A_83)))
      | ~ v3_funct_2(B_84,A_83,A_83)
      | ~ v1_funct_2(B_84,A_83,A_83)
      | ~ v1_funct_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_291,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_285])).

tff(c_295,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_291])).

tff(c_268,plain,(
    ! [A_78,B_79] :
      ( v1_funct_1(k2_funct_2(A_78,B_79))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k2_zfmisc_1(A_78,A_78)))
      | ~ v3_funct_2(B_79,A_78,A_78)
      | ~ v1_funct_2(B_79,A_78,A_78)
      | ~ v1_funct_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_274,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_268])).

tff(c_278,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_274])).

tff(c_296,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_278])).

tff(c_312,plain,(
    ! [A_88,B_89] :
      ( v3_funct_2(k2_funct_2(A_88,B_89),A_88,A_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(k2_zfmisc_1(A_88,A_88)))
      | ~ v3_funct_2(B_89,A_88,A_88)
      | ~ v1_funct_2(B_89,A_88,A_88)
      | ~ v1_funct_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_316,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_312])).

tff(c_320,plain,(
    v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_295,c_316])).

tff(c_323,plain,(
    ! [A_92,B_93] :
      ( m1_subset_1(k2_funct_2(A_92,B_93),k1_zfmisc_1(k2_zfmisc_1(A_92,A_92)))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k2_zfmisc_1(A_92,A_92)))
      | ~ v3_funct_2(B_93,A_92,A_92)
      | ~ v1_funct_2(B_93,A_92,A_92)
      | ~ v1_funct_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_355,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_323])).

tff(c_368,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_355])).

tff(c_18,plain,(
    ! [C_15,B_14,A_13] :
      ( v2_funct_2(C_15,B_14)
      | ~ v3_funct_2(C_15,A_13,B_14)
      | ~ v1_funct_1(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_385,plain,
    ( v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_368,c_18])).

tff(c_414,plain,(
    v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_320,c_385])).

tff(c_10,plain,(
    ! [C_5,A_3,B_4] :
      ( v1_relat_1(C_5)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_420,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_368,c_10])).

tff(c_12,plain,(
    ! [C_8,B_7,A_6] :
      ( v5_relat_1(C_8,B_7)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_418,plain,(
    v5_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_368,c_12])).

tff(c_26,plain,(
    ! [B_17,A_16] :
      ( k2_relat_1(B_17) = A_16
      | ~ v2_funct_2(B_17,A_16)
      | ~ v5_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_461,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_418,c_26])).

tff(c_464,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_461])).

tff(c_680,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_464])).

tff(c_2,plain,(
    ! [A_1] :
      ( k2_relat_1(k2_funct_1(A_1)) = k1_relat_1(A_1)
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_687,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_680,c_2])).

tff(c_699,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_54,c_240,c_687])).

tff(c_8,plain,(
    ! [A_2] :
      ( k5_relat_1(A_2,k2_funct_1(A_2)) = k6_relat_1(k1_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_55,plain,(
    ! [A_2] :
      ( k5_relat_1(A_2,k2_funct_1(A_2)) = k6_partfun1(k1_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_8])).

tff(c_421,plain,(
    ! [B_98,F_97,E_99,C_96,D_95,A_94] :
      ( k1_partfun1(A_94,B_98,C_96,D_95,E_99,F_97) = k5_relat_1(E_99,F_97)
      | ~ m1_subset_1(F_97,k1_zfmisc_1(k2_zfmisc_1(C_96,D_95)))
      | ~ v1_funct_1(F_97)
      | ~ m1_subset_1(E_99,k1_zfmisc_1(k2_zfmisc_1(A_94,B_98)))
      | ~ v1_funct_1(E_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1376,plain,(
    ! [A_133,A_132,E_131,B_135,B_134] :
      ( k1_partfun1(A_132,B_134,A_133,A_133,E_131,k2_funct_2(A_133,B_135)) = k5_relat_1(E_131,k2_funct_2(A_133,B_135))
      | ~ v1_funct_1(k2_funct_2(A_133,B_135))
      | ~ m1_subset_1(E_131,k1_zfmisc_1(k2_zfmisc_1(A_132,B_134)))
      | ~ v1_funct_1(E_131)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(k2_zfmisc_1(A_133,A_133)))
      | ~ v3_funct_2(B_135,A_133,A_133)
      | ~ v1_funct_2(B_135,A_133,A_133)
      | ~ v1_funct_1(B_135) ) ),
    inference(resolution,[status(thm)],[c_28,c_421])).

tff(c_1392,plain,(
    ! [A_133,B_135] :
      ( k1_partfun1('#skF_1','#skF_1',A_133,A_133,'#skF_2',k2_funct_2(A_133,B_135)) = k5_relat_1('#skF_2',k2_funct_2(A_133,B_135))
      | ~ v1_funct_1(k2_funct_2(A_133,B_135))
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(B_135,k1_zfmisc_1(k2_zfmisc_1(A_133,A_133)))
      | ~ v3_funct_2(B_135,A_133,A_133)
      | ~ v1_funct_2(B_135,A_133,A_133)
      | ~ v1_funct_1(B_135) ) ),
    inference(resolution,[status(thm)],[c_48,c_1376])).

tff(c_1433,plain,(
    ! [A_136,B_137] :
      ( k1_partfun1('#skF_1','#skF_1',A_136,A_136,'#skF_2',k2_funct_2(A_136,B_137)) = k5_relat_1('#skF_2',k2_funct_2(A_136,B_137))
      | ~ v1_funct_1(k2_funct_2(A_136,B_137))
      | ~ m1_subset_1(B_137,k1_zfmisc_1(k2_zfmisc_1(A_136,A_136)))
      | ~ v3_funct_2(B_137,A_136,A_136)
      | ~ v1_funct_2(B_137,A_136,A_136)
      | ~ v1_funct_1(B_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1392])).

tff(c_1449,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')) = k5_relat_1('#skF_2',k2_funct_2('#skF_1','#skF_2'))
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1433])).

tff(c_1469,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_296,c_295,c_295,c_295,c_1449])).

tff(c_46,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_77,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_297,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_77])).

tff(c_1470,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1469,c_297])).

tff(c_1477,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_1470])).

tff(c_1480,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_54,c_240,c_266,c_699,c_1477])).

tff(c_1481,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1673,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1671,c_1481])).

tff(c_2175,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2135,c_1673])).

tff(c_2182,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_2175])).

tff(c_2185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_54,c_1616,c_1641,c_1584,c_2182])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:10:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.61/1.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.81/1.83  
% 4.81/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.81/1.84  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 4.81/1.84  
% 4.81/1.84  %Foreground sorts:
% 4.81/1.84  
% 4.81/1.84  
% 4.81/1.84  %Background operators:
% 4.81/1.84  
% 4.81/1.84  
% 4.81/1.84  %Foreground operators:
% 4.81/1.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.81/1.84  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.81/1.84  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.81/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.81/1.84  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.81/1.84  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.81/1.84  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 4.81/1.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.81/1.84  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.81/1.84  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.81/1.84  tff('#skF_2', type, '#skF_2': $i).
% 4.81/1.84  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.81/1.84  tff('#skF_1', type, '#skF_1': $i).
% 4.81/1.84  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.81/1.84  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.81/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.81/1.84  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.81/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.81/1.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.81/1.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.81/1.84  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.81/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.81/1.84  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.81/1.84  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 4.81/1.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.81/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.81/1.84  
% 4.89/1.86  tff(f_136, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 4.89/1.86  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.89/1.86  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 4.89/1.86  tff(f_101, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.89/1.86  tff(f_61, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 4.89/1.86  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.89/1.86  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 4.89/1.86  tff(f_123, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.89/1.86  tff(f_45, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 4.89/1.86  tff(f_121, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 4.89/1.86  tff(f_97, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 4.89/1.86  tff(f_111, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.89/1.86  tff(f_35, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 4.89/1.86  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.89/1.86  tff(c_68, plain, (![C_33, A_34, B_35]: (v1_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.89/1.86  tff(c_76, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_68])).
% 4.89/1.86  tff(c_54, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.89/1.86  tff(c_50, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.89/1.86  tff(c_1606, plain, (![C_164, A_165, B_166]: (v2_funct_1(C_164) | ~v3_funct_2(C_164, A_165, B_166) | ~v1_funct_1(C_164) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.89/1.86  tff(c_1612, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1606])).
% 4.89/1.86  tff(c_1616, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_1612])).
% 4.89/1.86  tff(c_38, plain, (![A_20]: (m1_subset_1(k6_partfun1(A_20), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.89/1.86  tff(c_1629, plain, (![A_171, B_172, C_173, D_174]: (r2_relset_1(A_171, B_172, C_173, C_173) | ~m1_subset_1(D_174, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.89/1.86  tff(c_1636, plain, (![A_175, C_176]: (r2_relset_1(A_175, A_175, C_176, C_176) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_175, A_175))))), inference(resolution, [status(thm)], [c_38, c_1629])).
% 4.89/1.86  tff(c_1641, plain, (![A_20]: (r2_relset_1(A_20, A_20, k6_partfun1(A_20), k6_partfun1(A_20)))), inference(resolution, [status(thm)], [c_38, c_1636])).
% 4.89/1.86  tff(c_1493, plain, (![C_142, B_143, A_144]: (v5_relat_1(C_142, B_143) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_144, B_143))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.89/1.86  tff(c_1501, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_1493])).
% 4.89/1.86  tff(c_1526, plain, (![B_150, A_151]: (k2_relat_1(B_150)=A_151 | ~v2_funct_2(B_150, A_151) | ~v5_relat_1(B_150, A_151) | ~v1_relat_1(B_150))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.89/1.86  tff(c_1532, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1501, c_1526])).
% 4.89/1.86  tff(c_1538, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1532])).
% 4.89/1.86  tff(c_1548, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_1538])).
% 4.89/1.86  tff(c_1571, plain, (![C_159, B_160, A_161]: (v2_funct_2(C_159, B_160) | ~v3_funct_2(C_159, A_161, B_160) | ~v1_funct_1(C_159) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_161, B_160))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.89/1.86  tff(c_1577, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1571])).
% 4.89/1.86  tff(c_1581, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_1577])).
% 4.89/1.86  tff(c_1583, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1548, c_1581])).
% 4.89/1.86  tff(c_1584, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_1538])).
% 4.89/1.86  tff(c_44, plain, (![A_29]: (k6_relat_1(A_29)=k6_partfun1(A_29))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.89/1.86  tff(c_6, plain, (![A_2]: (k5_relat_1(k2_funct_1(A_2), A_2)=k6_relat_1(k2_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.89/1.86  tff(c_56, plain, (![A_2]: (k5_relat_1(k2_funct_1(A_2), A_2)=k6_partfun1(k2_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_6])).
% 4.89/1.86  tff(c_52, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.89/1.86  tff(c_1661, plain, (![A_183, B_184]: (k2_funct_2(A_183, B_184)=k2_funct_1(B_184) | ~m1_subset_1(B_184, k1_zfmisc_1(k2_zfmisc_1(A_183, A_183))) | ~v3_funct_2(B_184, A_183, A_183) | ~v1_funct_2(B_184, A_183, A_183) | ~v1_funct_1(B_184))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.89/1.86  tff(c_1667, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1661])).
% 4.89/1.86  tff(c_1671, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_1667])).
% 4.89/1.86  tff(c_1645, plain, (![A_179, B_180]: (v1_funct_1(k2_funct_2(A_179, B_180)) | ~m1_subset_1(B_180, k1_zfmisc_1(k2_zfmisc_1(A_179, A_179))) | ~v3_funct_2(B_180, A_179, A_179) | ~v1_funct_2(B_180, A_179, A_179) | ~v1_funct_1(B_180))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.89/1.86  tff(c_1651, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1645])).
% 4.89/1.86  tff(c_1655, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_1651])).
% 4.89/1.86  tff(c_1672, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1671, c_1655])).
% 4.89/1.86  tff(c_28, plain, (![A_18, B_19]: (m1_subset_1(k2_funct_2(A_18, B_19), k1_zfmisc_1(k2_zfmisc_1(A_18, A_18))) | ~m1_subset_1(B_19, k1_zfmisc_1(k2_zfmisc_1(A_18, A_18))) | ~v3_funct_2(B_19, A_18, A_18) | ~v1_funct_2(B_19, A_18, A_18) | ~v1_funct_1(B_19))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.89/1.86  tff(c_1803, plain, (![F_196, C_195, E_198, A_193, D_194, B_197]: (k1_partfun1(A_193, B_197, C_195, D_194, E_198, F_196)=k5_relat_1(E_198, F_196) | ~m1_subset_1(F_196, k1_zfmisc_1(k2_zfmisc_1(C_195, D_194))) | ~v1_funct_1(F_196) | ~m1_subset_1(E_198, k1_zfmisc_1(k2_zfmisc_1(A_193, B_197))) | ~v1_funct_1(E_198))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.89/1.86  tff(c_1811, plain, (![A_193, B_197, E_198]: (k1_partfun1(A_193, B_197, '#skF_1', '#skF_1', E_198, '#skF_2')=k5_relat_1(E_198, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_198, k1_zfmisc_1(k2_zfmisc_1(A_193, B_197))) | ~v1_funct_1(E_198))), inference(resolution, [status(thm)], [c_48, c_1803])).
% 4.89/1.86  tff(c_1832, plain, (![A_199, B_200, E_201]: (k1_partfun1(A_199, B_200, '#skF_1', '#skF_1', E_201, '#skF_2')=k5_relat_1(E_201, '#skF_2') | ~m1_subset_1(E_201, k1_zfmisc_1(k2_zfmisc_1(A_199, B_200))) | ~v1_funct_1(E_201))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1811])).
% 4.89/1.86  tff(c_2109, plain, (![A_208, B_209]: (k1_partfun1(A_208, A_208, '#skF_1', '#skF_1', k2_funct_2(A_208, B_209), '#skF_2')=k5_relat_1(k2_funct_2(A_208, B_209), '#skF_2') | ~v1_funct_1(k2_funct_2(A_208, B_209)) | ~m1_subset_1(B_209, k1_zfmisc_1(k2_zfmisc_1(A_208, A_208))) | ~v3_funct_2(B_209, A_208, A_208) | ~v1_funct_2(B_209, A_208, A_208) | ~v1_funct_1(B_209))), inference(resolution, [status(thm)], [c_28, c_1832])).
% 4.89/1.86  tff(c_2121, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_2109])).
% 4.89/1.86  tff(c_2135, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_1672, c_1671, c_1671, c_1671, c_2121])).
% 4.89/1.86  tff(c_230, plain, (![C_64, A_65, B_66]: (v2_funct_1(C_64) | ~v3_funct_2(C_64, A_65, B_66) | ~v1_funct_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.89/1.86  tff(c_236, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_230])).
% 4.89/1.86  tff(c_240, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_236])).
% 4.89/1.86  tff(c_254, plain, (![A_72, B_73, C_74, D_75]: (r2_relset_1(A_72, B_73, C_74, C_74) | ~m1_subset_1(D_75, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.89/1.86  tff(c_261, plain, (![A_76, C_77]: (r2_relset_1(A_76, A_76, C_77, C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_76, A_76))))), inference(resolution, [status(thm)], [c_38, c_254])).
% 4.89/1.86  tff(c_266, plain, (![A_20]: (r2_relset_1(A_20, A_20, k6_partfun1(A_20), k6_partfun1(A_20)))), inference(resolution, [status(thm)], [c_38, c_261])).
% 4.89/1.86  tff(c_285, plain, (![A_83, B_84]: (k2_funct_2(A_83, B_84)=k2_funct_1(B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(k2_zfmisc_1(A_83, A_83))) | ~v3_funct_2(B_84, A_83, A_83) | ~v1_funct_2(B_84, A_83, A_83) | ~v1_funct_1(B_84))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.89/1.86  tff(c_291, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_285])).
% 4.89/1.86  tff(c_295, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_291])).
% 4.89/1.86  tff(c_268, plain, (![A_78, B_79]: (v1_funct_1(k2_funct_2(A_78, B_79)) | ~m1_subset_1(B_79, k1_zfmisc_1(k2_zfmisc_1(A_78, A_78))) | ~v3_funct_2(B_79, A_78, A_78) | ~v1_funct_2(B_79, A_78, A_78) | ~v1_funct_1(B_79))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.89/1.86  tff(c_274, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_268])).
% 4.89/1.86  tff(c_278, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_274])).
% 4.89/1.86  tff(c_296, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_295, c_278])).
% 4.89/1.86  tff(c_312, plain, (![A_88, B_89]: (v3_funct_2(k2_funct_2(A_88, B_89), A_88, A_88) | ~m1_subset_1(B_89, k1_zfmisc_1(k2_zfmisc_1(A_88, A_88))) | ~v3_funct_2(B_89, A_88, A_88) | ~v1_funct_2(B_89, A_88, A_88) | ~v1_funct_1(B_89))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.89/1.86  tff(c_316, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_312])).
% 4.89/1.86  tff(c_320, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_295, c_316])).
% 4.89/1.86  tff(c_323, plain, (![A_92, B_93]: (m1_subset_1(k2_funct_2(A_92, B_93), k1_zfmisc_1(k2_zfmisc_1(A_92, A_92))) | ~m1_subset_1(B_93, k1_zfmisc_1(k2_zfmisc_1(A_92, A_92))) | ~v3_funct_2(B_93, A_92, A_92) | ~v1_funct_2(B_93, A_92, A_92) | ~v1_funct_1(B_93))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.89/1.86  tff(c_355, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_295, c_323])).
% 4.89/1.86  tff(c_368, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_355])).
% 4.89/1.86  tff(c_18, plain, (![C_15, B_14, A_13]: (v2_funct_2(C_15, B_14) | ~v3_funct_2(C_15, A_13, B_14) | ~v1_funct_1(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.89/1.86  tff(c_385, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_368, c_18])).
% 4.89/1.86  tff(c_414, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_296, c_320, c_385])).
% 4.89/1.86  tff(c_10, plain, (![C_5, A_3, B_4]: (v1_relat_1(C_5) | ~m1_subset_1(C_5, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.89/1.86  tff(c_420, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_368, c_10])).
% 4.89/1.86  tff(c_12, plain, (![C_8, B_7, A_6]: (v5_relat_1(C_8, B_7) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.89/1.86  tff(c_418, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_368, c_12])).
% 4.89/1.86  tff(c_26, plain, (![B_17, A_16]: (k2_relat_1(B_17)=A_16 | ~v2_funct_2(B_17, A_16) | ~v5_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.89/1.86  tff(c_461, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_418, c_26])).
% 4.89/1.86  tff(c_464, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_420, c_461])).
% 4.89/1.86  tff(c_680, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_414, c_464])).
% 4.89/1.86  tff(c_2, plain, (![A_1]: (k2_relat_1(k2_funct_1(A_1))=k1_relat_1(A_1) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.89/1.86  tff(c_687, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_680, c_2])).
% 4.89/1.86  tff(c_699, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_54, c_240, c_687])).
% 4.89/1.86  tff(c_8, plain, (![A_2]: (k5_relat_1(A_2, k2_funct_1(A_2))=k6_relat_1(k1_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.89/1.86  tff(c_55, plain, (![A_2]: (k5_relat_1(A_2, k2_funct_1(A_2))=k6_partfun1(k1_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_8])).
% 4.89/1.86  tff(c_421, plain, (![B_98, F_97, E_99, C_96, D_95, A_94]: (k1_partfun1(A_94, B_98, C_96, D_95, E_99, F_97)=k5_relat_1(E_99, F_97) | ~m1_subset_1(F_97, k1_zfmisc_1(k2_zfmisc_1(C_96, D_95))) | ~v1_funct_1(F_97) | ~m1_subset_1(E_99, k1_zfmisc_1(k2_zfmisc_1(A_94, B_98))) | ~v1_funct_1(E_99))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.89/1.86  tff(c_1376, plain, (![A_133, A_132, E_131, B_135, B_134]: (k1_partfun1(A_132, B_134, A_133, A_133, E_131, k2_funct_2(A_133, B_135))=k5_relat_1(E_131, k2_funct_2(A_133, B_135)) | ~v1_funct_1(k2_funct_2(A_133, B_135)) | ~m1_subset_1(E_131, k1_zfmisc_1(k2_zfmisc_1(A_132, B_134))) | ~v1_funct_1(E_131) | ~m1_subset_1(B_135, k1_zfmisc_1(k2_zfmisc_1(A_133, A_133))) | ~v3_funct_2(B_135, A_133, A_133) | ~v1_funct_2(B_135, A_133, A_133) | ~v1_funct_1(B_135))), inference(resolution, [status(thm)], [c_28, c_421])).
% 4.89/1.86  tff(c_1392, plain, (![A_133, B_135]: (k1_partfun1('#skF_1', '#skF_1', A_133, A_133, '#skF_2', k2_funct_2(A_133, B_135))=k5_relat_1('#skF_2', k2_funct_2(A_133, B_135)) | ~v1_funct_1(k2_funct_2(A_133, B_135)) | ~v1_funct_1('#skF_2') | ~m1_subset_1(B_135, k1_zfmisc_1(k2_zfmisc_1(A_133, A_133))) | ~v3_funct_2(B_135, A_133, A_133) | ~v1_funct_2(B_135, A_133, A_133) | ~v1_funct_1(B_135))), inference(resolution, [status(thm)], [c_48, c_1376])).
% 4.89/1.86  tff(c_1433, plain, (![A_136, B_137]: (k1_partfun1('#skF_1', '#skF_1', A_136, A_136, '#skF_2', k2_funct_2(A_136, B_137))=k5_relat_1('#skF_2', k2_funct_2(A_136, B_137)) | ~v1_funct_1(k2_funct_2(A_136, B_137)) | ~m1_subset_1(B_137, k1_zfmisc_1(k2_zfmisc_1(A_136, A_136))) | ~v3_funct_2(B_137, A_136, A_136) | ~v1_funct_2(B_137, A_136, A_136) | ~v1_funct_1(B_137))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1392])).
% 4.89/1.86  tff(c_1449, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2'))=k5_relat_1('#skF_2', k2_funct_2('#skF_1', '#skF_2')) | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1433])).
% 4.89/1.86  tff(c_1469, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_296, c_295, c_295, c_295, c_1449])).
% 4.89/1.86  tff(c_46, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.89/1.86  tff(c_77, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_46])).
% 4.89/1.86  tff(c_297, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_295, c_77])).
% 4.89/1.86  tff(c_1470, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1469, c_297])).
% 4.89/1.86  tff(c_1477, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_55, c_1470])).
% 4.89/1.86  tff(c_1480, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_54, c_240, c_266, c_699, c_1477])).
% 4.89/1.86  tff(c_1481, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_46])).
% 4.89/1.86  tff(c_1673, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1671, c_1481])).
% 4.89/1.86  tff(c_2175, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2135, c_1673])).
% 4.89/1.86  tff(c_2182, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_56, c_2175])).
% 4.89/1.86  tff(c_2185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_54, c_1616, c_1641, c_1584, c_2182])).
% 4.89/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.89/1.86  
% 4.89/1.86  Inference rules
% 4.89/1.86  ----------------------
% 4.89/1.86  #Ref     : 0
% 4.89/1.86  #Sup     : 449
% 4.89/1.86  #Fact    : 0
% 4.89/1.86  #Define  : 0
% 4.89/1.86  #Split   : 3
% 4.89/1.86  #Chain   : 0
% 4.89/1.86  #Close   : 0
% 4.89/1.86  
% 4.89/1.86  Ordering : KBO
% 4.89/1.86  
% 4.89/1.86  Simplification rules
% 4.89/1.86  ----------------------
% 4.89/1.86  #Subsume      : 12
% 4.89/1.86  #Demod        : 1040
% 4.89/1.86  #Tautology    : 154
% 4.89/1.86  #SimpNegUnit  : 2
% 4.89/1.86  #BackRed      : 38
% 4.89/1.86  
% 4.89/1.86  #Partial instantiations: 0
% 4.89/1.86  #Strategies tried      : 1
% 4.89/1.86  
% 4.89/1.86  Timing (in seconds)
% 4.89/1.86  ----------------------
% 4.89/1.86  Preprocessing        : 0.33
% 4.89/1.86  Parsing              : 0.18
% 4.89/1.86  CNF conversion       : 0.02
% 4.89/1.86  Main loop            : 0.76
% 4.89/1.86  Inferencing          : 0.26
% 4.89/1.86  Reduction            : 0.29
% 4.89/1.86  Demodulation         : 0.23
% 4.89/1.86  BG Simplification    : 0.03
% 4.89/1.86  Subsumption          : 0.12
% 4.89/1.86  Abstraction          : 0.03
% 4.89/1.86  MUC search           : 0.00
% 4.89/1.86  Cooper               : 0.00
% 4.89/1.87  Total                : 1.13
% 4.89/1.87  Index Insertion      : 0.00
% 4.89/1.87  Index Deletion       : 0.00
% 4.89/1.87  Index Matching       : 0.00
% 4.89/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
