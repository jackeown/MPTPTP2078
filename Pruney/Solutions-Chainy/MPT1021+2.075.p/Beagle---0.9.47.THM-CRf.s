%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:11 EST 2020

% Result     : Theorem 4.82s
% Output     : CNFRefutation 4.82s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 504 expanded)
%              Number of leaves         :   40 ( 210 expanded)
%              Depth                    :   12
%              Number of atoms          :  315 (1606 expanded)
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_141,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_106,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_128,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_126,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_102,axiom,(
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

tff(f_116,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_50,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_71,plain,(
    ! [B_37,A_38] :
      ( v1_relat_1(B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38))
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_77,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_50,c_71])).

tff(c_83,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_77])).

tff(c_56,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_52,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1676,plain,(
    ! [C_168,A_169,B_170] :
      ( v2_funct_1(C_168)
      | ~ v3_funct_2(C_168,A_169,B_170)
      | ~ v1_funct_1(C_168)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1682,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1676])).

tff(c_1686,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_1682])).

tff(c_40,plain,(
    ! [A_22] : m1_subset_1(k6_partfun1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1700,plain,(
    ! [A_176,B_177,C_178,D_179] :
      ( r2_relset_1(A_176,B_177,C_178,C_178)
      | ~ m1_subset_1(D_179,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177)))
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1707,plain,(
    ! [A_180,C_181] :
      ( r2_relset_1(A_180,A_180,C_181,C_181)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_180,A_180))) ) ),
    inference(resolution,[status(thm)],[c_40,c_1700])).

tff(c_1712,plain,(
    ! [A_22] : r2_relset_1(A_22,A_22,k6_partfun1(A_22),k6_partfun1(A_22)) ),
    inference(resolution,[status(thm)],[c_40,c_1707])).

tff(c_1545,plain,(
    ! [C_142,B_143,A_144] :
      ( v5_relat_1(C_142,B_143)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_144,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1553,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_1545])).

tff(c_1587,plain,(
    ! [B_153,A_154] :
      ( k2_relat_1(B_153) = A_154
      | ~ v2_funct_2(B_153,A_154)
      | ~ v5_relat_1(B_153,A_154)
      | ~ v1_relat_1(B_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1593,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1553,c_1587])).

tff(c_1599,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_1593])).

tff(c_1600,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1599])).

tff(c_1632,plain,(
    ! [C_162,B_163,A_164] :
      ( v2_funct_2(C_162,B_163)
      | ~ v3_funct_2(C_162,A_164,B_163)
      | ~ v1_funct_1(C_162)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_164,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1638,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1632])).

tff(c_1642,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_1638])).

tff(c_1644,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1600,c_1642])).

tff(c_1645,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1599])).

tff(c_46,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_10,plain,(
    ! [A_7] :
      ( k5_relat_1(k2_funct_1(A_7),A_7) = k6_relat_1(k2_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_58,plain,(
    ! [A_7] :
      ( k5_relat_1(k2_funct_1(A_7),A_7) = k6_partfun1(k2_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_10])).

tff(c_54,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1731,plain,(
    ! [A_187,B_188] :
      ( k2_funct_2(A_187,B_188) = k2_funct_1(B_188)
      | ~ m1_subset_1(B_188,k1_zfmisc_1(k2_zfmisc_1(A_187,A_187)))
      | ~ v3_funct_2(B_188,A_187,A_187)
      | ~ v1_funct_2(B_188,A_187,A_187)
      | ~ v1_funct_1(B_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1737,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1731])).

tff(c_1741,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_1737])).

tff(c_1714,plain,(
    ! [A_182,B_183] :
      ( v1_funct_1(k2_funct_2(A_182,B_183))
      | ~ m1_subset_1(B_183,k1_zfmisc_1(k2_zfmisc_1(A_182,A_182)))
      | ~ v3_funct_2(B_183,A_182,A_182)
      | ~ v1_funct_2(B_183,A_182,A_182)
      | ~ v1_funct_1(B_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1720,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1714])).

tff(c_1724,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_1720])).

tff(c_1742,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1741,c_1724])).

tff(c_30,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k2_funct_2(A_20,B_21),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ v3_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1818,plain,(
    ! [F_199,A_203,E_200,C_198,D_202,B_201] :
      ( k1_partfun1(A_203,B_201,C_198,D_202,E_200,F_199) = k5_relat_1(E_200,F_199)
      | ~ m1_subset_1(F_199,k1_zfmisc_1(k2_zfmisc_1(C_198,D_202)))
      | ~ v1_funct_1(F_199)
      | ~ m1_subset_1(E_200,k1_zfmisc_1(k2_zfmisc_1(A_203,B_201)))
      | ~ v1_funct_1(E_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1824,plain,(
    ! [A_203,B_201,E_200] :
      ( k1_partfun1(A_203,B_201,'#skF_1','#skF_1',E_200,'#skF_2') = k5_relat_1(E_200,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_200,k1_zfmisc_1(k2_zfmisc_1(A_203,B_201)))
      | ~ v1_funct_1(E_200) ) ),
    inference(resolution,[status(thm)],[c_50,c_1818])).

tff(c_1889,plain,(
    ! [A_204,B_205,E_206] :
      ( k1_partfun1(A_204,B_205,'#skF_1','#skF_1',E_206,'#skF_2') = k5_relat_1(E_206,'#skF_2')
      | ~ m1_subset_1(E_206,k1_zfmisc_1(k2_zfmisc_1(A_204,B_205)))
      | ~ v1_funct_1(E_206) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1824])).

tff(c_2124,plain,(
    ! [A_214,B_215] :
      ( k1_partfun1(A_214,A_214,'#skF_1','#skF_1',k2_funct_2(A_214,B_215),'#skF_2') = k5_relat_1(k2_funct_2(A_214,B_215),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_214,B_215))
      | ~ m1_subset_1(B_215,k1_zfmisc_1(k2_zfmisc_1(A_214,A_214)))
      | ~ v3_funct_2(B_215,A_214,A_214)
      | ~ v1_funct_2(B_215,A_214,A_214)
      | ~ v1_funct_1(B_215) ) ),
    inference(resolution,[status(thm)],[c_30,c_1889])).

tff(c_2134,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_2124])).

tff(c_2145,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_1742,c_1741,c_1741,c_1741,c_2134])).

tff(c_229,plain,(
    ! [C_67,A_68,B_69] :
      ( v2_funct_1(C_67)
      | ~ v3_funct_2(C_67,A_68,B_69)
      | ~ v1_funct_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_235,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_229])).

tff(c_239,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_235])).

tff(c_262,plain,(
    ! [A_76,B_77,C_78,D_79] :
      ( r2_relset_1(A_76,B_77,C_78,C_78)
      | ~ m1_subset_1(D_79,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77)))
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_269,plain,(
    ! [A_80,C_81] :
      ( r2_relset_1(A_80,A_80,C_81,C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_80,A_80))) ) ),
    inference(resolution,[status(thm)],[c_40,c_262])).

tff(c_274,plain,(
    ! [A_22] : r2_relset_1(A_22,A_22,k6_partfun1(A_22),k6_partfun1(A_22)) ),
    inference(resolution,[status(thm)],[c_40,c_269])).

tff(c_293,plain,(
    ! [A_87,B_88] :
      ( k2_funct_2(A_87,B_88) = k2_funct_1(B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(k2_zfmisc_1(A_87,A_87)))
      | ~ v3_funct_2(B_88,A_87,A_87)
      | ~ v1_funct_2(B_88,A_87,A_87)
      | ~ v1_funct_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_299,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_293])).

tff(c_303,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_299])).

tff(c_277,plain,(
    ! [A_83,B_84] :
      ( v1_funct_1(k2_funct_2(A_83,B_84))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(k2_zfmisc_1(A_83,A_83)))
      | ~ v3_funct_2(B_84,A_83,A_83)
      | ~ v1_funct_2(B_84,A_83,A_83)
      | ~ v1_funct_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_283,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_277])).

tff(c_287,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_283])).

tff(c_313,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_287])).

tff(c_322,plain,(
    ! [A_93,B_94] :
      ( v3_funct_2(k2_funct_2(A_93,B_94),A_93,A_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(k2_zfmisc_1(A_93,A_93)))
      | ~ v3_funct_2(B_94,A_93,A_93)
      | ~ v1_funct_2(B_94,A_93,A_93)
      | ~ v1_funct_1(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_326,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_322])).

tff(c_330,plain,(
    v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_303,c_326])).

tff(c_332,plain,(
    ! [A_96,B_97] :
      ( m1_subset_1(k2_funct_2(A_96,B_97),k1_zfmisc_1(k2_zfmisc_1(A_96,A_96)))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(k2_zfmisc_1(A_96,A_96)))
      | ~ v3_funct_2(B_97,A_96,A_96)
      | ~ v1_funct_2(B_97,A_96,A_96)
      | ~ v1_funct_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_364,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_332])).

tff(c_379,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_364])).

tff(c_20,plain,(
    ! [C_17,B_16,A_15] :
      ( v2_funct_2(C_17,B_16)
      | ~ v3_funct_2(C_17,A_15,B_16)
      | ~ v1_funct_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_396,plain,
    ( v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_379,c_20])).

tff(c_425,plain,(
    v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_330,c_396])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_408,plain,
    ( v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_379,c_2])).

tff(c_433,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_408])).

tff(c_14,plain,(
    ! [C_10,B_9,A_8] :
      ( v5_relat_1(C_10,B_9)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_430,plain,(
    v5_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_379,c_14])).

tff(c_28,plain,(
    ! [B_19,A_18] :
      ( k2_relat_1(B_19) = A_18
      | ~ v2_funct_2(B_19,A_18)
      | ~ v5_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_436,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_430,c_28])).

tff(c_439,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_436])).

tff(c_491,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_439])).

tff(c_6,plain,(
    ! [A_6] :
      ( k2_relat_1(k2_funct_1(A_6)) = k1_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_498,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_491,c_6])).

tff(c_510,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_56,c_239,c_498])).

tff(c_12,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k2_funct_1(A_7)) = k6_relat_1(k1_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_57,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k2_funct_1(A_7)) = k6_partfun1(k1_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_12])).

tff(c_450,plain,(
    ! [E_100,B_101,A_103,C_98,F_99,D_102] :
      ( k1_partfun1(A_103,B_101,C_98,D_102,E_100,F_99) = k5_relat_1(E_100,F_99)
      | ~ m1_subset_1(F_99,k1_zfmisc_1(k2_zfmisc_1(C_98,D_102)))
      | ~ v1_funct_1(F_99)
      | ~ m1_subset_1(E_100,k1_zfmisc_1(k2_zfmisc_1(A_103,B_101)))
      | ~ v1_funct_1(E_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1450,plain,(
    ! [A_134,B_133,B_136,A_137,E_135] :
      ( k1_partfun1(A_134,B_133,A_137,A_137,E_135,k2_funct_2(A_137,B_136)) = k5_relat_1(E_135,k2_funct_2(A_137,B_136))
      | ~ v1_funct_1(k2_funct_2(A_137,B_136))
      | ~ m1_subset_1(E_135,k1_zfmisc_1(k2_zfmisc_1(A_134,B_133)))
      | ~ v1_funct_1(E_135)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(k2_zfmisc_1(A_137,A_137)))
      | ~ v3_funct_2(B_136,A_137,A_137)
      | ~ v1_funct_2(B_136,A_137,A_137)
      | ~ v1_funct_1(B_136) ) ),
    inference(resolution,[status(thm)],[c_30,c_450])).

tff(c_1466,plain,(
    ! [A_137,B_136] :
      ( k1_partfun1('#skF_1','#skF_1',A_137,A_137,'#skF_2',k2_funct_2(A_137,B_136)) = k5_relat_1('#skF_2',k2_funct_2(A_137,B_136))
      | ~ v1_funct_1(k2_funct_2(A_137,B_136))
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(B_136,k1_zfmisc_1(k2_zfmisc_1(A_137,A_137)))
      | ~ v3_funct_2(B_136,A_137,A_137)
      | ~ v1_funct_2(B_136,A_137,A_137)
      | ~ v1_funct_1(B_136) ) ),
    inference(resolution,[status(thm)],[c_50,c_1450])).

tff(c_1487,plain,(
    ! [A_138,B_139] :
      ( k1_partfun1('#skF_1','#skF_1',A_138,A_138,'#skF_2',k2_funct_2(A_138,B_139)) = k5_relat_1('#skF_2',k2_funct_2(A_138,B_139))
      | ~ v1_funct_1(k2_funct_2(A_138,B_139))
      | ~ m1_subset_1(B_139,k1_zfmisc_1(k2_zfmisc_1(A_138,A_138)))
      | ~ v3_funct_2(B_139,A_138,A_138)
      | ~ v1_funct_2(B_139,A_138,A_138)
      | ~ v1_funct_1(B_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1466])).

tff(c_1503,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')) = k5_relat_1('#skF_2',k2_funct_2('#skF_1','#skF_2'))
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1487])).

tff(c_1523,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_313,c_303,c_303,c_303,c_1503])).

tff(c_48,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_84,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_314,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_84])).

tff(c_1531,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1523,c_314])).

tff(c_1538,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_1531])).

tff(c_1541,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_56,c_239,c_274,c_510,c_1538])).

tff(c_1542,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1743,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1741,c_1542])).

tff(c_2168,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2145,c_1743])).

tff(c_2175,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_2168])).

tff(c_2178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_56,c_1686,c_1712,c_1645,c_2175])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:05:26 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.82/1.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.82/1.88  
% 4.82/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.82/1.88  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 4.82/1.88  
% 4.82/1.88  %Foreground sorts:
% 4.82/1.88  
% 4.82/1.88  
% 4.82/1.88  %Background operators:
% 4.82/1.88  
% 4.82/1.88  
% 4.82/1.88  %Foreground operators:
% 4.82/1.88  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.82/1.88  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.82/1.88  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.82/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.82/1.88  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.82/1.88  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.82/1.88  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 4.82/1.88  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.82/1.88  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.82/1.88  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.82/1.88  tff('#skF_2', type, '#skF_2': $i).
% 4.82/1.88  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.82/1.88  tff('#skF_1', type, '#skF_1': $i).
% 4.82/1.88  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.82/1.88  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.82/1.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.82/1.88  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.82/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.82/1.88  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.82/1.88  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.82/1.88  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.82/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.82/1.88  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.82/1.88  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 4.82/1.88  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.82/1.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.82/1.88  
% 4.82/1.90  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.82/1.90  tff(f_141, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 4.82/1.90  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.82/1.90  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 4.82/1.90  tff(f_106, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.82/1.90  tff(f_66, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 4.82/1.90  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.82/1.90  tff(f_86, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 4.82/1.90  tff(f_128, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.82/1.90  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 4.82/1.90  tff(f_126, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 4.82/1.90  tff(f_102, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 4.82/1.90  tff(f_116, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.82/1.90  tff(f_44, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 4.82/1.90  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.82/1.90  tff(c_50, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.82/1.90  tff(c_71, plain, (![B_37, A_38]: (v1_relat_1(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.82/1.90  tff(c_77, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_50, c_71])).
% 4.82/1.90  tff(c_83, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_77])).
% 4.82/1.90  tff(c_56, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.82/1.90  tff(c_52, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.82/1.90  tff(c_1676, plain, (![C_168, A_169, B_170]: (v2_funct_1(C_168) | ~v3_funct_2(C_168, A_169, B_170) | ~v1_funct_1(C_168) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.82/1.90  tff(c_1682, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1676])).
% 4.82/1.90  tff(c_1686, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_1682])).
% 4.82/1.90  tff(c_40, plain, (![A_22]: (m1_subset_1(k6_partfun1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.82/1.90  tff(c_1700, plain, (![A_176, B_177, C_178, D_179]: (r2_relset_1(A_176, B_177, C_178, C_178) | ~m1_subset_1(D_179, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))) | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.82/1.90  tff(c_1707, plain, (![A_180, C_181]: (r2_relset_1(A_180, A_180, C_181, C_181) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_180, A_180))))), inference(resolution, [status(thm)], [c_40, c_1700])).
% 4.82/1.90  tff(c_1712, plain, (![A_22]: (r2_relset_1(A_22, A_22, k6_partfun1(A_22), k6_partfun1(A_22)))), inference(resolution, [status(thm)], [c_40, c_1707])).
% 4.82/1.90  tff(c_1545, plain, (![C_142, B_143, A_144]: (v5_relat_1(C_142, B_143) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_144, B_143))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.82/1.90  tff(c_1553, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_1545])).
% 4.82/1.90  tff(c_1587, plain, (![B_153, A_154]: (k2_relat_1(B_153)=A_154 | ~v2_funct_2(B_153, A_154) | ~v5_relat_1(B_153, A_154) | ~v1_relat_1(B_153))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.82/1.90  tff(c_1593, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1553, c_1587])).
% 4.82/1.90  tff(c_1599, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_1593])).
% 4.82/1.90  tff(c_1600, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_1599])).
% 4.82/1.90  tff(c_1632, plain, (![C_162, B_163, A_164]: (v2_funct_2(C_162, B_163) | ~v3_funct_2(C_162, A_164, B_163) | ~v1_funct_1(C_162) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_164, B_163))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.82/1.90  tff(c_1638, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1632])).
% 4.82/1.90  tff(c_1642, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_1638])).
% 4.82/1.90  tff(c_1644, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1600, c_1642])).
% 4.82/1.90  tff(c_1645, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_1599])).
% 4.82/1.90  tff(c_46, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.82/1.90  tff(c_10, plain, (![A_7]: (k5_relat_1(k2_funct_1(A_7), A_7)=k6_relat_1(k2_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.82/1.90  tff(c_58, plain, (![A_7]: (k5_relat_1(k2_funct_1(A_7), A_7)=k6_partfun1(k2_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_10])).
% 4.82/1.90  tff(c_54, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.82/1.90  tff(c_1731, plain, (![A_187, B_188]: (k2_funct_2(A_187, B_188)=k2_funct_1(B_188) | ~m1_subset_1(B_188, k1_zfmisc_1(k2_zfmisc_1(A_187, A_187))) | ~v3_funct_2(B_188, A_187, A_187) | ~v1_funct_2(B_188, A_187, A_187) | ~v1_funct_1(B_188))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.82/1.90  tff(c_1737, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1731])).
% 4.82/1.90  tff(c_1741, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_1737])).
% 4.82/1.90  tff(c_1714, plain, (![A_182, B_183]: (v1_funct_1(k2_funct_2(A_182, B_183)) | ~m1_subset_1(B_183, k1_zfmisc_1(k2_zfmisc_1(A_182, A_182))) | ~v3_funct_2(B_183, A_182, A_182) | ~v1_funct_2(B_183, A_182, A_182) | ~v1_funct_1(B_183))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.82/1.90  tff(c_1720, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1714])).
% 4.82/1.90  tff(c_1724, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_1720])).
% 4.82/1.90  tff(c_1742, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1741, c_1724])).
% 4.82/1.90  tff(c_30, plain, (![A_20, B_21]: (m1_subset_1(k2_funct_2(A_20, B_21), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~v3_funct_2(B_21, A_20, A_20) | ~v1_funct_2(B_21, A_20, A_20) | ~v1_funct_1(B_21))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.82/1.90  tff(c_1818, plain, (![F_199, A_203, E_200, C_198, D_202, B_201]: (k1_partfun1(A_203, B_201, C_198, D_202, E_200, F_199)=k5_relat_1(E_200, F_199) | ~m1_subset_1(F_199, k1_zfmisc_1(k2_zfmisc_1(C_198, D_202))) | ~v1_funct_1(F_199) | ~m1_subset_1(E_200, k1_zfmisc_1(k2_zfmisc_1(A_203, B_201))) | ~v1_funct_1(E_200))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.82/1.90  tff(c_1824, plain, (![A_203, B_201, E_200]: (k1_partfun1(A_203, B_201, '#skF_1', '#skF_1', E_200, '#skF_2')=k5_relat_1(E_200, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_200, k1_zfmisc_1(k2_zfmisc_1(A_203, B_201))) | ~v1_funct_1(E_200))), inference(resolution, [status(thm)], [c_50, c_1818])).
% 4.82/1.90  tff(c_1889, plain, (![A_204, B_205, E_206]: (k1_partfun1(A_204, B_205, '#skF_1', '#skF_1', E_206, '#skF_2')=k5_relat_1(E_206, '#skF_2') | ~m1_subset_1(E_206, k1_zfmisc_1(k2_zfmisc_1(A_204, B_205))) | ~v1_funct_1(E_206))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1824])).
% 4.82/1.90  tff(c_2124, plain, (![A_214, B_215]: (k1_partfun1(A_214, A_214, '#skF_1', '#skF_1', k2_funct_2(A_214, B_215), '#skF_2')=k5_relat_1(k2_funct_2(A_214, B_215), '#skF_2') | ~v1_funct_1(k2_funct_2(A_214, B_215)) | ~m1_subset_1(B_215, k1_zfmisc_1(k2_zfmisc_1(A_214, A_214))) | ~v3_funct_2(B_215, A_214, A_214) | ~v1_funct_2(B_215, A_214, A_214) | ~v1_funct_1(B_215))), inference(resolution, [status(thm)], [c_30, c_1889])).
% 4.82/1.90  tff(c_2134, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_2124])).
% 4.82/1.90  tff(c_2145, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_1742, c_1741, c_1741, c_1741, c_2134])).
% 4.82/1.90  tff(c_229, plain, (![C_67, A_68, B_69]: (v2_funct_1(C_67) | ~v3_funct_2(C_67, A_68, B_69) | ~v1_funct_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.82/1.90  tff(c_235, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_229])).
% 4.82/1.90  tff(c_239, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_235])).
% 4.82/1.90  tff(c_262, plain, (![A_76, B_77, C_78, D_79]: (r2_relset_1(A_76, B_77, C_78, C_78) | ~m1_subset_1(D_79, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.82/1.90  tff(c_269, plain, (![A_80, C_81]: (r2_relset_1(A_80, A_80, C_81, C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_80, A_80))))), inference(resolution, [status(thm)], [c_40, c_262])).
% 4.82/1.90  tff(c_274, plain, (![A_22]: (r2_relset_1(A_22, A_22, k6_partfun1(A_22), k6_partfun1(A_22)))), inference(resolution, [status(thm)], [c_40, c_269])).
% 4.82/1.90  tff(c_293, plain, (![A_87, B_88]: (k2_funct_2(A_87, B_88)=k2_funct_1(B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(k2_zfmisc_1(A_87, A_87))) | ~v3_funct_2(B_88, A_87, A_87) | ~v1_funct_2(B_88, A_87, A_87) | ~v1_funct_1(B_88))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.82/1.90  tff(c_299, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_293])).
% 4.82/1.90  tff(c_303, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_299])).
% 4.82/1.90  tff(c_277, plain, (![A_83, B_84]: (v1_funct_1(k2_funct_2(A_83, B_84)) | ~m1_subset_1(B_84, k1_zfmisc_1(k2_zfmisc_1(A_83, A_83))) | ~v3_funct_2(B_84, A_83, A_83) | ~v1_funct_2(B_84, A_83, A_83) | ~v1_funct_1(B_84))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.82/1.90  tff(c_283, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_277])).
% 4.82/1.90  tff(c_287, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_283])).
% 4.82/1.90  tff(c_313, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_303, c_287])).
% 4.82/1.90  tff(c_322, plain, (![A_93, B_94]: (v3_funct_2(k2_funct_2(A_93, B_94), A_93, A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(k2_zfmisc_1(A_93, A_93))) | ~v3_funct_2(B_94, A_93, A_93) | ~v1_funct_2(B_94, A_93, A_93) | ~v1_funct_1(B_94))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.82/1.90  tff(c_326, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_322])).
% 4.82/1.90  tff(c_330, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_303, c_326])).
% 4.82/1.90  tff(c_332, plain, (![A_96, B_97]: (m1_subset_1(k2_funct_2(A_96, B_97), k1_zfmisc_1(k2_zfmisc_1(A_96, A_96))) | ~m1_subset_1(B_97, k1_zfmisc_1(k2_zfmisc_1(A_96, A_96))) | ~v3_funct_2(B_97, A_96, A_96) | ~v1_funct_2(B_97, A_96, A_96) | ~v1_funct_1(B_97))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.82/1.90  tff(c_364, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_303, c_332])).
% 4.82/1.90  tff(c_379, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_364])).
% 4.82/1.90  tff(c_20, plain, (![C_17, B_16, A_15]: (v2_funct_2(C_17, B_16) | ~v3_funct_2(C_17, A_15, B_16) | ~v1_funct_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.82/1.90  tff(c_396, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_379, c_20])).
% 4.82/1.90  tff(c_425, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_313, c_330, c_396])).
% 4.82/1.90  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.82/1.90  tff(c_408, plain, (v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_379, c_2])).
% 4.82/1.90  tff(c_433, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_408])).
% 4.82/1.90  tff(c_14, plain, (![C_10, B_9, A_8]: (v5_relat_1(C_10, B_9) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.82/1.90  tff(c_430, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_379, c_14])).
% 4.82/1.90  tff(c_28, plain, (![B_19, A_18]: (k2_relat_1(B_19)=A_18 | ~v2_funct_2(B_19, A_18) | ~v5_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.82/1.90  tff(c_436, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_430, c_28])).
% 4.82/1.90  tff(c_439, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_433, c_436])).
% 4.82/1.90  tff(c_491, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_425, c_439])).
% 4.82/1.90  tff(c_6, plain, (![A_6]: (k2_relat_1(k2_funct_1(A_6))=k1_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.82/1.90  tff(c_498, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_491, c_6])).
% 4.82/1.90  tff(c_510, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_83, c_56, c_239, c_498])).
% 4.82/1.90  tff(c_12, plain, (![A_7]: (k5_relat_1(A_7, k2_funct_1(A_7))=k6_relat_1(k1_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.82/1.90  tff(c_57, plain, (![A_7]: (k5_relat_1(A_7, k2_funct_1(A_7))=k6_partfun1(k1_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_12])).
% 4.82/1.90  tff(c_450, plain, (![E_100, B_101, A_103, C_98, F_99, D_102]: (k1_partfun1(A_103, B_101, C_98, D_102, E_100, F_99)=k5_relat_1(E_100, F_99) | ~m1_subset_1(F_99, k1_zfmisc_1(k2_zfmisc_1(C_98, D_102))) | ~v1_funct_1(F_99) | ~m1_subset_1(E_100, k1_zfmisc_1(k2_zfmisc_1(A_103, B_101))) | ~v1_funct_1(E_100))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.82/1.90  tff(c_1450, plain, (![A_134, B_133, B_136, A_137, E_135]: (k1_partfun1(A_134, B_133, A_137, A_137, E_135, k2_funct_2(A_137, B_136))=k5_relat_1(E_135, k2_funct_2(A_137, B_136)) | ~v1_funct_1(k2_funct_2(A_137, B_136)) | ~m1_subset_1(E_135, k1_zfmisc_1(k2_zfmisc_1(A_134, B_133))) | ~v1_funct_1(E_135) | ~m1_subset_1(B_136, k1_zfmisc_1(k2_zfmisc_1(A_137, A_137))) | ~v3_funct_2(B_136, A_137, A_137) | ~v1_funct_2(B_136, A_137, A_137) | ~v1_funct_1(B_136))), inference(resolution, [status(thm)], [c_30, c_450])).
% 4.82/1.90  tff(c_1466, plain, (![A_137, B_136]: (k1_partfun1('#skF_1', '#skF_1', A_137, A_137, '#skF_2', k2_funct_2(A_137, B_136))=k5_relat_1('#skF_2', k2_funct_2(A_137, B_136)) | ~v1_funct_1(k2_funct_2(A_137, B_136)) | ~v1_funct_1('#skF_2') | ~m1_subset_1(B_136, k1_zfmisc_1(k2_zfmisc_1(A_137, A_137))) | ~v3_funct_2(B_136, A_137, A_137) | ~v1_funct_2(B_136, A_137, A_137) | ~v1_funct_1(B_136))), inference(resolution, [status(thm)], [c_50, c_1450])).
% 4.82/1.90  tff(c_1487, plain, (![A_138, B_139]: (k1_partfun1('#skF_1', '#skF_1', A_138, A_138, '#skF_2', k2_funct_2(A_138, B_139))=k5_relat_1('#skF_2', k2_funct_2(A_138, B_139)) | ~v1_funct_1(k2_funct_2(A_138, B_139)) | ~m1_subset_1(B_139, k1_zfmisc_1(k2_zfmisc_1(A_138, A_138))) | ~v3_funct_2(B_139, A_138, A_138) | ~v1_funct_2(B_139, A_138, A_138) | ~v1_funct_1(B_139))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1466])).
% 4.82/1.90  tff(c_1503, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2'))=k5_relat_1('#skF_2', k2_funct_2('#skF_1', '#skF_2')) | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1487])).
% 4.82/1.90  tff(c_1523, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_313, c_303, c_303, c_303, c_1503])).
% 4.82/1.90  tff(c_48, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.82/1.90  tff(c_84, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_48])).
% 4.82/1.90  tff(c_314, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_303, c_84])).
% 4.82/1.90  tff(c_1531, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1523, c_314])).
% 4.82/1.90  tff(c_1538, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_57, c_1531])).
% 4.82/1.90  tff(c_1541, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_56, c_239, c_274, c_510, c_1538])).
% 4.82/1.90  tff(c_1542, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_48])).
% 4.82/1.90  tff(c_1743, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1741, c_1542])).
% 4.82/1.90  tff(c_2168, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2145, c_1743])).
% 4.82/1.90  tff(c_2175, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_58, c_2168])).
% 4.82/1.90  tff(c_2178, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_56, c_1686, c_1712, c_1645, c_2175])).
% 4.82/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.82/1.90  
% 4.82/1.90  Inference rules
% 4.82/1.90  ----------------------
% 4.82/1.90  #Ref     : 0
% 4.82/1.90  #Sup     : 445
% 4.82/1.90  #Fact    : 0
% 4.82/1.90  #Define  : 0
% 4.82/1.90  #Split   : 3
% 4.82/1.90  #Chain   : 0
% 4.82/1.90  #Close   : 0
% 4.82/1.90  
% 4.82/1.90  Ordering : KBO
% 4.82/1.90  
% 4.82/1.90  Simplification rules
% 4.82/1.90  ----------------------
% 4.82/1.90  #Subsume      : 11
% 4.82/1.90  #Demod        : 1026
% 4.82/1.90  #Tautology    : 166
% 4.82/1.90  #SimpNegUnit  : 2
% 4.82/1.90  #BackRed      : 45
% 4.82/1.90  
% 4.82/1.90  #Partial instantiations: 0
% 4.82/1.90  #Strategies tried      : 1
% 4.82/1.90  
% 4.82/1.90  Timing (in seconds)
% 4.82/1.90  ----------------------
% 5.24/1.91  Preprocessing        : 0.34
% 5.24/1.91  Parsing              : 0.18
% 5.24/1.91  CNF conversion       : 0.02
% 5.24/1.91  Main loop            : 0.81
% 5.24/1.91  Inferencing          : 0.28
% 5.24/1.91  Reduction            : 0.30
% 5.24/1.91  Demodulation         : 0.23
% 5.24/1.91  BG Simplification    : 0.03
% 5.24/1.91  Subsumption          : 0.13
% 5.24/1.91  Abstraction          : 0.03
% 5.24/1.91  MUC search           : 0.00
% 5.24/1.91  Cooper               : 0.00
% 5.24/1.91  Total                : 1.20
% 5.24/1.91  Index Insertion      : 0.00
% 5.24/1.91  Index Deletion       : 0.00
% 5.24/1.91  Index Matching       : 0.00
% 5.24/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
