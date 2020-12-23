%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:12 EST 2020

% Result     : Theorem 4.94s
% Output     : CNFRefutation 4.94s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 514 expanded)
%              Number of leaves         :   39 ( 213 expanded)
%              Depth                    :   11
%              Number of atoms          :  313 (1612 expanded)
%              Number of equality atoms :   41 ( 112 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_139,negated_conjecture,(
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

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_126,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_68,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

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

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_124,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_104,axiom,(
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

tff(f_114,axiom,(
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

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_69,plain,(
    ! [B_36,A_37] :
      ( v1_relat_1(B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_37))
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_75,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_48,c_69])).

tff(c_81,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_75])).

tff(c_54,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_50,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1595,plain,(
    ! [C_165,A_166,B_167] :
      ( v2_funct_1(C_165)
      | ~ v3_funct_2(C_165,A_166,B_167)
      | ~ v1_funct_1(C_165)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1601,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1595])).

tff(c_1605,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_1601])).

tff(c_44,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_20,plain,(
    ! [A_15] : m1_subset_1(k6_relat_1(A_15),k1_zfmisc_1(k2_zfmisc_1(A_15,A_15))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_55,plain,(
    ! [A_15] : m1_subset_1(k6_partfun1(A_15),k1_zfmisc_1(k2_zfmisc_1(A_15,A_15))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_20])).

tff(c_1619,plain,(
    ! [A_173,B_174,C_175,D_176] :
      ( r2_relset_1(A_173,B_174,C_175,C_175)
      | ~ m1_subset_1(D_176,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174)))
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1634,plain,(
    ! [A_178,C_179] :
      ( r2_relset_1(A_178,A_178,C_179,C_179)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_178,A_178))) ) ),
    inference(resolution,[status(thm)],[c_55,c_1619])).

tff(c_1639,plain,(
    ! [A_15] : r2_relset_1(A_15,A_15,k6_partfun1(A_15),k6_partfun1(A_15)) ),
    inference(resolution,[status(thm)],[c_55,c_1634])).

tff(c_1443,plain,(
    ! [C_137,B_138,A_139] :
      ( v5_relat_1(C_137,B_138)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_139,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1451,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_1443])).

tff(c_1464,plain,(
    ! [B_146,A_147] :
      ( k2_relat_1(B_146) = A_147
      | ~ v2_funct_2(B_146,A_147)
      | ~ v5_relat_1(B_146,A_147)
      | ~ v1_relat_1(B_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1470,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1451,c_1464])).

tff(c_1476,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_1470])).

tff(c_1477,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1476])).

tff(c_1530,plain,(
    ! [C_157,B_158,A_159] :
      ( v2_funct_2(C_157,B_158)
      | ~ v3_funct_2(C_157,A_159,B_158)
      | ~ v1_funct_1(C_157)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_159,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1536,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1530])).

tff(c_1540,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_1536])).

tff(c_1542,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1477,c_1540])).

tff(c_1543,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1476])).

tff(c_10,plain,(
    ! [A_7] :
      ( k5_relat_1(k2_funct_1(A_7),A_7) = k6_relat_1(k2_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_57,plain,(
    ! [A_7] :
      ( k5_relat_1(k2_funct_1(A_7),A_7) = k6_partfun1(k2_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_10])).

tff(c_52,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1655,plain,(
    ! [A_183,B_184] :
      ( k2_funct_2(A_183,B_184) = k2_funct_1(B_184)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(k2_zfmisc_1(A_183,A_183)))
      | ~ v3_funct_2(B_184,A_183,A_183)
      | ~ v1_funct_2(B_184,A_183,A_183)
      | ~ v1_funct_1(B_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1661,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1655])).

tff(c_1665,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_1661])).

tff(c_1644,plain,(
    ! [A_181,B_182] :
      ( v1_funct_1(k2_funct_2(A_181,B_182))
      | ~ m1_subset_1(B_182,k1_zfmisc_1(k2_zfmisc_1(A_181,A_181)))
      | ~ v3_funct_2(B_182,A_181,A_181)
      | ~ v1_funct_2(B_182,A_181,A_181)
      | ~ v1_funct_1(B_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1650,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1644])).

tff(c_1654,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_1650])).

tff(c_1666,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1665,c_1654])).

tff(c_32,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(k2_funct_2(A_21,B_22),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21)))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k2_zfmisc_1(A_21,A_21)))
      | ~ v3_funct_2(B_22,A_21,A_21)
      | ~ v1_funct_2(B_22,A_21,A_21)
      | ~ v1_funct_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1806,plain,(
    ! [E_197,F_196,A_200,C_195,D_199,B_198] :
      ( k1_partfun1(A_200,B_198,C_195,D_199,E_197,F_196) = k5_relat_1(E_197,F_196)
      | ~ m1_subset_1(F_196,k1_zfmisc_1(k2_zfmisc_1(C_195,D_199)))
      | ~ v1_funct_1(F_196)
      | ~ m1_subset_1(E_197,k1_zfmisc_1(k2_zfmisc_1(A_200,B_198)))
      | ~ v1_funct_1(E_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1814,plain,(
    ! [A_200,B_198,E_197] :
      ( k1_partfun1(A_200,B_198,'#skF_1','#skF_1',E_197,'#skF_2') = k5_relat_1(E_197,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_197,k1_zfmisc_1(k2_zfmisc_1(A_200,B_198)))
      | ~ v1_funct_1(E_197) ) ),
    inference(resolution,[status(thm)],[c_48,c_1806])).

tff(c_1823,plain,(
    ! [A_201,B_202,E_203] :
      ( k1_partfun1(A_201,B_202,'#skF_1','#skF_1',E_203,'#skF_2') = k5_relat_1(E_203,'#skF_2')
      | ~ m1_subset_1(E_203,k1_zfmisc_1(k2_zfmisc_1(A_201,B_202)))
      | ~ v1_funct_1(E_203) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1814])).

tff(c_2031,plain,(
    ! [A_210,B_211] :
      ( k1_partfun1(A_210,A_210,'#skF_1','#skF_1',k2_funct_2(A_210,B_211),'#skF_2') = k5_relat_1(k2_funct_2(A_210,B_211),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_210,B_211))
      | ~ m1_subset_1(B_211,k1_zfmisc_1(k2_zfmisc_1(A_210,A_210)))
      | ~ v3_funct_2(B_211,A_210,A_210)
      | ~ v1_funct_2(B_211,A_210,A_210)
      | ~ v1_funct_1(B_211) ) ),
    inference(resolution,[status(thm)],[c_32,c_1823])).

tff(c_2041,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_2031])).

tff(c_2052,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_1666,c_1665,c_1665,c_1665,c_2041])).

tff(c_214,plain,(
    ! [C_64,A_65,B_66] :
      ( v2_funct_1(C_64)
      | ~ v3_funct_2(C_64,A_65,B_66)
      | ~ v1_funct_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_220,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_214])).

tff(c_224,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_220])).

tff(c_238,plain,(
    ! [A_72,B_73,C_74,D_75] :
      ( r2_relset_1(A_72,B_73,C_74,C_74)
      | ~ m1_subset_1(D_75,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73)))
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_245,plain,(
    ! [A_76,C_77] :
      ( r2_relset_1(A_76,A_76,C_77,C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_76,A_76))) ) ),
    inference(resolution,[status(thm)],[c_55,c_238])).

tff(c_250,plain,(
    ! [A_15] : r2_relset_1(A_15,A_15,k6_partfun1(A_15),k6_partfun1(A_15)) ),
    inference(resolution,[status(thm)],[c_55,c_245])).

tff(c_265,plain,(
    ! [A_82,B_83] :
      ( k2_funct_2(A_82,B_83) = k2_funct_1(B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k2_zfmisc_1(A_82,A_82)))
      | ~ v3_funct_2(B_83,A_82,A_82)
      | ~ v1_funct_2(B_83,A_82,A_82)
      | ~ v1_funct_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_271,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_265])).

tff(c_275,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_271])).

tff(c_307,plain,(
    ! [A_92,B_93] :
      ( m1_subset_1(k2_funct_2(A_92,B_93),k1_zfmisc_1(k2_zfmisc_1(A_92,A_92)))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k2_zfmisc_1(A_92,A_92)))
      | ~ v3_funct_2(B_93,A_92,A_92)
      | ~ v1_funct_2(B_93,A_92,A_92)
      | ~ v1_funct_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_339,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_307])).

tff(c_354,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_339])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_383,plain,
    ( v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_354,c_2])).

tff(c_408,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_383])).

tff(c_253,plain,(
    ! [A_79,B_80] :
      ( v1_funct_1(k2_funct_2(A_79,B_80))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k2_zfmisc_1(A_79,A_79)))
      | ~ v3_funct_2(B_80,A_79,A_79)
      | ~ v1_funct_2(B_80,A_79,A_79)
      | ~ v1_funct_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_259,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_253])).

tff(c_263,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_259])).

tff(c_276,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_263])).

tff(c_297,plain,(
    ! [A_89,B_90] :
      ( v3_funct_2(k2_funct_2(A_89,B_90),A_89,A_89)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(k2_zfmisc_1(A_89,A_89)))
      | ~ v3_funct_2(B_90,A_89,A_89)
      | ~ v1_funct_2(B_90,A_89,A_89)
      | ~ v1_funct_1(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_301,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_297])).

tff(c_305,plain,(
    v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_275,c_301])).

tff(c_22,plain,(
    ! [C_18,B_17,A_16] :
      ( v2_funct_2(C_18,B_17)
      | ~ v3_funct_2(C_18,A_16,B_17)
      | ~ v1_funct_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_371,plain,
    ( v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_354,c_22])).

tff(c_400,plain,(
    v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_305,c_371])).

tff(c_14,plain,(
    ! [C_10,B_9,A_8] :
      ( v5_relat_1(C_10,B_9)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_405,plain,(
    v5_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_354,c_14])).

tff(c_30,plain,(
    ! [B_20,A_19] :
      ( k2_relat_1(B_20) = A_19
      | ~ v2_funct_2(B_20,A_19)
      | ~ v5_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_428,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_405,c_30])).

tff(c_431,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_400,c_428])).

tff(c_6,plain,(
    ! [A_6] :
      ( k2_relat_1(k2_funct_1(A_6)) = k1_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_459,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_6])).

tff(c_471,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_54,c_224,c_459])).

tff(c_12,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k2_funct_1(A_7)) = k6_relat_1(k1_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_56,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k2_funct_1(A_7)) = k6_partfun1(k1_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_12])).

tff(c_409,plain,(
    ! [A_99,F_95,C_94,E_96,B_97,D_98] :
      ( k1_partfun1(A_99,B_97,C_94,D_98,E_96,F_95) = k5_relat_1(E_96,F_95)
      | ~ m1_subset_1(F_95,k1_zfmisc_1(k2_zfmisc_1(C_94,D_98)))
      | ~ v1_funct_1(F_95)
      | ~ m1_subset_1(E_96,k1_zfmisc_1(k2_zfmisc_1(A_99,B_97)))
      | ~ v1_funct_1(E_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1355,plain,(
    ! [B_133,E_132,A_131,B_130,A_129] :
      ( k1_partfun1(A_129,B_130,A_131,A_131,E_132,k2_funct_2(A_131,B_133)) = k5_relat_1(E_132,k2_funct_2(A_131,B_133))
      | ~ v1_funct_1(k2_funct_2(A_131,B_133))
      | ~ m1_subset_1(E_132,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130)))
      | ~ v1_funct_1(E_132)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(k2_zfmisc_1(A_131,A_131)))
      | ~ v3_funct_2(B_133,A_131,A_131)
      | ~ v1_funct_2(B_133,A_131,A_131)
      | ~ v1_funct_1(B_133) ) ),
    inference(resolution,[status(thm)],[c_32,c_409])).

tff(c_1371,plain,(
    ! [A_131,B_133] :
      ( k1_partfun1('#skF_1','#skF_1',A_131,A_131,'#skF_2',k2_funct_2(A_131,B_133)) = k5_relat_1('#skF_2',k2_funct_2(A_131,B_133))
      | ~ v1_funct_1(k2_funct_2(A_131,B_133))
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(B_133,k1_zfmisc_1(k2_zfmisc_1(A_131,A_131)))
      | ~ v3_funct_2(B_133,A_131,A_131)
      | ~ v1_funct_2(B_133,A_131,A_131)
      | ~ v1_funct_1(B_133) ) ),
    inference(resolution,[status(thm)],[c_48,c_1355])).

tff(c_1392,plain,(
    ! [A_134,B_135] :
      ( k1_partfun1('#skF_1','#skF_1',A_134,A_134,'#skF_2',k2_funct_2(A_134,B_135)) = k5_relat_1('#skF_2',k2_funct_2(A_134,B_135))
      | ~ v1_funct_1(k2_funct_2(A_134,B_135))
      | ~ m1_subset_1(B_135,k1_zfmisc_1(k2_zfmisc_1(A_134,A_134)))
      | ~ v3_funct_2(B_135,A_134,A_134)
      | ~ v1_funct_2(B_135,A_134,A_134)
      | ~ v1_funct_1(B_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1371])).

tff(c_1408,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')) = k5_relat_1('#skF_2',k2_funct_2('#skF_1','#skF_2'))
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1392])).

tff(c_1428,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_276,c_275,c_275,c_275,c_1408])).

tff(c_46,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_82,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_277,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_82])).

tff(c_1429,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1428,c_277])).

tff(c_1436,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1429])).

tff(c_1439,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_54,c_224,c_250,c_471,c_1436])).

tff(c_1440,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1667,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1665,c_1440])).

tff(c_2214,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2052,c_1667])).

tff(c_2227,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_2214])).

tff(c_2230,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_54,c_1605,c_1639,c_1543,c_2227])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.94/1.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.94/1.87  
% 4.94/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.94/1.87  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 4.94/1.87  
% 4.94/1.87  %Foreground sorts:
% 4.94/1.87  
% 4.94/1.87  
% 4.94/1.87  %Background operators:
% 4.94/1.87  
% 4.94/1.87  
% 4.94/1.87  %Foreground operators:
% 4.94/1.87  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.94/1.87  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.94/1.87  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.94/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.94/1.87  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.94/1.87  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.94/1.87  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 4.94/1.87  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.94/1.87  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.94/1.87  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.94/1.87  tff('#skF_2', type, '#skF_2': $i).
% 4.94/1.87  tff('#skF_1', type, '#skF_1': $i).
% 4.94/1.87  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.94/1.87  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.94/1.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.94/1.87  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.94/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.94/1.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.94/1.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.94/1.87  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.94/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.94/1.87  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.94/1.87  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 4.94/1.87  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.94/1.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.94/1.87  
% 4.94/1.90  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.94/1.90  tff(f_139, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 4.94/1.90  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.94/1.90  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 4.94/1.90  tff(f_126, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.94/1.90  tff(f_68, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 4.94/1.90  tff(f_66, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 4.94/1.90  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.94/1.90  tff(f_88, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 4.94/1.90  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 4.94/1.90  tff(f_124, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 4.94/1.90  tff(f_104, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 4.94/1.90  tff(f_114, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.94/1.90  tff(f_44, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 4.94/1.90  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.94/1.90  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.94/1.90  tff(c_69, plain, (![B_36, A_37]: (v1_relat_1(B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(A_37)) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.94/1.90  tff(c_75, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_48, c_69])).
% 4.94/1.90  tff(c_81, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_75])).
% 4.94/1.90  tff(c_54, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.94/1.90  tff(c_50, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.94/1.90  tff(c_1595, plain, (![C_165, A_166, B_167]: (v2_funct_1(C_165) | ~v3_funct_2(C_165, A_166, B_167) | ~v1_funct_1(C_165) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.94/1.90  tff(c_1601, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1595])).
% 4.94/1.90  tff(c_1605, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_1601])).
% 4.94/1.90  tff(c_44, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.94/1.90  tff(c_20, plain, (![A_15]: (m1_subset_1(k6_relat_1(A_15), k1_zfmisc_1(k2_zfmisc_1(A_15, A_15))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.94/1.90  tff(c_55, plain, (![A_15]: (m1_subset_1(k6_partfun1(A_15), k1_zfmisc_1(k2_zfmisc_1(A_15, A_15))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_20])).
% 4.94/1.90  tff(c_1619, plain, (![A_173, B_174, C_175, D_176]: (r2_relset_1(A_173, B_174, C_175, C_175) | ~m1_subset_1(D_176, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.94/1.90  tff(c_1634, plain, (![A_178, C_179]: (r2_relset_1(A_178, A_178, C_179, C_179) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_178, A_178))))), inference(resolution, [status(thm)], [c_55, c_1619])).
% 4.94/1.90  tff(c_1639, plain, (![A_15]: (r2_relset_1(A_15, A_15, k6_partfun1(A_15), k6_partfun1(A_15)))), inference(resolution, [status(thm)], [c_55, c_1634])).
% 4.94/1.90  tff(c_1443, plain, (![C_137, B_138, A_139]: (v5_relat_1(C_137, B_138) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_139, B_138))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.94/1.90  tff(c_1451, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_1443])).
% 4.94/1.90  tff(c_1464, plain, (![B_146, A_147]: (k2_relat_1(B_146)=A_147 | ~v2_funct_2(B_146, A_147) | ~v5_relat_1(B_146, A_147) | ~v1_relat_1(B_146))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.94/1.90  tff(c_1470, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1451, c_1464])).
% 4.94/1.90  tff(c_1476, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_1470])).
% 4.94/1.90  tff(c_1477, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_1476])).
% 4.94/1.90  tff(c_1530, plain, (![C_157, B_158, A_159]: (v2_funct_2(C_157, B_158) | ~v3_funct_2(C_157, A_159, B_158) | ~v1_funct_1(C_157) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_159, B_158))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.94/1.90  tff(c_1536, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1530])).
% 4.94/1.90  tff(c_1540, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_1536])).
% 4.94/1.90  tff(c_1542, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1477, c_1540])).
% 4.94/1.90  tff(c_1543, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_1476])).
% 4.94/1.90  tff(c_10, plain, (![A_7]: (k5_relat_1(k2_funct_1(A_7), A_7)=k6_relat_1(k2_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.94/1.90  tff(c_57, plain, (![A_7]: (k5_relat_1(k2_funct_1(A_7), A_7)=k6_partfun1(k2_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_10])).
% 4.94/1.90  tff(c_52, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.94/1.90  tff(c_1655, plain, (![A_183, B_184]: (k2_funct_2(A_183, B_184)=k2_funct_1(B_184) | ~m1_subset_1(B_184, k1_zfmisc_1(k2_zfmisc_1(A_183, A_183))) | ~v3_funct_2(B_184, A_183, A_183) | ~v1_funct_2(B_184, A_183, A_183) | ~v1_funct_1(B_184))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.94/1.90  tff(c_1661, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1655])).
% 4.94/1.90  tff(c_1665, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_1661])).
% 4.94/1.90  tff(c_1644, plain, (![A_181, B_182]: (v1_funct_1(k2_funct_2(A_181, B_182)) | ~m1_subset_1(B_182, k1_zfmisc_1(k2_zfmisc_1(A_181, A_181))) | ~v3_funct_2(B_182, A_181, A_181) | ~v1_funct_2(B_182, A_181, A_181) | ~v1_funct_1(B_182))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.94/1.90  tff(c_1650, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1644])).
% 4.94/1.90  tff(c_1654, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_1650])).
% 4.94/1.90  tff(c_1666, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1665, c_1654])).
% 4.94/1.90  tff(c_32, plain, (![A_21, B_22]: (m1_subset_1(k2_funct_2(A_21, B_22), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))) | ~m1_subset_1(B_22, k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))) | ~v3_funct_2(B_22, A_21, A_21) | ~v1_funct_2(B_22, A_21, A_21) | ~v1_funct_1(B_22))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.94/1.90  tff(c_1806, plain, (![E_197, F_196, A_200, C_195, D_199, B_198]: (k1_partfun1(A_200, B_198, C_195, D_199, E_197, F_196)=k5_relat_1(E_197, F_196) | ~m1_subset_1(F_196, k1_zfmisc_1(k2_zfmisc_1(C_195, D_199))) | ~v1_funct_1(F_196) | ~m1_subset_1(E_197, k1_zfmisc_1(k2_zfmisc_1(A_200, B_198))) | ~v1_funct_1(E_197))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.94/1.90  tff(c_1814, plain, (![A_200, B_198, E_197]: (k1_partfun1(A_200, B_198, '#skF_1', '#skF_1', E_197, '#skF_2')=k5_relat_1(E_197, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_197, k1_zfmisc_1(k2_zfmisc_1(A_200, B_198))) | ~v1_funct_1(E_197))), inference(resolution, [status(thm)], [c_48, c_1806])).
% 4.94/1.90  tff(c_1823, plain, (![A_201, B_202, E_203]: (k1_partfun1(A_201, B_202, '#skF_1', '#skF_1', E_203, '#skF_2')=k5_relat_1(E_203, '#skF_2') | ~m1_subset_1(E_203, k1_zfmisc_1(k2_zfmisc_1(A_201, B_202))) | ~v1_funct_1(E_203))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1814])).
% 4.94/1.90  tff(c_2031, plain, (![A_210, B_211]: (k1_partfun1(A_210, A_210, '#skF_1', '#skF_1', k2_funct_2(A_210, B_211), '#skF_2')=k5_relat_1(k2_funct_2(A_210, B_211), '#skF_2') | ~v1_funct_1(k2_funct_2(A_210, B_211)) | ~m1_subset_1(B_211, k1_zfmisc_1(k2_zfmisc_1(A_210, A_210))) | ~v3_funct_2(B_211, A_210, A_210) | ~v1_funct_2(B_211, A_210, A_210) | ~v1_funct_1(B_211))), inference(resolution, [status(thm)], [c_32, c_1823])).
% 4.94/1.90  tff(c_2041, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_2031])).
% 4.94/1.90  tff(c_2052, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_1666, c_1665, c_1665, c_1665, c_2041])).
% 4.94/1.90  tff(c_214, plain, (![C_64, A_65, B_66]: (v2_funct_1(C_64) | ~v3_funct_2(C_64, A_65, B_66) | ~v1_funct_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.94/1.90  tff(c_220, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_214])).
% 4.94/1.90  tff(c_224, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_220])).
% 4.94/1.90  tff(c_238, plain, (![A_72, B_73, C_74, D_75]: (r2_relset_1(A_72, B_73, C_74, C_74) | ~m1_subset_1(D_75, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.94/1.90  tff(c_245, plain, (![A_76, C_77]: (r2_relset_1(A_76, A_76, C_77, C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_76, A_76))))), inference(resolution, [status(thm)], [c_55, c_238])).
% 4.94/1.90  tff(c_250, plain, (![A_15]: (r2_relset_1(A_15, A_15, k6_partfun1(A_15), k6_partfun1(A_15)))), inference(resolution, [status(thm)], [c_55, c_245])).
% 4.94/1.90  tff(c_265, plain, (![A_82, B_83]: (k2_funct_2(A_82, B_83)=k2_funct_1(B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(k2_zfmisc_1(A_82, A_82))) | ~v3_funct_2(B_83, A_82, A_82) | ~v1_funct_2(B_83, A_82, A_82) | ~v1_funct_1(B_83))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.94/1.90  tff(c_271, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_265])).
% 4.94/1.90  tff(c_275, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_271])).
% 4.94/1.90  tff(c_307, plain, (![A_92, B_93]: (m1_subset_1(k2_funct_2(A_92, B_93), k1_zfmisc_1(k2_zfmisc_1(A_92, A_92))) | ~m1_subset_1(B_93, k1_zfmisc_1(k2_zfmisc_1(A_92, A_92))) | ~v3_funct_2(B_93, A_92, A_92) | ~v1_funct_2(B_93, A_92, A_92) | ~v1_funct_1(B_93))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.94/1.90  tff(c_339, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_275, c_307])).
% 4.94/1.90  tff(c_354, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_339])).
% 4.94/1.90  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.94/1.90  tff(c_383, plain, (v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_354, c_2])).
% 4.94/1.90  tff(c_408, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_383])).
% 4.94/1.90  tff(c_253, plain, (![A_79, B_80]: (v1_funct_1(k2_funct_2(A_79, B_80)) | ~m1_subset_1(B_80, k1_zfmisc_1(k2_zfmisc_1(A_79, A_79))) | ~v3_funct_2(B_80, A_79, A_79) | ~v1_funct_2(B_80, A_79, A_79) | ~v1_funct_1(B_80))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.94/1.90  tff(c_259, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_253])).
% 4.94/1.90  tff(c_263, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_259])).
% 4.94/1.90  tff(c_276, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_275, c_263])).
% 4.94/1.90  tff(c_297, plain, (![A_89, B_90]: (v3_funct_2(k2_funct_2(A_89, B_90), A_89, A_89) | ~m1_subset_1(B_90, k1_zfmisc_1(k2_zfmisc_1(A_89, A_89))) | ~v3_funct_2(B_90, A_89, A_89) | ~v1_funct_2(B_90, A_89, A_89) | ~v1_funct_1(B_90))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.94/1.90  tff(c_301, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_297])).
% 4.94/1.90  tff(c_305, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_275, c_301])).
% 4.94/1.90  tff(c_22, plain, (![C_18, B_17, A_16]: (v2_funct_2(C_18, B_17) | ~v3_funct_2(C_18, A_16, B_17) | ~v1_funct_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.94/1.90  tff(c_371, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_354, c_22])).
% 4.94/1.90  tff(c_400, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_276, c_305, c_371])).
% 4.94/1.90  tff(c_14, plain, (![C_10, B_9, A_8]: (v5_relat_1(C_10, B_9) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.94/1.90  tff(c_405, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_354, c_14])).
% 4.94/1.90  tff(c_30, plain, (![B_20, A_19]: (k2_relat_1(B_20)=A_19 | ~v2_funct_2(B_20, A_19) | ~v5_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.94/1.90  tff(c_428, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_405, c_30])).
% 4.94/1.90  tff(c_431, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_408, c_400, c_428])).
% 4.94/1.90  tff(c_6, plain, (![A_6]: (k2_relat_1(k2_funct_1(A_6))=k1_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.94/1.90  tff(c_459, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_431, c_6])).
% 4.94/1.90  tff(c_471, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_81, c_54, c_224, c_459])).
% 4.94/1.90  tff(c_12, plain, (![A_7]: (k5_relat_1(A_7, k2_funct_1(A_7))=k6_relat_1(k1_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.94/1.90  tff(c_56, plain, (![A_7]: (k5_relat_1(A_7, k2_funct_1(A_7))=k6_partfun1(k1_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_12])).
% 4.94/1.90  tff(c_409, plain, (![A_99, F_95, C_94, E_96, B_97, D_98]: (k1_partfun1(A_99, B_97, C_94, D_98, E_96, F_95)=k5_relat_1(E_96, F_95) | ~m1_subset_1(F_95, k1_zfmisc_1(k2_zfmisc_1(C_94, D_98))) | ~v1_funct_1(F_95) | ~m1_subset_1(E_96, k1_zfmisc_1(k2_zfmisc_1(A_99, B_97))) | ~v1_funct_1(E_96))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.94/1.90  tff(c_1355, plain, (![B_133, E_132, A_131, B_130, A_129]: (k1_partfun1(A_129, B_130, A_131, A_131, E_132, k2_funct_2(A_131, B_133))=k5_relat_1(E_132, k2_funct_2(A_131, B_133)) | ~v1_funct_1(k2_funct_2(A_131, B_133)) | ~m1_subset_1(E_132, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))) | ~v1_funct_1(E_132) | ~m1_subset_1(B_133, k1_zfmisc_1(k2_zfmisc_1(A_131, A_131))) | ~v3_funct_2(B_133, A_131, A_131) | ~v1_funct_2(B_133, A_131, A_131) | ~v1_funct_1(B_133))), inference(resolution, [status(thm)], [c_32, c_409])).
% 4.94/1.90  tff(c_1371, plain, (![A_131, B_133]: (k1_partfun1('#skF_1', '#skF_1', A_131, A_131, '#skF_2', k2_funct_2(A_131, B_133))=k5_relat_1('#skF_2', k2_funct_2(A_131, B_133)) | ~v1_funct_1(k2_funct_2(A_131, B_133)) | ~v1_funct_1('#skF_2') | ~m1_subset_1(B_133, k1_zfmisc_1(k2_zfmisc_1(A_131, A_131))) | ~v3_funct_2(B_133, A_131, A_131) | ~v1_funct_2(B_133, A_131, A_131) | ~v1_funct_1(B_133))), inference(resolution, [status(thm)], [c_48, c_1355])).
% 4.94/1.90  tff(c_1392, plain, (![A_134, B_135]: (k1_partfun1('#skF_1', '#skF_1', A_134, A_134, '#skF_2', k2_funct_2(A_134, B_135))=k5_relat_1('#skF_2', k2_funct_2(A_134, B_135)) | ~v1_funct_1(k2_funct_2(A_134, B_135)) | ~m1_subset_1(B_135, k1_zfmisc_1(k2_zfmisc_1(A_134, A_134))) | ~v3_funct_2(B_135, A_134, A_134) | ~v1_funct_2(B_135, A_134, A_134) | ~v1_funct_1(B_135))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1371])).
% 4.94/1.90  tff(c_1408, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2'))=k5_relat_1('#skF_2', k2_funct_2('#skF_1', '#skF_2')) | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1392])).
% 4.94/1.90  tff(c_1428, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_276, c_275, c_275, c_275, c_1408])).
% 4.94/1.90  tff(c_46, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.94/1.90  tff(c_82, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_46])).
% 4.94/1.90  tff(c_277, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_275, c_82])).
% 4.94/1.90  tff(c_1429, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1428, c_277])).
% 4.94/1.90  tff(c_1436, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_56, c_1429])).
% 4.94/1.90  tff(c_1439, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_54, c_224, c_250, c_471, c_1436])).
% 4.94/1.90  tff(c_1440, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_46])).
% 4.94/1.90  tff(c_1667, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1665, c_1440])).
% 4.94/1.90  tff(c_2214, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2052, c_1667])).
% 4.94/1.90  tff(c_2227, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_57, c_2214])).
% 4.94/1.90  tff(c_2230, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_54, c_1605, c_1639, c_1543, c_2227])).
% 4.94/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.94/1.90  
% 4.94/1.90  Inference rules
% 4.94/1.90  ----------------------
% 4.94/1.90  #Ref     : 0
% 4.94/1.90  #Sup     : 457
% 4.94/1.90  #Fact    : 0
% 4.94/1.90  #Define  : 0
% 4.94/1.90  #Split   : 3
% 4.94/1.90  #Chain   : 0
% 4.94/1.90  #Close   : 0
% 4.94/1.90  
% 4.94/1.90  Ordering : KBO
% 4.94/1.90  
% 4.94/1.90  Simplification rules
% 4.94/1.90  ----------------------
% 4.94/1.90  #Subsume      : 12
% 4.94/1.90  #Demod        : 1001
% 4.94/1.90  #Tautology    : 166
% 4.94/1.90  #SimpNegUnit  : 2
% 4.94/1.90  #BackRed      : 38
% 4.94/1.90  
% 4.94/1.90  #Partial instantiations: 0
% 4.94/1.90  #Strategies tried      : 1
% 4.94/1.90  
% 4.94/1.90  Timing (in seconds)
% 4.94/1.90  ----------------------
% 4.94/1.90  Preprocessing        : 0.34
% 4.94/1.90  Parsing              : 0.19
% 4.94/1.90  CNF conversion       : 0.02
% 4.94/1.90  Main loop            : 0.78
% 4.94/1.90  Inferencing          : 0.27
% 4.94/1.90  Reduction            : 0.29
% 4.94/1.90  Demodulation         : 0.21
% 4.94/1.90  BG Simplification    : 0.03
% 4.94/1.90  Subsumption          : 0.14
% 4.94/1.90  Abstraction          : 0.03
% 4.94/1.90  MUC search           : 0.00
% 4.94/1.90  Cooper               : 0.00
% 4.94/1.90  Total                : 1.17
% 4.94/1.90  Index Insertion      : 0.00
% 4.94/1.90  Index Deletion       : 0.00
% 4.94/1.90  Index Matching       : 0.00
% 4.94/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
