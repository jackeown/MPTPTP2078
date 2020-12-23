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
% DateTime   : Thu Dec  3 10:13:32 EST 2020

% Result     : Theorem 5.73s
% Output     : CNFRefutation 5.87s
% Verified   : 
% Statistics : Number of formulae       :  181 (1060 expanded)
%              Number of leaves         :   36 ( 344 expanded)
%              Depth                    :   14
%              Number of atoms          :  311 (3407 expanded)
%              Number of equality atoms :   98 (1260 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(A,B,D,C))
              & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
              & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_98,axiom,(
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

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_112,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_52,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_12,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_104,plain,(
    ! [B_46,A_47] :
      ( v1_relat_1(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_107,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_104])).

tff(c_110,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_107])).

tff(c_50,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_63,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_56,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_3861,plain,(
    ! [A_353,B_354,C_355] :
      ( k1_relset_1(A_353,B_354,C_355) = k1_relat_1(C_355)
      | ~ m1_subset_1(C_355,k1_zfmisc_1(k2_zfmisc_1(A_353,B_354))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_3875,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_3861])).

tff(c_4072,plain,(
    ! [B_391,A_392,C_393] :
      ( k1_xboole_0 = B_391
      | k1_relset_1(A_392,B_391,C_393) = A_392
      | ~ v1_funct_2(C_393,A_392,B_391)
      | ~ m1_subset_1(C_393,k1_zfmisc_1(k2_zfmisc_1(A_392,B_391))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4081,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_4072])).

tff(c_4095,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3875,c_4081])).

tff(c_4096,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_4095])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( k1_relat_1(k7_relat_1(B_14,A_13)) = A_13
      | ~ r1_tarski(A_13,k1_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4108,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_13)) = A_13
      | ~ r1_tarski(A_13,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4096,c_18])).

tff(c_4112,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_13)) = A_13
      | ~ r1_tarski(A_13,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_4108])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_3984,plain,(
    ! [A_384,B_385,C_386,D_387] :
      ( k2_partfun1(A_384,B_385,C_386,D_387) = k7_relat_1(C_386,D_387)
      | ~ m1_subset_1(C_386,k1_zfmisc_1(k2_zfmisc_1(A_384,B_385)))
      | ~ v1_funct_1(C_386) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_3990,plain,(
    ! [D_387] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_387) = k7_relat_1('#skF_4',D_387)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_3984])).

tff(c_4003,plain,(
    ! [D_387] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_387) = k7_relat_1('#skF_4',D_387) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_3990])).

tff(c_317,plain,(
    ! [A_106,B_107,C_108] :
      ( k1_relset_1(A_106,B_107,C_108) = k1_relat_1(C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_327,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_317])).

tff(c_825,plain,(
    ! [B_182,A_183,C_184] :
      ( k1_xboole_0 = B_182
      | k1_relset_1(A_183,B_182,C_184) = A_183
      | ~ v1_funct_2(C_184,A_183,B_182)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_183,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_834,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_825])).

tff(c_847,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_327,c_834])).

tff(c_848,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_847])).

tff(c_866,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_13)) = A_13
      | ~ r1_tarski(A_13,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_848,c_18])).

tff(c_873,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_13)) = A_13
      | ~ r1_tarski(A_13,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_866])).

tff(c_409,plain,(
    ! [A_135,B_136,C_137,D_138] :
      ( k2_partfun1(A_135,B_136,C_137,D_138) = k7_relat_1(C_137,D_138)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136)))
      | ~ v1_funct_1(C_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_413,plain,(
    ! [D_138] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_138) = k7_relat_1('#skF_4',D_138)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_409])).

tff(c_423,plain,(
    ! [D_138] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_138) = k7_relat_1('#skF_4',D_138) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_413])).

tff(c_886,plain,(
    ! [A_186,B_187,C_188,D_189] :
      ( m1_subset_1(k2_partfun1(A_186,B_187,C_188,D_189),k1_zfmisc_1(k2_zfmisc_1(A_186,B_187)))
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(A_186,B_187)))
      | ~ v1_funct_1(C_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_916,plain,(
    ! [D_138] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_138),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_886])).

tff(c_945,plain,(
    ! [D_191] : m1_subset_1(k7_relat_1('#skF_4',D_191),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_916])).

tff(c_20,plain,(
    ! [C_17,A_15,B_16] :
      ( v1_relat_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_991,plain,(
    ! [D_191] : v1_relat_1(k7_relat_1('#skF_4',D_191)) ),
    inference(resolution,[status(thm)],[c_945,c_20])).

tff(c_24,plain,(
    ! [C_20,A_18,B_19] :
      ( v4_relat_1(C_20,A_18)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1058,plain,(
    ! [D_194] : v4_relat_1(k7_relat_1('#skF_4',D_194),'#skF_1') ),
    inference(resolution,[status(thm)],[c_945,c_24])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( k7_relat_1(B_10,A_9) = B_10
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1061,plain,(
    ! [D_194] :
      ( k7_relat_1(k7_relat_1('#skF_4',D_194),'#skF_1') = k7_relat_1('#skF_4',D_194)
      | ~ v1_relat_1(k7_relat_1('#skF_4',D_194)) ) ),
    inference(resolution,[status(thm)],[c_1058,c_14])).

tff(c_1173,plain,(
    ! [D_208] : k7_relat_1(k7_relat_1('#skF_4',D_208),'#skF_1') = k7_relat_1('#skF_4',D_208) ),
    inference(demodulation,[status(thm),theory(equality)],[c_991,c_1061])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_12,A_11)),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1183,plain,(
    ! [D_208] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_4',D_208)),'#skF_1')
      | ~ v1_relat_1(k7_relat_1('#skF_4',D_208)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1173,c_16])).

tff(c_1197,plain,(
    ! [D_209] : r1_tarski(k1_relat_1(k7_relat_1('#skF_4',D_209)),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_991,c_1183])).

tff(c_1078,plain,(
    ! [A_197] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_197)) = A_197
      | ~ r1_tarski(A_197,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_866])).

tff(c_1095,plain,(
    ! [A_197] :
      ( r1_tarski(A_197,A_197)
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski(A_197,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1078,c_16])).

tff(c_1115,plain,(
    ! [A_197] :
      ( r1_tarski(A_197,A_197)
      | ~ r1_tarski(A_197,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_1095])).

tff(c_1285,plain,(
    ! [D_218] : r1_tarski(k1_relat_1(k7_relat_1('#skF_4',D_218)),k1_relat_1(k7_relat_1('#skF_4',D_218))) ),
    inference(resolution,[status(thm)],[c_1197,c_1115])).

tff(c_1298,plain,(
    ! [A_13] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_13)),A_13)
      | ~ r1_tarski(A_13,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_873,c_1285])).

tff(c_28,plain,(
    ! [D_27,B_25,C_26,A_24] :
      ( m1_subset_1(D_27,k1_zfmisc_1(k2_zfmisc_1(B_25,C_26)))
      | ~ r1_tarski(k1_relat_1(D_27),B_25)
      | ~ m1_subset_1(D_27,k1_zfmisc_1(k2_zfmisc_1(A_24,C_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3592,plain,(
    ! [B_341,C_343,A_344,B_340,D_342] :
      ( m1_subset_1(k2_partfun1(A_344,B_340,C_343,D_342),k1_zfmisc_1(k2_zfmisc_1(B_341,B_340)))
      | ~ r1_tarski(k1_relat_1(k2_partfun1(A_344,B_340,C_343,D_342)),B_341)
      | ~ m1_subset_1(C_343,k1_zfmisc_1(k2_zfmisc_1(A_344,B_340)))
      | ~ v1_funct_1(C_343) ) ),
    inference(resolution,[status(thm)],[c_886,c_28])).

tff(c_3635,plain,(
    ! [D_138,B_341] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_138),k1_zfmisc_1(k2_zfmisc_1(B_341,'#skF_2')))
      | ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_138)),B_341)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_3592])).

tff(c_3708,plain,(
    ! [D_346,B_347] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_346),k1_zfmisc_1(k2_zfmisc_1(B_347,'#skF_2')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4',D_346)),B_347) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_423,c_3635])).

tff(c_230,plain,(
    ! [A_84,B_85,C_86,D_87] :
      ( v1_funct_1(k2_partfun1(A_84,B_85,C_86,D_87))
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85)))
      | ~ v1_funct_1(C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_232,plain,(
    ! [D_87] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_87))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_230])).

tff(c_239,plain,(
    ! [D_87] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_87)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_232])).

tff(c_48,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_140,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_140])).

tff(c_243,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_294,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_243])).

tff(c_425,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_294])).

tff(c_3777,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_3708,c_425])).

tff(c_3800,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_1298,c_3777])).

tff(c_3812,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3800])).

tff(c_3814,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_243])).

tff(c_3874,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_3814,c_3861])).

tff(c_4008,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4003,c_4003,c_3874])).

tff(c_3813,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_243])).

tff(c_4013,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4003,c_3813])).

tff(c_4012,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4003,c_3814])).

tff(c_4147,plain,(
    ! [B_397,C_398,A_399] :
      ( k1_xboole_0 = B_397
      | v1_funct_2(C_398,A_399,B_397)
      | k1_relset_1(A_399,B_397,C_398) != A_399
      | ~ m1_subset_1(C_398,k1_zfmisc_1(k2_zfmisc_1(A_399,B_397))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4150,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_4012,c_4147])).

tff(c_4162,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_4013,c_63,c_4150])).

tff(c_4285,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4008,c_4162])).

tff(c_4345,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4112,c_4285])).

tff(c_4349,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4345])).

tff(c_4350,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4363,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4350,c_4350,c_6])).

tff(c_4351,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_4356,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4350,c_4351])).

tff(c_4362,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4356,c_54])).

tff(c_4364,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4363,c_4362])).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4372,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_1',B_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4350,c_4350,c_8])).

tff(c_4658,plain,(
    ! [C_466,A_467,B_468] :
      ( v1_relat_1(C_466)
      | ~ m1_subset_1(C_466,k1_zfmisc_1(k2_zfmisc_1(A_467,B_468))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4663,plain,(
    ! [C_469] :
      ( v1_relat_1(C_469)
      | ~ m1_subset_1(C_469,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4372,c_4658])).

tff(c_4667,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4364,c_4663])).

tff(c_4694,plain,(
    ! [C_475,A_476,B_477] :
      ( v4_relat_1(C_475,A_476)
      | ~ m1_subset_1(C_475,k1_zfmisc_1(k2_zfmisc_1(A_476,B_477))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4898,plain,(
    ! [C_531] :
      ( v4_relat_1(C_531,'#skF_1')
      | ~ m1_subset_1(C_531,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4372,c_4694])).

tff(c_4902,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_4364,c_4898])).

tff(c_4903,plain,(
    ! [B_532,A_533] :
      ( k7_relat_1(B_532,A_533) = B_532
      | ~ v4_relat_1(B_532,A_533)
      | ~ v1_relat_1(B_532) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4906,plain,
    ( k7_relat_1('#skF_4','#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4902,c_4903])).

tff(c_4909,plain,(
    k7_relat_1('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4667,c_4906])).

tff(c_4668,plain,(
    ! [B_470,A_471] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_470,A_471)),A_471)
      | ~ v1_relat_1(B_470) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4394,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ r1_tarski(A_1,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4350,c_4350,c_2])).

tff(c_4673,plain,(
    ! [B_470] :
      ( k1_relat_1(k7_relat_1(B_470,'#skF_1')) = '#skF_1'
      | ~ v1_relat_1(B_470) ) ),
    inference(resolution,[status(thm)],[c_4668,c_4394])).

tff(c_4913,plain,
    ( k1_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4909,c_4673])).

tff(c_4920,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4667,c_4913])).

tff(c_5034,plain,(
    ! [A_551,B_552,C_553] :
      ( k1_relset_1(A_551,B_552,C_553) = k1_relat_1(C_553)
      | ~ m1_subset_1(C_553,k1_zfmisc_1(k2_zfmisc_1(A_551,B_552))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_5041,plain,(
    ! [B_554,C_555] :
      ( k1_relset_1('#skF_1',B_554,C_555) = k1_relat_1(C_555)
      | ~ m1_subset_1(C_555,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4372,c_5034])).

tff(c_5045,plain,(
    ! [B_554] : k1_relset_1('#skF_1',B_554,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4364,c_5041])).

tff(c_5048,plain,(
    ! [B_554] : k1_relset_1('#skF_1',B_554,'#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4920,c_5045])).

tff(c_34,plain,(
    ! [C_30,B_29] :
      ( v1_funct_2(C_30,k1_xboole_0,B_29)
      | k1_relset_1(k1_xboole_0,B_29,C_30) != k1_xboole_0
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_60,plain,(
    ! [C_30,B_29] :
      ( v1_funct_2(C_30,k1_xboole_0,B_29)
      | k1_relset_1(k1_xboole_0,B_29,C_30) != k1_xboole_0
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_34])).

tff(c_5115,plain,(
    ! [C_563,B_564] :
      ( v1_funct_2(C_563,'#skF_1',B_564)
      | k1_relset_1('#skF_1',B_564,C_563) != '#skF_1'
      | ~ m1_subset_1(C_563,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4350,c_4350,c_4350,c_4350,c_60])).

tff(c_5119,plain,(
    ! [B_564] :
      ( v1_funct_2('#skF_4','#skF_1',B_564)
      | k1_relset_1('#skF_1',B_564,'#skF_4') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_4364,c_5115])).

tff(c_5123,plain,(
    ! [B_564] : v1_funct_2('#skF_4','#skF_1',B_564) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5048,c_5119])).

tff(c_4929,plain,(
    ! [C_534,A_535] :
      ( v4_relat_1(C_534,A_535)
      | ~ m1_subset_1(C_534,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4363,c_4694])).

tff(c_4934,plain,(
    ! [A_536] : v4_relat_1('#skF_4',A_536) ),
    inference(resolution,[status(thm)],[c_4364,c_4929])).

tff(c_4937,plain,(
    ! [A_536] :
      ( k7_relat_1('#skF_4',A_536) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4934,c_14])).

tff(c_4940,plain,(
    ! [A_536] : k7_relat_1('#skF_4',A_536) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4667,c_4937])).

tff(c_5177,plain,(
    ! [A_583,B_584,C_585,D_586] :
      ( k2_partfun1(A_583,B_584,C_585,D_586) = k7_relat_1(C_585,D_586)
      | ~ m1_subset_1(C_585,k1_zfmisc_1(k2_zfmisc_1(A_583,B_584)))
      | ~ v1_funct_1(C_585) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_5183,plain,(
    ! [B_589,C_590,D_591] :
      ( k2_partfun1('#skF_1',B_589,C_590,D_591) = k7_relat_1(C_590,D_591)
      | ~ m1_subset_1(C_590,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_590) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4372,c_5177])).

tff(c_5187,plain,(
    ! [B_589,D_591] :
      ( k2_partfun1('#skF_1',B_589,'#skF_4',D_591) = k7_relat_1('#skF_4',D_591)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4364,c_5183])).

tff(c_5193,plain,(
    ! [B_589,D_591] : k2_partfun1('#skF_1',B_589,'#skF_4',D_591) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_4940,c_5187])).

tff(c_4707,plain,(
    ! [C_479,A_480] :
      ( v4_relat_1(C_479,A_480)
      | ~ m1_subset_1(C_479,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4363,c_4694])).

tff(c_4710,plain,(
    ! [A_480] : v4_relat_1('#skF_4',A_480) ),
    inference(resolution,[status(thm)],[c_4364,c_4707])).

tff(c_4713,plain,(
    ! [B_482,A_483] :
      ( k7_relat_1(B_482,A_483) = B_482
      | ~ v4_relat_1(B_482,A_483)
      | ~ v1_relat_1(B_482) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4716,plain,(
    ! [A_480] :
      ( k7_relat_1('#skF_4',A_480) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4710,c_4713])).

tff(c_4719,plain,(
    ! [A_480] : k7_relat_1('#skF_4',A_480) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4667,c_4716])).

tff(c_4879,plain,(
    ! [A_524,B_525,C_526,D_527] :
      ( k2_partfun1(A_524,B_525,C_526,D_527) = k7_relat_1(C_526,D_527)
      | ~ m1_subset_1(C_526,k1_zfmisc_1(k2_zfmisc_1(A_524,B_525)))
      | ~ v1_funct_1(C_526) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_4884,plain,(
    ! [B_528,C_529,D_530] :
      ( k2_partfun1('#skF_1',B_528,C_529,D_530) = k7_relat_1(C_529,D_530)
      | ~ m1_subset_1(C_529,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_529) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4372,c_4879])).

tff(c_4886,plain,(
    ! [B_528,D_530] :
      ( k2_partfun1('#skF_1',B_528,'#skF_4',D_530) = k7_relat_1('#skF_4',D_530)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4364,c_4884])).

tff(c_4889,plain,(
    ! [B_528,D_530] : k2_partfun1('#skF_1',B_528,'#skF_4',D_530) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_4719,c_4886])).

tff(c_4578,plain,(
    ! [A_447,B_448,C_449,D_450] :
      ( v1_funct_1(k2_partfun1(A_447,B_448,C_449,D_450))
      | ~ m1_subset_1(C_449,k1_zfmisc_1(k2_zfmisc_1(A_447,B_448)))
      | ~ v1_funct_1(C_449) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_4630,plain,(
    ! [A_461,C_462,D_463] :
      ( v1_funct_1(k2_partfun1(A_461,'#skF_1',C_462,D_463))
      | ~ m1_subset_1(C_462,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_462) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4363,c_4578])).

tff(c_4632,plain,(
    ! [A_461,D_463] :
      ( v1_funct_1(k2_partfun1(A_461,'#skF_1','#skF_4',D_463))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4364,c_4630])).

tff(c_4635,plain,(
    ! [A_461,D_463] : v1_funct_1(k2_partfun1(A_461,'#skF_1','#skF_4',D_463)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_4632])).

tff(c_4395,plain,(
    ! [A_413] :
      ( A_413 = '#skF_1'
      | ~ r1_tarski(A_413,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4350,c_4350,c_2])).

tff(c_4399,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_52,c_4395])).

tff(c_4405,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4399,c_4356,c_4399,c_4399,c_4356,c_4356,c_4399,c_4363,c_4356,c_4356,c_48])).

tff(c_4406,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_4405])).

tff(c_4638,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4635,c_4406])).

tff(c_4639,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_4405])).

tff(c_4701,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_4639])).

tff(c_4891,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4889,c_4701])).

tff(c_4895,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4364,c_4891])).

tff(c_4896,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_4639])).

tff(c_5204,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5193,c_4896])).

tff(c_5217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5123,c_5204])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:48:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.73/2.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.87/2.08  
% 5.87/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.87/2.09  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.87/2.09  
% 5.87/2.09  %Foreground sorts:
% 5.87/2.09  
% 5.87/2.09  
% 5.87/2.09  %Background operators:
% 5.87/2.09  
% 5.87/2.09  
% 5.87/2.09  %Foreground operators:
% 5.87/2.09  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.87/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.87/2.09  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.87/2.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.87/2.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.87/2.09  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.87/2.09  tff('#skF_2', type, '#skF_2': $i).
% 5.87/2.09  tff('#skF_3', type, '#skF_3': $i).
% 5.87/2.09  tff('#skF_1', type, '#skF_1': $i).
% 5.87/2.09  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.87/2.09  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.87/2.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.87/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.87/2.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.87/2.09  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.87/2.09  tff('#skF_4', type, '#skF_4': $i).
% 5.87/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.87/2.09  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 5.87/2.09  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.87/2.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.87/2.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.87/2.09  
% 5.87/2.11  tff(f_132, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 5.87/2.11  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.87/2.11  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.87/2.11  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.87/2.11  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.87/2.11  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 5.87/2.11  tff(f_112, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 5.87/2.11  tff(f_106, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 5.87/2.11  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.87/2.11  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.87/2.11  tff(f_50, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 5.87/2.11  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 5.87/2.11  tff(f_80, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 5.87/2.11  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.87/2.11  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 5.87/2.11  tff(c_52, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.87/2.11  tff(c_12, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.87/2.11  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.87/2.11  tff(c_104, plain, (![B_46, A_47]: (v1_relat_1(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.87/2.11  tff(c_107, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_54, c_104])).
% 5.87/2.11  tff(c_110, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_107])).
% 5.87/2.11  tff(c_50, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.87/2.11  tff(c_63, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_50])).
% 5.87/2.11  tff(c_56, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.87/2.11  tff(c_3861, plain, (![A_353, B_354, C_355]: (k1_relset_1(A_353, B_354, C_355)=k1_relat_1(C_355) | ~m1_subset_1(C_355, k1_zfmisc_1(k2_zfmisc_1(A_353, B_354))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.87/2.11  tff(c_3875, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_3861])).
% 5.87/2.11  tff(c_4072, plain, (![B_391, A_392, C_393]: (k1_xboole_0=B_391 | k1_relset_1(A_392, B_391, C_393)=A_392 | ~v1_funct_2(C_393, A_392, B_391) | ~m1_subset_1(C_393, k1_zfmisc_1(k2_zfmisc_1(A_392, B_391))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.87/2.11  tff(c_4081, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_4072])).
% 5.87/2.11  tff(c_4095, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3875, c_4081])).
% 5.87/2.11  tff(c_4096, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_63, c_4095])).
% 5.87/2.11  tff(c_18, plain, (![B_14, A_13]: (k1_relat_1(k7_relat_1(B_14, A_13))=A_13 | ~r1_tarski(A_13, k1_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.87/2.11  tff(c_4108, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_4', A_13))=A_13 | ~r1_tarski(A_13, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4096, c_18])).
% 5.87/2.11  tff(c_4112, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_4', A_13))=A_13 | ~r1_tarski(A_13, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_4108])).
% 5.87/2.11  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.87/2.11  tff(c_3984, plain, (![A_384, B_385, C_386, D_387]: (k2_partfun1(A_384, B_385, C_386, D_387)=k7_relat_1(C_386, D_387) | ~m1_subset_1(C_386, k1_zfmisc_1(k2_zfmisc_1(A_384, B_385))) | ~v1_funct_1(C_386))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.87/2.11  tff(c_3990, plain, (![D_387]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_387)=k7_relat_1('#skF_4', D_387) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_3984])).
% 5.87/2.11  tff(c_4003, plain, (![D_387]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_387)=k7_relat_1('#skF_4', D_387))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_3990])).
% 5.87/2.11  tff(c_317, plain, (![A_106, B_107, C_108]: (k1_relset_1(A_106, B_107, C_108)=k1_relat_1(C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.87/2.11  tff(c_327, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_317])).
% 5.87/2.11  tff(c_825, plain, (![B_182, A_183, C_184]: (k1_xboole_0=B_182 | k1_relset_1(A_183, B_182, C_184)=A_183 | ~v1_funct_2(C_184, A_183, B_182) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_183, B_182))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.87/2.11  tff(c_834, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_825])).
% 5.87/2.11  tff(c_847, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_327, c_834])).
% 5.87/2.11  tff(c_848, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_63, c_847])).
% 5.87/2.11  tff(c_866, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_4', A_13))=A_13 | ~r1_tarski(A_13, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_848, c_18])).
% 5.87/2.11  tff(c_873, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_4', A_13))=A_13 | ~r1_tarski(A_13, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_866])).
% 5.87/2.11  tff(c_409, plain, (![A_135, B_136, C_137, D_138]: (k2_partfun1(A_135, B_136, C_137, D_138)=k7_relat_1(C_137, D_138) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))) | ~v1_funct_1(C_137))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.87/2.11  tff(c_413, plain, (![D_138]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_138)=k7_relat_1('#skF_4', D_138) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_409])).
% 5.87/2.11  tff(c_423, plain, (![D_138]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_138)=k7_relat_1('#skF_4', D_138))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_413])).
% 5.87/2.11  tff(c_886, plain, (![A_186, B_187, C_188, D_189]: (m1_subset_1(k2_partfun1(A_186, B_187, C_188, D_189), k1_zfmisc_1(k2_zfmisc_1(A_186, B_187))) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(A_186, B_187))) | ~v1_funct_1(C_188))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.87/2.11  tff(c_916, plain, (![D_138]: (m1_subset_1(k7_relat_1('#skF_4', D_138), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_423, c_886])).
% 5.87/2.11  tff(c_945, plain, (![D_191]: (m1_subset_1(k7_relat_1('#skF_4', D_191), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_916])).
% 5.87/2.11  tff(c_20, plain, (![C_17, A_15, B_16]: (v1_relat_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.87/2.11  tff(c_991, plain, (![D_191]: (v1_relat_1(k7_relat_1('#skF_4', D_191)))), inference(resolution, [status(thm)], [c_945, c_20])).
% 5.87/2.11  tff(c_24, plain, (![C_20, A_18, B_19]: (v4_relat_1(C_20, A_18) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.87/2.11  tff(c_1058, plain, (![D_194]: (v4_relat_1(k7_relat_1('#skF_4', D_194), '#skF_1'))), inference(resolution, [status(thm)], [c_945, c_24])).
% 5.87/2.11  tff(c_14, plain, (![B_10, A_9]: (k7_relat_1(B_10, A_9)=B_10 | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.87/2.11  tff(c_1061, plain, (![D_194]: (k7_relat_1(k7_relat_1('#skF_4', D_194), '#skF_1')=k7_relat_1('#skF_4', D_194) | ~v1_relat_1(k7_relat_1('#skF_4', D_194)))), inference(resolution, [status(thm)], [c_1058, c_14])).
% 5.87/2.11  tff(c_1173, plain, (![D_208]: (k7_relat_1(k7_relat_1('#skF_4', D_208), '#skF_1')=k7_relat_1('#skF_4', D_208))), inference(demodulation, [status(thm), theory('equality')], [c_991, c_1061])).
% 5.87/2.11  tff(c_16, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(k7_relat_1(B_12, A_11)), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.87/2.11  tff(c_1183, plain, (![D_208]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', D_208)), '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_4', D_208)))), inference(superposition, [status(thm), theory('equality')], [c_1173, c_16])).
% 5.87/2.11  tff(c_1197, plain, (![D_209]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', D_209)), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_991, c_1183])).
% 5.87/2.11  tff(c_1078, plain, (![A_197]: (k1_relat_1(k7_relat_1('#skF_4', A_197))=A_197 | ~r1_tarski(A_197, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_866])).
% 5.87/2.11  tff(c_1095, plain, (![A_197]: (r1_tarski(A_197, A_197) | ~v1_relat_1('#skF_4') | ~r1_tarski(A_197, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1078, c_16])).
% 5.87/2.11  tff(c_1115, plain, (![A_197]: (r1_tarski(A_197, A_197) | ~r1_tarski(A_197, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_1095])).
% 5.87/2.11  tff(c_1285, plain, (![D_218]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', D_218)), k1_relat_1(k7_relat_1('#skF_4', D_218))))), inference(resolution, [status(thm)], [c_1197, c_1115])).
% 5.87/2.11  tff(c_1298, plain, (![A_13]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_13)), A_13) | ~r1_tarski(A_13, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_873, c_1285])).
% 5.87/2.11  tff(c_28, plain, (![D_27, B_25, C_26, A_24]: (m1_subset_1(D_27, k1_zfmisc_1(k2_zfmisc_1(B_25, C_26))) | ~r1_tarski(k1_relat_1(D_27), B_25) | ~m1_subset_1(D_27, k1_zfmisc_1(k2_zfmisc_1(A_24, C_26))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.87/2.11  tff(c_3592, plain, (![B_341, C_343, A_344, B_340, D_342]: (m1_subset_1(k2_partfun1(A_344, B_340, C_343, D_342), k1_zfmisc_1(k2_zfmisc_1(B_341, B_340))) | ~r1_tarski(k1_relat_1(k2_partfun1(A_344, B_340, C_343, D_342)), B_341) | ~m1_subset_1(C_343, k1_zfmisc_1(k2_zfmisc_1(A_344, B_340))) | ~v1_funct_1(C_343))), inference(resolution, [status(thm)], [c_886, c_28])).
% 5.87/2.11  tff(c_3635, plain, (![D_138, B_341]: (m1_subset_1(k7_relat_1('#skF_4', D_138), k1_zfmisc_1(k2_zfmisc_1(B_341, '#skF_2'))) | ~r1_tarski(k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_138)), B_341) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_423, c_3592])).
% 5.87/2.11  tff(c_3708, plain, (![D_346, B_347]: (m1_subset_1(k7_relat_1('#skF_4', D_346), k1_zfmisc_1(k2_zfmisc_1(B_347, '#skF_2'))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', D_346)), B_347))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_423, c_3635])).
% 5.87/2.11  tff(c_230, plain, (![A_84, B_85, C_86, D_87]: (v1_funct_1(k2_partfun1(A_84, B_85, C_86, D_87)) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))) | ~v1_funct_1(C_86))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.87/2.11  tff(c_232, plain, (![D_87]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_87)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_230])).
% 5.87/2.11  tff(c_239, plain, (![D_87]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_87)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_232])).
% 5.87/2.11  tff(c_48, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.87/2.11  tff(c_140, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_48])).
% 5.87/2.11  tff(c_242, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_239, c_140])).
% 5.87/2.11  tff(c_243, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_48])).
% 5.87/2.11  tff(c_294, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_243])).
% 5.87/2.11  tff(c_425, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_423, c_294])).
% 5.87/2.11  tff(c_3777, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3')), inference(resolution, [status(thm)], [c_3708, c_425])).
% 5.87/2.11  tff(c_3800, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_1298, c_3777])).
% 5.87/2.11  tff(c_3812, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_3800])).
% 5.87/2.11  tff(c_3814, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_243])).
% 5.87/2.11  tff(c_3874, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_3814, c_3861])).
% 5.87/2.11  tff(c_4008, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4003, c_4003, c_3874])).
% 5.87/2.11  tff(c_3813, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_243])).
% 5.87/2.11  tff(c_4013, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4003, c_3813])).
% 5.87/2.11  tff(c_4012, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4003, c_3814])).
% 5.87/2.11  tff(c_4147, plain, (![B_397, C_398, A_399]: (k1_xboole_0=B_397 | v1_funct_2(C_398, A_399, B_397) | k1_relset_1(A_399, B_397, C_398)!=A_399 | ~m1_subset_1(C_398, k1_zfmisc_1(k2_zfmisc_1(A_399, B_397))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.87/2.11  tff(c_4150, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_4012, c_4147])).
% 5.87/2.11  tff(c_4162, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_4013, c_63, c_4150])).
% 5.87/2.11  tff(c_4285, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4008, c_4162])).
% 5.87/2.11  tff(c_4345, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4112, c_4285])).
% 5.87/2.11  tff(c_4349, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_4345])).
% 5.87/2.11  tff(c_4350, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_50])).
% 5.87/2.11  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.87/2.11  tff(c_4363, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4350, c_4350, c_6])).
% 5.87/2.11  tff(c_4351, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_50])).
% 5.87/2.11  tff(c_4356, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4350, c_4351])).
% 5.87/2.11  tff(c_4362, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4356, c_54])).
% 5.87/2.11  tff(c_4364, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4363, c_4362])).
% 5.87/2.11  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.87/2.11  tff(c_4372, plain, (![B_3]: (k2_zfmisc_1('#skF_1', B_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4350, c_4350, c_8])).
% 5.87/2.11  tff(c_4658, plain, (![C_466, A_467, B_468]: (v1_relat_1(C_466) | ~m1_subset_1(C_466, k1_zfmisc_1(k2_zfmisc_1(A_467, B_468))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.87/2.11  tff(c_4663, plain, (![C_469]: (v1_relat_1(C_469) | ~m1_subset_1(C_469, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4372, c_4658])).
% 5.87/2.11  tff(c_4667, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4364, c_4663])).
% 5.87/2.11  tff(c_4694, plain, (![C_475, A_476, B_477]: (v4_relat_1(C_475, A_476) | ~m1_subset_1(C_475, k1_zfmisc_1(k2_zfmisc_1(A_476, B_477))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.87/2.11  tff(c_4898, plain, (![C_531]: (v4_relat_1(C_531, '#skF_1') | ~m1_subset_1(C_531, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4372, c_4694])).
% 5.87/2.11  tff(c_4902, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_4364, c_4898])).
% 5.87/2.11  tff(c_4903, plain, (![B_532, A_533]: (k7_relat_1(B_532, A_533)=B_532 | ~v4_relat_1(B_532, A_533) | ~v1_relat_1(B_532))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.87/2.11  tff(c_4906, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4902, c_4903])).
% 5.87/2.11  tff(c_4909, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4667, c_4906])).
% 5.87/2.11  tff(c_4668, plain, (![B_470, A_471]: (r1_tarski(k1_relat_1(k7_relat_1(B_470, A_471)), A_471) | ~v1_relat_1(B_470))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.87/2.11  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.87/2.11  tff(c_4394, plain, (![A_1]: (A_1='#skF_1' | ~r1_tarski(A_1, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4350, c_4350, c_2])).
% 5.87/2.11  tff(c_4673, plain, (![B_470]: (k1_relat_1(k7_relat_1(B_470, '#skF_1'))='#skF_1' | ~v1_relat_1(B_470))), inference(resolution, [status(thm)], [c_4668, c_4394])).
% 5.87/2.11  tff(c_4913, plain, (k1_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4909, c_4673])).
% 5.87/2.11  tff(c_4920, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4667, c_4913])).
% 5.87/2.11  tff(c_5034, plain, (![A_551, B_552, C_553]: (k1_relset_1(A_551, B_552, C_553)=k1_relat_1(C_553) | ~m1_subset_1(C_553, k1_zfmisc_1(k2_zfmisc_1(A_551, B_552))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.87/2.11  tff(c_5041, plain, (![B_554, C_555]: (k1_relset_1('#skF_1', B_554, C_555)=k1_relat_1(C_555) | ~m1_subset_1(C_555, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4372, c_5034])).
% 5.87/2.11  tff(c_5045, plain, (![B_554]: (k1_relset_1('#skF_1', B_554, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_4364, c_5041])).
% 5.87/2.11  tff(c_5048, plain, (![B_554]: (k1_relset_1('#skF_1', B_554, '#skF_4')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4920, c_5045])).
% 5.87/2.11  tff(c_34, plain, (![C_30, B_29]: (v1_funct_2(C_30, k1_xboole_0, B_29) | k1_relset_1(k1_xboole_0, B_29, C_30)!=k1_xboole_0 | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_29))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.87/2.11  tff(c_60, plain, (![C_30, B_29]: (v1_funct_2(C_30, k1_xboole_0, B_29) | k1_relset_1(k1_xboole_0, B_29, C_30)!=k1_xboole_0 | ~m1_subset_1(C_30, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_34])).
% 5.87/2.11  tff(c_5115, plain, (![C_563, B_564]: (v1_funct_2(C_563, '#skF_1', B_564) | k1_relset_1('#skF_1', B_564, C_563)!='#skF_1' | ~m1_subset_1(C_563, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4350, c_4350, c_4350, c_4350, c_60])).
% 5.87/2.11  tff(c_5119, plain, (![B_564]: (v1_funct_2('#skF_4', '#skF_1', B_564) | k1_relset_1('#skF_1', B_564, '#skF_4')!='#skF_1')), inference(resolution, [status(thm)], [c_4364, c_5115])).
% 5.87/2.11  tff(c_5123, plain, (![B_564]: (v1_funct_2('#skF_4', '#skF_1', B_564))), inference(demodulation, [status(thm), theory('equality')], [c_5048, c_5119])).
% 5.87/2.11  tff(c_4929, plain, (![C_534, A_535]: (v4_relat_1(C_534, A_535) | ~m1_subset_1(C_534, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4363, c_4694])).
% 5.87/2.11  tff(c_4934, plain, (![A_536]: (v4_relat_1('#skF_4', A_536))), inference(resolution, [status(thm)], [c_4364, c_4929])).
% 5.87/2.11  tff(c_4937, plain, (![A_536]: (k7_relat_1('#skF_4', A_536)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_4934, c_14])).
% 5.87/2.11  tff(c_4940, plain, (![A_536]: (k7_relat_1('#skF_4', A_536)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4667, c_4937])).
% 5.87/2.11  tff(c_5177, plain, (![A_583, B_584, C_585, D_586]: (k2_partfun1(A_583, B_584, C_585, D_586)=k7_relat_1(C_585, D_586) | ~m1_subset_1(C_585, k1_zfmisc_1(k2_zfmisc_1(A_583, B_584))) | ~v1_funct_1(C_585))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.87/2.11  tff(c_5183, plain, (![B_589, C_590, D_591]: (k2_partfun1('#skF_1', B_589, C_590, D_591)=k7_relat_1(C_590, D_591) | ~m1_subset_1(C_590, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_590))), inference(superposition, [status(thm), theory('equality')], [c_4372, c_5177])).
% 5.87/2.11  tff(c_5187, plain, (![B_589, D_591]: (k2_partfun1('#skF_1', B_589, '#skF_4', D_591)=k7_relat_1('#skF_4', D_591) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4364, c_5183])).
% 5.87/2.11  tff(c_5193, plain, (![B_589, D_591]: (k2_partfun1('#skF_1', B_589, '#skF_4', D_591)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_4940, c_5187])).
% 5.87/2.11  tff(c_4707, plain, (![C_479, A_480]: (v4_relat_1(C_479, A_480) | ~m1_subset_1(C_479, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4363, c_4694])).
% 5.87/2.11  tff(c_4710, plain, (![A_480]: (v4_relat_1('#skF_4', A_480))), inference(resolution, [status(thm)], [c_4364, c_4707])).
% 5.87/2.11  tff(c_4713, plain, (![B_482, A_483]: (k7_relat_1(B_482, A_483)=B_482 | ~v4_relat_1(B_482, A_483) | ~v1_relat_1(B_482))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.87/2.11  tff(c_4716, plain, (![A_480]: (k7_relat_1('#skF_4', A_480)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_4710, c_4713])).
% 5.87/2.11  tff(c_4719, plain, (![A_480]: (k7_relat_1('#skF_4', A_480)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4667, c_4716])).
% 5.87/2.11  tff(c_4879, plain, (![A_524, B_525, C_526, D_527]: (k2_partfun1(A_524, B_525, C_526, D_527)=k7_relat_1(C_526, D_527) | ~m1_subset_1(C_526, k1_zfmisc_1(k2_zfmisc_1(A_524, B_525))) | ~v1_funct_1(C_526))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.87/2.11  tff(c_4884, plain, (![B_528, C_529, D_530]: (k2_partfun1('#skF_1', B_528, C_529, D_530)=k7_relat_1(C_529, D_530) | ~m1_subset_1(C_529, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_529))), inference(superposition, [status(thm), theory('equality')], [c_4372, c_4879])).
% 5.87/2.11  tff(c_4886, plain, (![B_528, D_530]: (k2_partfun1('#skF_1', B_528, '#skF_4', D_530)=k7_relat_1('#skF_4', D_530) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4364, c_4884])).
% 5.87/2.11  tff(c_4889, plain, (![B_528, D_530]: (k2_partfun1('#skF_1', B_528, '#skF_4', D_530)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_4719, c_4886])).
% 5.87/2.11  tff(c_4578, plain, (![A_447, B_448, C_449, D_450]: (v1_funct_1(k2_partfun1(A_447, B_448, C_449, D_450)) | ~m1_subset_1(C_449, k1_zfmisc_1(k2_zfmisc_1(A_447, B_448))) | ~v1_funct_1(C_449))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.87/2.11  tff(c_4630, plain, (![A_461, C_462, D_463]: (v1_funct_1(k2_partfun1(A_461, '#skF_1', C_462, D_463)) | ~m1_subset_1(C_462, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_462))), inference(superposition, [status(thm), theory('equality')], [c_4363, c_4578])).
% 5.87/2.11  tff(c_4632, plain, (![A_461, D_463]: (v1_funct_1(k2_partfun1(A_461, '#skF_1', '#skF_4', D_463)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4364, c_4630])).
% 5.87/2.11  tff(c_4635, plain, (![A_461, D_463]: (v1_funct_1(k2_partfun1(A_461, '#skF_1', '#skF_4', D_463)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_4632])).
% 5.87/2.11  tff(c_4395, plain, (![A_413]: (A_413='#skF_1' | ~r1_tarski(A_413, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4350, c_4350, c_2])).
% 5.87/2.11  tff(c_4399, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_52, c_4395])).
% 5.87/2.11  tff(c_4405, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4399, c_4356, c_4399, c_4399, c_4356, c_4356, c_4399, c_4363, c_4356, c_4356, c_48])).
% 5.87/2.11  tff(c_4406, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(splitLeft, [status(thm)], [c_4405])).
% 5.87/2.11  tff(c_4638, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4635, c_4406])).
% 5.87/2.11  tff(c_4639, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_4405])).
% 5.87/2.11  tff(c_4701, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_4639])).
% 5.87/2.11  tff(c_4891, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4889, c_4701])).
% 5.87/2.11  tff(c_4895, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4364, c_4891])).
% 5.87/2.11  tff(c_4896, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_4639])).
% 5.87/2.11  tff(c_5204, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5193, c_4896])).
% 5.87/2.11  tff(c_5217, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5123, c_5204])).
% 5.87/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.87/2.11  
% 5.87/2.11  Inference rules
% 5.87/2.11  ----------------------
% 5.87/2.11  #Ref     : 0
% 5.87/2.11  #Sup     : 1118
% 5.87/2.11  #Fact    : 0
% 5.87/2.11  #Define  : 0
% 5.87/2.11  #Split   : 20
% 5.87/2.11  #Chain   : 0
% 5.87/2.11  #Close   : 0
% 5.87/2.11  
% 5.87/2.11  Ordering : KBO
% 5.87/2.11  
% 5.87/2.11  Simplification rules
% 5.87/2.11  ----------------------
% 5.87/2.11  #Subsume      : 138
% 5.87/2.11  #Demod        : 1194
% 5.87/2.11  #Tautology    : 509
% 5.87/2.11  #SimpNegUnit  : 26
% 5.87/2.11  #BackRed      : 61
% 5.87/2.11  
% 5.87/2.11  #Partial instantiations: 0
% 5.87/2.11  #Strategies tried      : 1
% 5.87/2.11  
% 5.87/2.11  Timing (in seconds)
% 5.87/2.11  ----------------------
% 5.87/2.12  Preprocessing        : 0.34
% 5.87/2.12  Parsing              : 0.19
% 5.87/2.12  CNF conversion       : 0.02
% 5.87/2.12  Main loop            : 0.99
% 5.87/2.12  Inferencing          : 0.35
% 5.87/2.12  Reduction            : 0.35
% 5.87/2.12  Demodulation         : 0.26
% 5.87/2.12  BG Simplification    : 0.04
% 5.87/2.12  Subsumption          : 0.17
% 5.87/2.12  Abstraction          : 0.05
% 5.87/2.12  MUC search           : 0.00
% 5.87/2.12  Cooper               : 0.00
% 5.87/2.12  Total                : 1.39
% 5.87/2.12  Index Insertion      : 0.00
% 5.87/2.12  Index Deletion       : 0.00
% 5.87/2.12  Index Matching       : 0.00
% 5.87/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
