%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:56 EST 2020

% Result     : Theorem 27.22s
% Output     : CNFRefutation 27.22s
% Verified   : 
% Statistics : Number of formulae       :  139 (1697 expanded)
%              Number of leaves         :   47 ( 627 expanded)
%              Depth                    :   31
%              Number of atoms          :  291 (6606 expanded)
%              Number of equality atoms :   75 (1826 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_183,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,B,C)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ( ( k2_relset_1(A,C,k1_partfun1(A,B,B,C,D,E)) = C
                & v2_funct_1(E) )
             => ( C = k1_xboole_0
                | k2_relset_1(A,B,D) = B ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_funct_2)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_139,axiom,(
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

tff(f_93,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_161,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_151,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(c_80,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_112,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_120,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_112])).

tff(c_161,plain,(
    ! [C_66,B_67,A_68] :
      ( v5_relat_1(C_66,B_67)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_68,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_169,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_161])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_246,plain,(
    ! [A_81,B_82,C_83] :
      ( k2_relset_1(A_81,B_82,C_83) = k2_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_254,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_246])).

tff(c_66,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_259,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_66])).

tff(c_74,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_119,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_112])).

tff(c_78,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_70,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_24,plain,(
    ! [A_12] :
      ( v1_relat_1(k2_funct_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_76,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_229,plain,(
    ! [A_78,B_79,C_80] :
      ( k1_relset_1(A_78,B_79,C_80) = k1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_236,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_229])).

tff(c_494,plain,(
    ! [B_112,A_113,C_114] :
      ( k1_xboole_0 = B_112
      | k1_relset_1(A_113,B_112,C_114) = A_113
      | ~ v1_funct_2(C_114,A_113,B_112)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_113,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_497,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_494])).

tff(c_503,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_236,c_497])).

tff(c_504,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_503])).

tff(c_188,plain,(
    ! [A_74] :
      ( k2_relat_1(k2_funct_1(A_74)) = k1_relat_1(A_74)
      | ~ v2_funct_1(A_74)
      | ~ v1_funct_1(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_134,plain,(
    ! [B_59,A_60] :
      ( v5_relat_1(B_59,A_60)
      | ~ r1_tarski(k2_relat_1(B_59),A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_146,plain,(
    ! [B_59] :
      ( v5_relat_1(B_59,k2_relat_1(B_59))
      | ~ v1_relat_1(B_59) ) ),
    inference(resolution,[status(thm)],[c_6,c_134])).

tff(c_194,plain,(
    ! [A_74] :
      ( v5_relat_1(k2_funct_1(A_74),k1_relat_1(A_74))
      | ~ v1_relat_1(k2_funct_1(A_74))
      | ~ v2_funct_1(A_74)
      | ~ v1_funct_1(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_146])).

tff(c_512,plain,
    ( v5_relat_1(k2_funct_1('#skF_5'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_504,c_194])).

tff(c_516,plain,
    ( v5_relat_1(k2_funct_1('#skF_5'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_78,c_70,c_512])).

tff(c_551,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_516])).

tff(c_554,plain,
    ( ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_551])).

tff(c_558,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_78,c_70,c_554])).

tff(c_560,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_516])).

tff(c_18,plain,(
    ! [A_11] : k2_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_36,plain,(
    ! [A_18] :
      ( k5_relat_1(A_18,k2_funct_1(A_18)) = k6_relat_1(k1_relat_1(A_18))
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_168,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_161])).

tff(c_84,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_700,plain,(
    ! [E_140,A_141,C_144,D_142,F_143,B_145] :
      ( k1_partfun1(A_141,B_145,C_144,D_142,E_140,F_143) = k5_relat_1(E_140,F_143)
      | ~ m1_subset_1(F_143,k1_zfmisc_1(k2_zfmisc_1(C_144,D_142)))
      | ~ v1_funct_1(F_143)
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(A_141,B_145)))
      | ~ v1_funct_1(E_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_702,plain,(
    ! [A_141,B_145,E_140] :
      ( k1_partfun1(A_141,B_145,'#skF_2','#skF_3',E_140,'#skF_5') = k5_relat_1(E_140,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(A_141,B_145)))
      | ~ v1_funct_1(E_140) ) ),
    inference(resolution,[status(thm)],[c_74,c_700])).

tff(c_781,plain,(
    ! [A_152,B_153,E_154] :
      ( k1_partfun1(A_152,B_153,'#skF_2','#skF_3',E_154,'#skF_5') = k5_relat_1(E_154,'#skF_5')
      | ~ m1_subset_1(E_154,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153)))
      | ~ v1_funct_1(E_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_702])).

tff(c_787,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_781])).

tff(c_793,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_787])).

tff(c_72,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_800,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_793,c_72])).

tff(c_809,plain,(
    ! [C_160,B_159,A_155,F_157,D_156,E_158] :
      ( m1_subset_1(k1_partfun1(A_155,B_159,C_160,D_156,E_158,F_157),k1_zfmisc_1(k2_zfmisc_1(A_155,D_156)))
      | ~ m1_subset_1(F_157,k1_zfmisc_1(k2_zfmisc_1(C_160,D_156)))
      | ~ v1_funct_1(F_157)
      | ~ m1_subset_1(E_158,k1_zfmisc_1(k2_zfmisc_1(A_155,B_159)))
      | ~ v1_funct_1(E_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_858,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_793,c_809])).

tff(c_878,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_78,c_74,c_858])).

tff(c_46,plain,(
    ! [A_28,B_29,C_30] :
      ( k2_relset_1(A_28,B_29,C_30) = k2_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_902,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_878,c_46])).

tff(c_937,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_800,c_902])).

tff(c_14,plain,(
    ! [A_8,B_10] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_8,B_10)),k2_relat_1(B_10))
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_123,plain,(
    ! [B_57,A_58] :
      ( r1_tarski(k2_relat_1(B_57),A_58)
      | ~ v5_relat_1(B_57,A_58)
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_297,plain,(
    ! [B_91,A_92] :
      ( k2_relat_1(B_91) = A_92
      | ~ r1_tarski(A_92,k2_relat_1(B_91))
      | ~ v5_relat_1(B_91,A_92)
      | ~ v1_relat_1(B_91) ) ),
    inference(resolution,[status(thm)],[c_123,c_2])).

tff(c_320,plain,(
    ! [A_8,B_10] :
      ( k2_relat_1(k5_relat_1(A_8,B_10)) = k2_relat_1(B_10)
      | ~ v5_relat_1(B_10,k2_relat_1(k5_relat_1(A_8,B_10)))
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_297])).

tff(c_953,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = k2_relat_1('#skF_5')
    | ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_937,c_320])).

tff(c_995,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_119,c_168,c_937,c_953])).

tff(c_12,plain,(
    ! [B_7,A_5] :
      ( k9_relat_1(B_7,k2_relat_1(A_5)) = k2_relat_1(k5_relat_1(A_5,B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1046,plain,(
    ! [B_7] :
      ( k2_relat_1(k5_relat_1('#skF_5',B_7)) = k9_relat_1(B_7,'#skF_3')
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_995,c_12])).

tff(c_1428,plain,(
    ! [B_174] :
      ( k2_relat_1(k5_relat_1('#skF_5',B_174)) = k9_relat_1(B_174,'#skF_3')
      | ~ v1_relat_1(B_174) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_1046])).

tff(c_1495,plain,
    ( k2_relat_1(k6_relat_1(k1_relat_1('#skF_5'))) = k9_relat_1(k2_funct_1('#skF_5'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1428])).

tff(c_1509,plain,(
    k9_relat_1(k2_funct_1('#skF_5'),'#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_78,c_70,c_560,c_18,c_504,c_1495])).

tff(c_28,plain,(
    ! [B_16,A_15] :
      ( k10_relat_1(k2_funct_1(B_16),A_15) = k9_relat_1(B_16,A_15)
      | ~ v2_funct_1(B_16)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_22,plain,(
    ! [A_12] :
      ( v1_funct_1(k2_funct_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1476,plain,(
    ! [B_174] :
      ( r1_tarski(k9_relat_1(B_174,'#skF_3'),k2_relat_1(B_174))
      | ~ v1_relat_1(B_174)
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1(B_174) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1428,c_14])).

tff(c_1534,plain,(
    ! [B_175] :
      ( r1_tarski(k9_relat_1(B_175,'#skF_3'),k2_relat_1(B_175))
      | ~ v1_relat_1(B_175) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_1476])).

tff(c_1544,plain,
    ( r1_tarski('#skF_2',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1509,c_1534])).

tff(c_1567,plain,(
    r1_tarski('#skF_2',k2_relat_1(k2_funct_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_1544])).

tff(c_26,plain,(
    ! [B_14,A_13] :
      ( k9_relat_1(B_14,k10_relat_1(B_14,A_13)) = A_13
      | ~ r1_tarski(A_13,k2_relat_1(B_14))
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1573,plain,
    ( k9_relat_1(k2_funct_1('#skF_5'),k10_relat_1(k2_funct_1('#skF_5'),'#skF_2')) = '#skF_2'
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1567,c_26])).

tff(c_1584,plain,
    ( k9_relat_1(k2_funct_1('#skF_5'),k10_relat_1(k2_funct_1('#skF_5'),'#skF_2')) = '#skF_2'
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_1573])).

tff(c_3186,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1584])).

tff(c_3189,plain,
    ( ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_3186])).

tff(c_3193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_78,c_70,c_3189])).

tff(c_3195,plain,(
    v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1584])).

tff(c_559,plain,(
    v5_relat_1(k2_funct_1('#skF_5'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_516])).

tff(c_129,plain,(
    ! [B_57,A_58] :
      ( k2_relat_1(B_57) = A_58
      | ~ r1_tarski(A_58,k2_relat_1(B_57))
      | ~ v5_relat_1(B_57,A_58)
      | ~ v1_relat_1(B_57) ) ),
    inference(resolution,[status(thm)],[c_123,c_2])).

tff(c_1576,plain,
    ( k2_relat_1(k2_funct_1('#skF_5')) = '#skF_2'
    | ~ v5_relat_1(k2_funct_1('#skF_5'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1567,c_129])).

tff(c_1587,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_559,c_1576])).

tff(c_1618,plain,(
    ! [A_13] :
      ( k9_relat_1(k2_funct_1('#skF_5'),k10_relat_1(k2_funct_1('#skF_5'),A_13)) = A_13
      | ~ r1_tarski(A_13,'#skF_2')
      | ~ v1_funct_1(k2_funct_1('#skF_5'))
      | ~ v1_relat_1(k2_funct_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1587,c_26])).

tff(c_1662,plain,(
    ! [A_13] :
      ( k9_relat_1(k2_funct_1('#skF_5'),k10_relat_1(k2_funct_1('#skF_5'),A_13)) = A_13
      | ~ r1_tarski(A_13,'#skF_2')
      | ~ v1_funct_1(k2_funct_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_1618])).

tff(c_8188,plain,(
    ! [A_409] :
      ( k9_relat_1(k2_funct_1('#skF_5'),k10_relat_1(k2_funct_1('#skF_5'),A_409)) = A_409
      | ~ r1_tarski(A_409,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3195,c_1662])).

tff(c_8269,plain,(
    ! [A_15] :
      ( k9_relat_1(k2_funct_1('#skF_5'),k9_relat_1('#skF_5',A_15)) = A_15
      | ~ r1_tarski(A_15,'#skF_2')
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_8188])).

tff(c_8318,plain,(
    ! [A_410] :
      ( k9_relat_1(k2_funct_1('#skF_5'),k9_relat_1('#skF_5',A_410)) = A_410
      | ~ r1_tarski(A_410,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_78,c_70,c_8269])).

tff(c_8375,plain,(
    ! [A_5] :
      ( k9_relat_1(k2_funct_1('#skF_5'),k2_relat_1(k5_relat_1(A_5,'#skF_5'))) = k2_relat_1(A_5)
      | ~ r1_tarski(k2_relat_1(A_5),'#skF_2')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_8318])).

tff(c_51700,plain,(
    ! [A_1311] :
      ( k9_relat_1(k2_funct_1('#skF_5'),k2_relat_1(k5_relat_1(A_1311,'#skF_5'))) = k2_relat_1(A_1311)
      | ~ r1_tarski(k2_relat_1(A_1311),'#skF_2')
      | ~ v1_relat_1(A_1311) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_8375])).

tff(c_51779,plain,
    ( k9_relat_1(k2_funct_1('#skF_5'),'#skF_3') = k2_relat_1('#skF_4')
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_937,c_51700])).

tff(c_51831,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_1509,c_51779])).

tff(c_51832,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_259,c_51831])).

tff(c_51841,plain,
    ( ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_51832])).

tff(c_51845,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_169,c_51841])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:57:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 27.22/16.95  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.22/16.97  
% 27.22/16.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.22/16.97  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 27.22/16.97  
% 27.22/16.97  %Foreground sorts:
% 27.22/16.97  
% 27.22/16.97  
% 27.22/16.97  %Background operators:
% 27.22/16.97  
% 27.22/16.97  
% 27.22/16.97  %Foreground operators:
% 27.22/16.97  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 27.22/16.97  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 27.22/16.97  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 27.22/16.97  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 27.22/16.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 27.22/16.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 27.22/16.97  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 27.22/16.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 27.22/16.97  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 27.22/16.97  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 27.22/16.97  tff('#skF_5', type, '#skF_5': $i).
% 27.22/16.97  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 27.22/16.97  tff('#skF_2', type, '#skF_2': $i).
% 27.22/16.97  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 27.22/16.97  tff('#skF_3', type, '#skF_3': $i).
% 27.22/16.97  tff('#skF_1', type, '#skF_1': $i).
% 27.22/16.97  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 27.22/16.97  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 27.22/16.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 27.22/16.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 27.22/16.97  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 27.22/16.97  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 27.22/16.97  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 27.22/16.97  tff('#skF_4', type, '#skF_4': $i).
% 27.22/16.97  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 27.22/16.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 27.22/16.97  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 27.22/16.97  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 27.22/16.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 27.22/16.97  
% 27.22/17.00  tff(f_183, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_funct_2)).
% 27.22/17.00  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 27.22/17.00  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 27.22/17.00  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 27.22/17.00  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 27.22/17.00  tff(f_67, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 27.22/17.00  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 27.22/17.00  tff(f_139, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 27.22/17.00  tff(f_93, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 27.22/17.00  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 27.22/17.00  tff(f_55, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 27.22/17.00  tff(f_103, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 27.22/17.00  tff(f_161, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 27.22/17.00  tff(f_151, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 27.22/17.00  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 27.22/17.00  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 27.22/17.00  tff(f_83, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_funct_1)).
% 27.22/17.00  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 27.22/17.00  tff(c_80, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 27.22/17.00  tff(c_112, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 27.22/17.00  tff(c_120, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_112])).
% 27.22/17.00  tff(c_161, plain, (![C_66, B_67, A_68]: (v5_relat_1(C_66, B_67) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_68, B_67))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 27.22/17.00  tff(c_169, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_80, c_161])).
% 27.22/17.00  tff(c_10, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 27.22/17.00  tff(c_246, plain, (![A_81, B_82, C_83]: (k2_relset_1(A_81, B_82, C_83)=k2_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 27.22/17.00  tff(c_254, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_246])).
% 27.22/17.00  tff(c_66, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_183])).
% 27.22/17.00  tff(c_259, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_254, c_66])).
% 27.22/17.00  tff(c_74, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 27.22/17.00  tff(c_119, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_112])).
% 27.22/17.00  tff(c_78, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_183])).
% 27.22/17.00  tff(c_70, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_183])).
% 27.22/17.00  tff(c_24, plain, (![A_12]: (v1_relat_1(k2_funct_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_67])).
% 27.22/17.00  tff(c_68, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_183])).
% 27.22/17.00  tff(c_76, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 27.22/17.00  tff(c_229, plain, (![A_78, B_79, C_80]: (k1_relset_1(A_78, B_79, C_80)=k1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 27.22/17.00  tff(c_236, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_229])).
% 27.22/17.00  tff(c_494, plain, (![B_112, A_113, C_114]: (k1_xboole_0=B_112 | k1_relset_1(A_113, B_112, C_114)=A_113 | ~v1_funct_2(C_114, A_113, B_112) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_113, B_112))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.22/17.00  tff(c_497, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_494])).
% 27.22/17.00  tff(c_503, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_236, c_497])).
% 27.22/17.00  tff(c_504, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_68, c_503])).
% 27.22/17.00  tff(c_188, plain, (![A_74]: (k2_relat_1(k2_funct_1(A_74))=k1_relat_1(A_74) | ~v2_funct_1(A_74) | ~v1_funct_1(A_74) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_93])).
% 27.22/17.00  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 27.22/17.00  tff(c_134, plain, (![B_59, A_60]: (v5_relat_1(B_59, A_60) | ~r1_tarski(k2_relat_1(B_59), A_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_37])).
% 27.22/17.00  tff(c_146, plain, (![B_59]: (v5_relat_1(B_59, k2_relat_1(B_59)) | ~v1_relat_1(B_59))), inference(resolution, [status(thm)], [c_6, c_134])).
% 27.22/17.00  tff(c_194, plain, (![A_74]: (v5_relat_1(k2_funct_1(A_74), k1_relat_1(A_74)) | ~v1_relat_1(k2_funct_1(A_74)) | ~v2_funct_1(A_74) | ~v1_funct_1(A_74) | ~v1_relat_1(A_74))), inference(superposition, [status(thm), theory('equality')], [c_188, c_146])).
% 27.22/17.00  tff(c_512, plain, (v5_relat_1(k2_funct_1('#skF_5'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_504, c_194])).
% 27.22/17.00  tff(c_516, plain, (v5_relat_1(k2_funct_1('#skF_5'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_78, c_70, c_512])).
% 27.22/17.00  tff(c_551, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_516])).
% 27.22/17.00  tff(c_554, plain, (~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_24, c_551])).
% 27.22/17.00  tff(c_558, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_119, c_78, c_70, c_554])).
% 27.22/17.00  tff(c_560, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_516])).
% 27.22/17.00  tff(c_18, plain, (![A_11]: (k2_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_55])).
% 27.22/17.00  tff(c_36, plain, (![A_18]: (k5_relat_1(A_18, k2_funct_1(A_18))=k6_relat_1(k1_relat_1(A_18)) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_103])).
% 27.22/17.00  tff(c_168, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_161])).
% 27.22/17.00  tff(c_84, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_183])).
% 27.22/17.00  tff(c_700, plain, (![E_140, A_141, C_144, D_142, F_143, B_145]: (k1_partfun1(A_141, B_145, C_144, D_142, E_140, F_143)=k5_relat_1(E_140, F_143) | ~m1_subset_1(F_143, k1_zfmisc_1(k2_zfmisc_1(C_144, D_142))) | ~v1_funct_1(F_143) | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1(A_141, B_145))) | ~v1_funct_1(E_140))), inference(cnfTransformation, [status(thm)], [f_161])).
% 27.22/17.00  tff(c_702, plain, (![A_141, B_145, E_140]: (k1_partfun1(A_141, B_145, '#skF_2', '#skF_3', E_140, '#skF_5')=k5_relat_1(E_140, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1(A_141, B_145))) | ~v1_funct_1(E_140))), inference(resolution, [status(thm)], [c_74, c_700])).
% 27.22/17.00  tff(c_781, plain, (![A_152, B_153, E_154]: (k1_partfun1(A_152, B_153, '#skF_2', '#skF_3', E_154, '#skF_5')=k5_relat_1(E_154, '#skF_5') | ~m1_subset_1(E_154, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))) | ~v1_funct_1(E_154))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_702])).
% 27.22/17.00  tff(c_787, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_781])).
% 27.22/17.00  tff(c_793, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_787])).
% 27.22/17.00  tff(c_72, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_183])).
% 27.22/17.00  tff(c_800, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_793, c_72])).
% 27.22/17.00  tff(c_809, plain, (![C_160, B_159, A_155, F_157, D_156, E_158]: (m1_subset_1(k1_partfun1(A_155, B_159, C_160, D_156, E_158, F_157), k1_zfmisc_1(k2_zfmisc_1(A_155, D_156))) | ~m1_subset_1(F_157, k1_zfmisc_1(k2_zfmisc_1(C_160, D_156))) | ~v1_funct_1(F_157) | ~m1_subset_1(E_158, k1_zfmisc_1(k2_zfmisc_1(A_155, B_159))) | ~v1_funct_1(E_158))), inference(cnfTransformation, [status(thm)], [f_151])).
% 27.22/17.00  tff(c_858, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_793, c_809])).
% 27.22/17.00  tff(c_878, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_78, c_74, c_858])).
% 27.22/17.00  tff(c_46, plain, (![A_28, B_29, C_30]: (k2_relset_1(A_28, B_29, C_30)=k2_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 27.22/17.00  tff(c_902, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_878, c_46])).
% 27.22/17.00  tff(c_937, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_800, c_902])).
% 27.22/17.00  tff(c_14, plain, (![A_8, B_10]: (r1_tarski(k2_relat_1(k5_relat_1(A_8, B_10)), k2_relat_1(B_10)) | ~v1_relat_1(B_10) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 27.22/17.00  tff(c_123, plain, (![B_57, A_58]: (r1_tarski(k2_relat_1(B_57), A_58) | ~v5_relat_1(B_57, A_58) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_37])).
% 27.22/17.00  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 27.22/17.00  tff(c_297, plain, (![B_91, A_92]: (k2_relat_1(B_91)=A_92 | ~r1_tarski(A_92, k2_relat_1(B_91)) | ~v5_relat_1(B_91, A_92) | ~v1_relat_1(B_91))), inference(resolution, [status(thm)], [c_123, c_2])).
% 27.22/17.00  tff(c_320, plain, (![A_8, B_10]: (k2_relat_1(k5_relat_1(A_8, B_10))=k2_relat_1(B_10) | ~v5_relat_1(B_10, k2_relat_1(k5_relat_1(A_8, B_10))) | ~v1_relat_1(B_10) | ~v1_relat_1(A_8))), inference(resolution, [status(thm)], [c_14, c_297])).
% 27.22/17.00  tff(c_953, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1('#skF_5') | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_937, c_320])).
% 27.22/17.00  tff(c_995, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_120, c_119, c_168, c_937, c_953])).
% 27.22/17.00  tff(c_12, plain, (![B_7, A_5]: (k9_relat_1(B_7, k2_relat_1(A_5))=k2_relat_1(k5_relat_1(A_5, B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 27.22/17.00  tff(c_1046, plain, (![B_7]: (k2_relat_1(k5_relat_1('#skF_5', B_7))=k9_relat_1(B_7, '#skF_3') | ~v1_relat_1(B_7) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_995, c_12])).
% 27.22/17.00  tff(c_1428, plain, (![B_174]: (k2_relat_1(k5_relat_1('#skF_5', B_174))=k9_relat_1(B_174, '#skF_3') | ~v1_relat_1(B_174))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_1046])).
% 27.22/17.00  tff(c_1495, plain, (k2_relat_1(k6_relat_1(k1_relat_1('#skF_5')))=k9_relat_1(k2_funct_1('#skF_5'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_36, c_1428])).
% 27.22/17.00  tff(c_1509, plain, (k9_relat_1(k2_funct_1('#skF_5'), '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_119, c_78, c_70, c_560, c_18, c_504, c_1495])).
% 27.22/17.00  tff(c_28, plain, (![B_16, A_15]: (k10_relat_1(k2_funct_1(B_16), A_15)=k9_relat_1(B_16, A_15) | ~v2_funct_1(B_16) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_83])).
% 27.22/17.00  tff(c_22, plain, (![A_12]: (v1_funct_1(k2_funct_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_67])).
% 27.22/17.00  tff(c_1476, plain, (![B_174]: (r1_tarski(k9_relat_1(B_174, '#skF_3'), k2_relat_1(B_174)) | ~v1_relat_1(B_174) | ~v1_relat_1('#skF_5') | ~v1_relat_1(B_174))), inference(superposition, [status(thm), theory('equality')], [c_1428, c_14])).
% 27.22/17.00  tff(c_1534, plain, (![B_175]: (r1_tarski(k9_relat_1(B_175, '#skF_3'), k2_relat_1(B_175)) | ~v1_relat_1(B_175))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_1476])).
% 27.22/17.01  tff(c_1544, plain, (r1_tarski('#skF_2', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1509, c_1534])).
% 27.22/17.01  tff(c_1567, plain, (r1_tarski('#skF_2', k2_relat_1(k2_funct_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_560, c_1544])).
% 27.22/17.01  tff(c_26, plain, (![B_14, A_13]: (k9_relat_1(B_14, k10_relat_1(B_14, A_13))=A_13 | ~r1_tarski(A_13, k2_relat_1(B_14)) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_75])).
% 27.22/17.01  tff(c_1573, plain, (k9_relat_1(k2_funct_1('#skF_5'), k10_relat_1(k2_funct_1('#skF_5'), '#skF_2'))='#skF_2' | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_1567, c_26])).
% 27.22/17.01  tff(c_1584, plain, (k9_relat_1(k2_funct_1('#skF_5'), k10_relat_1(k2_funct_1('#skF_5'), '#skF_2'))='#skF_2' | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_560, c_1573])).
% 27.22/17.01  tff(c_3186, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_1584])).
% 27.22/17.01  tff(c_3189, plain, (~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_3186])).
% 27.22/17.01  tff(c_3193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_119, c_78, c_70, c_3189])).
% 27.22/17.01  tff(c_3195, plain, (v1_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_1584])).
% 27.22/17.01  tff(c_559, plain, (v5_relat_1(k2_funct_1('#skF_5'), '#skF_2')), inference(splitRight, [status(thm)], [c_516])).
% 27.22/17.01  tff(c_129, plain, (![B_57, A_58]: (k2_relat_1(B_57)=A_58 | ~r1_tarski(A_58, k2_relat_1(B_57)) | ~v5_relat_1(B_57, A_58) | ~v1_relat_1(B_57))), inference(resolution, [status(thm)], [c_123, c_2])).
% 27.22/17.01  tff(c_1576, plain, (k2_relat_1(k2_funct_1('#skF_5'))='#skF_2' | ~v5_relat_1(k2_funct_1('#skF_5'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_1567, c_129])).
% 27.22/17.01  tff(c_1587, plain, (k2_relat_1(k2_funct_1('#skF_5'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_560, c_559, c_1576])).
% 27.22/17.01  tff(c_1618, plain, (![A_13]: (k9_relat_1(k2_funct_1('#skF_5'), k10_relat_1(k2_funct_1('#skF_5'), A_13))=A_13 | ~r1_tarski(A_13, '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1587, c_26])).
% 27.22/17.01  tff(c_1662, plain, (![A_13]: (k9_relat_1(k2_funct_1('#skF_5'), k10_relat_1(k2_funct_1('#skF_5'), A_13))=A_13 | ~r1_tarski(A_13, '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_560, c_1618])).
% 27.22/17.01  tff(c_8188, plain, (![A_409]: (k9_relat_1(k2_funct_1('#skF_5'), k10_relat_1(k2_funct_1('#skF_5'), A_409))=A_409 | ~r1_tarski(A_409, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3195, c_1662])).
% 27.22/17.01  tff(c_8269, plain, (![A_15]: (k9_relat_1(k2_funct_1('#skF_5'), k9_relat_1('#skF_5', A_15))=A_15 | ~r1_tarski(A_15, '#skF_2') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_8188])).
% 27.22/17.01  tff(c_8318, plain, (![A_410]: (k9_relat_1(k2_funct_1('#skF_5'), k9_relat_1('#skF_5', A_410))=A_410 | ~r1_tarski(A_410, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_78, c_70, c_8269])).
% 27.22/17.01  tff(c_8375, plain, (![A_5]: (k9_relat_1(k2_funct_1('#skF_5'), k2_relat_1(k5_relat_1(A_5, '#skF_5')))=k2_relat_1(A_5) | ~r1_tarski(k2_relat_1(A_5), '#skF_2') | ~v1_relat_1('#skF_5') | ~v1_relat_1(A_5))), inference(superposition, [status(thm), theory('equality')], [c_12, c_8318])).
% 27.22/17.01  tff(c_51700, plain, (![A_1311]: (k9_relat_1(k2_funct_1('#skF_5'), k2_relat_1(k5_relat_1(A_1311, '#skF_5')))=k2_relat_1(A_1311) | ~r1_tarski(k2_relat_1(A_1311), '#skF_2') | ~v1_relat_1(A_1311))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_8375])).
% 27.22/17.01  tff(c_51779, plain, (k9_relat_1(k2_funct_1('#skF_5'), '#skF_3')=k2_relat_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_937, c_51700])).
% 27.22/17.01  tff(c_51831, plain, (k2_relat_1('#skF_4')='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_1509, c_51779])).
% 27.22/17.01  tff(c_51832, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_259, c_51831])).
% 27.22/17.01  tff(c_51841, plain, (~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_51832])).
% 27.22/17.01  tff(c_51845, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_120, c_169, c_51841])).
% 27.22/17.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.22/17.01  
% 27.22/17.01  Inference rules
% 27.22/17.01  ----------------------
% 27.22/17.01  #Ref     : 0
% 27.22/17.01  #Sup     : 11303
% 27.22/17.01  #Fact    : 0
% 27.22/17.01  #Define  : 0
% 27.22/17.01  #Split   : 112
% 27.22/17.01  #Chain   : 0
% 27.22/17.01  #Close   : 0
% 27.22/17.01  
% 27.22/17.01  Ordering : KBO
% 27.22/17.01  
% 27.22/17.01  Simplification rules
% 27.22/17.01  ----------------------
% 27.22/17.01  #Subsume      : 1923
% 27.22/17.01  #Demod        : 20663
% 27.22/17.01  #Tautology    : 2761
% 27.22/17.01  #SimpNegUnit  : 259
% 27.22/17.01  #BackRed      : 547
% 27.22/17.01  
% 27.22/17.01  #Partial instantiations: 0
% 27.22/17.01  #Strategies tried      : 1
% 27.22/17.01  
% 27.22/17.01  Timing (in seconds)
% 27.22/17.01  ----------------------
% 27.22/17.01  Preprocessing        : 0.40
% 27.52/17.01  Parsing              : 0.21
% 27.52/17.01  CNF conversion       : 0.03
% 27.52/17.01  Main loop            : 15.74
% 27.52/17.01  Inferencing          : 2.81
% 27.52/17.01  Reduction            : 8.69
% 27.52/17.01  Demodulation         : 7.37
% 27.52/17.01  BG Simplification    : 0.24
% 27.52/17.01  Subsumption          : 3.28
% 27.52/17.01  Abstraction          : 0.37
% 27.52/17.01  MUC search           : 0.00
% 27.52/17.01  Cooper               : 0.00
% 27.52/17.01  Total                : 16.21
% 27.52/17.01  Index Insertion      : 0.00
% 27.52/17.01  Index Deletion       : 0.00
% 27.52/17.01  Index Matching       : 0.00
% 27.52/17.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
