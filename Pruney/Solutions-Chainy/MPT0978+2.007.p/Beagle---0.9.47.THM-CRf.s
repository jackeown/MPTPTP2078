%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:53 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 153 expanded)
%              Number of leaves         :   39 (  70 expanded)
%              Depth                    :   10
%              Number of atoms          :  149 ( 411 expanded)
%              Number of equality atoms :   33 (  67 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_121,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
             => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_103,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_57,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_101,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_228,plain,(
    ! [A_77,B_78,C_79] :
      ( k2_relset_1(A_77,B_78,C_79) = k2_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_240,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_228])).

tff(c_44,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_251,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_44])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_93,plain,(
    ! [B_47,A_48] :
      ( v1_relat_1(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48))
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_99,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_93])).

tff(c_108,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_99])).

tff(c_130,plain,(
    ! [C_56,B_57,A_58] :
      ( v5_relat_1(C_56,B_57)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_58,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_141,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_130])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_102,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_48,c_93])).

tff(c_111,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_102])).

tff(c_42,plain,(
    ! [A_37] : k6_relat_1(A_37) = k6_partfun1(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_20,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_59,plain,(
    ! [A_13] : k2_relat_1(k6_partfun1(A_13)) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_20])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_58,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_469,plain,(
    ! [E_119,B_118,C_122,A_120,F_121,D_117] :
      ( k1_partfun1(A_120,B_118,C_122,D_117,E_119,F_121) = k5_relat_1(E_119,F_121)
      | ~ m1_subset_1(F_121,k1_zfmisc_1(k2_zfmisc_1(C_122,D_117)))
      | ~ v1_funct_1(F_121)
      | ~ m1_subset_1(E_119,k1_zfmisc_1(k2_zfmisc_1(A_120,B_118)))
      | ~ v1_funct_1(E_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_473,plain,(
    ! [A_120,B_118,E_119] :
      ( k1_partfun1(A_120,B_118,'#skF_1','#skF_2',E_119,'#skF_3') = k5_relat_1(E_119,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_119,k1_zfmisc_1(k2_zfmisc_1(A_120,B_118)))
      | ~ v1_funct_1(E_119) ) ),
    inference(resolution,[status(thm)],[c_54,c_469])).

tff(c_494,plain,(
    ! [A_125,B_126,E_127] :
      ( k1_partfun1(A_125,B_126,'#skF_1','#skF_2',E_127,'#skF_3') = k5_relat_1(E_127,'#skF_3')
      | ~ m1_subset_1(E_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126)))
      | ~ v1_funct_1(E_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_473])).

tff(c_503,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_494])).

tff(c_510,plain,(
    k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_503])).

tff(c_38,plain,(
    ! [A_30] : m1_subset_1(k6_partfun1(A_30),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_46,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_286,plain,(
    ! [D_83,C_84,A_85,B_86] :
      ( D_83 = C_84
      | ~ r2_relset_1(A_85,B_86,C_84,D_83)
      | ~ m1_subset_1(D_83,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86)))
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_294,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_46,c_286])).

tff(c_309,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_294])).

tff(c_336,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_309])).

tff(c_517,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_336])).

tff(c_528,plain,(
    ! [C_128,B_129,A_132,E_130,D_133,F_131] :
      ( m1_subset_1(k1_partfun1(A_132,B_129,C_128,D_133,E_130,F_131),k1_zfmisc_1(k2_zfmisc_1(A_132,D_133)))
      | ~ m1_subset_1(F_131,k1_zfmisc_1(k2_zfmisc_1(C_128,D_133)))
      | ~ v1_funct_1(F_131)
      | ~ m1_subset_1(E_130,k1_zfmisc_1(k2_zfmisc_1(A_132,B_129)))
      | ~ v1_funct_1(E_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_558,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_528])).

tff(c_575,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_58,c_54,c_558])).

tff(c_577,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_517,c_575])).

tff(c_578,plain,(
    k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_309])).

tff(c_642,plain,(
    ! [A_152,B_150,F_153,C_154,D_149,E_151] :
      ( k1_partfun1(A_152,B_150,C_154,D_149,E_151,F_153) = k5_relat_1(E_151,F_153)
      | ~ m1_subset_1(F_153,k1_zfmisc_1(k2_zfmisc_1(C_154,D_149)))
      | ~ v1_funct_1(F_153)
      | ~ m1_subset_1(E_151,k1_zfmisc_1(k2_zfmisc_1(A_152,B_150)))
      | ~ v1_funct_1(E_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_646,plain,(
    ! [A_152,B_150,E_151] :
      ( k1_partfun1(A_152,B_150,'#skF_1','#skF_2',E_151,'#skF_3') = k5_relat_1(E_151,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_151,k1_zfmisc_1(k2_zfmisc_1(A_152,B_150)))
      | ~ v1_funct_1(E_151) ) ),
    inference(resolution,[status(thm)],[c_54,c_642])).

tff(c_792,plain,(
    ! [A_166,B_167,E_168] :
      ( k1_partfun1(A_166,B_167,'#skF_1','#skF_2',E_168,'#skF_3') = k5_relat_1(E_168,'#skF_3')
      | ~ m1_subset_1(E_168,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167)))
      | ~ v1_funct_1(E_168) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_646])).

tff(c_807,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_792])).

tff(c_818,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_578,c_807])).

tff(c_16,plain,(
    ! [A_10,B_12] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_10,B_12)),k2_relat_1(B_12))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_825,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_2')),k2_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_818,c_16])).

tff(c_831,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_108,c_59,c_825])).

tff(c_120,plain,(
    ! [B_52,A_53] :
      ( r1_tarski(k2_relat_1(B_52),A_53)
      | ~ v5_relat_1(B_52,A_53)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_126,plain,(
    ! [B_52,A_53] :
      ( k2_relat_1(B_52) = A_53
      | ~ r1_tarski(A_53,k2_relat_1(B_52))
      | ~ v5_relat_1(B_52,A_53)
      | ~ v1_relat_1(B_52) ) ),
    inference(resolution,[status(thm)],[c_120,c_2])).

tff(c_835,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_831,c_126])).

tff(c_840,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_141,c_835])).

tff(c_842,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_251,c_840])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:55:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.48  
% 3.20/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.48  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.20/1.48  
% 3.20/1.48  %Foreground sorts:
% 3.20/1.48  
% 3.20/1.48  
% 3.20/1.48  %Background operators:
% 3.20/1.48  
% 3.20/1.48  
% 3.20/1.48  %Foreground operators:
% 3.20/1.48  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.20/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.20/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.48  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.20/1.48  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.20/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.20/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.20/1.48  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.20/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.20/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.20/1.48  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.20/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.20/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.20/1.48  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.20/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.20/1.48  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.20/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.20/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.20/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.20/1.48  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.20/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.48  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.20/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.20/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.20/1.48  
% 3.33/1.50  tff(f_121, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 3.33/1.50  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.33/1.50  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.33/1.50  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.33/1.50  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.33/1.50  tff(f_103, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.33/1.50  tff(f_57, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.33/1.50  tff(f_101, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.33/1.50  tff(f_91, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 3.33/1.50  tff(f_75, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.33/1.50  tff(f_87, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.33/1.50  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 3.33/1.50  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.33/1.50  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.33/1.50  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.33/1.50  tff(c_228, plain, (![A_77, B_78, C_79]: (k2_relset_1(A_77, B_78, C_79)=k2_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.33/1.50  tff(c_240, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_228])).
% 3.33/1.50  tff(c_44, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.33/1.50  tff(c_251, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_240, c_44])).
% 3.33/1.50  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.33/1.50  tff(c_93, plain, (![B_47, A_48]: (v1_relat_1(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.33/1.50  tff(c_99, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_54, c_93])).
% 3.33/1.50  tff(c_108, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_99])).
% 3.33/1.50  tff(c_130, plain, (![C_56, B_57, A_58]: (v5_relat_1(C_56, B_57) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_58, B_57))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.33/1.50  tff(c_141, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_130])).
% 3.33/1.50  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.33/1.50  tff(c_102, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_48, c_93])).
% 3.33/1.50  tff(c_111, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_102])).
% 3.33/1.50  tff(c_42, plain, (![A_37]: (k6_relat_1(A_37)=k6_partfun1(A_37))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.33/1.50  tff(c_20, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.33/1.50  tff(c_59, plain, (![A_13]: (k2_relat_1(k6_partfun1(A_13))=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_20])).
% 3.33/1.50  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.33/1.50  tff(c_58, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.33/1.50  tff(c_469, plain, (![E_119, B_118, C_122, A_120, F_121, D_117]: (k1_partfun1(A_120, B_118, C_122, D_117, E_119, F_121)=k5_relat_1(E_119, F_121) | ~m1_subset_1(F_121, k1_zfmisc_1(k2_zfmisc_1(C_122, D_117))) | ~v1_funct_1(F_121) | ~m1_subset_1(E_119, k1_zfmisc_1(k2_zfmisc_1(A_120, B_118))) | ~v1_funct_1(E_119))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.33/1.50  tff(c_473, plain, (![A_120, B_118, E_119]: (k1_partfun1(A_120, B_118, '#skF_1', '#skF_2', E_119, '#skF_3')=k5_relat_1(E_119, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_119, k1_zfmisc_1(k2_zfmisc_1(A_120, B_118))) | ~v1_funct_1(E_119))), inference(resolution, [status(thm)], [c_54, c_469])).
% 3.33/1.50  tff(c_494, plain, (![A_125, B_126, E_127]: (k1_partfun1(A_125, B_126, '#skF_1', '#skF_2', E_127, '#skF_3')=k5_relat_1(E_127, '#skF_3') | ~m1_subset_1(E_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))) | ~v1_funct_1(E_127))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_473])).
% 3.33/1.50  tff(c_503, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_494])).
% 3.33/1.50  tff(c_510, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_503])).
% 3.33/1.50  tff(c_38, plain, (![A_30]: (m1_subset_1(k6_partfun1(A_30), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.33/1.50  tff(c_46, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.33/1.50  tff(c_286, plain, (![D_83, C_84, A_85, B_86]: (D_83=C_84 | ~r2_relset_1(A_85, B_86, C_84, D_83) | ~m1_subset_1(D_83, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.33/1.50  tff(c_294, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_46, c_286])).
% 3.33/1.50  tff(c_309, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_294])).
% 3.33/1.50  tff(c_336, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_309])).
% 3.33/1.50  tff(c_517, plain, (~m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_510, c_336])).
% 3.33/1.50  tff(c_528, plain, (![C_128, B_129, A_132, E_130, D_133, F_131]: (m1_subset_1(k1_partfun1(A_132, B_129, C_128, D_133, E_130, F_131), k1_zfmisc_1(k2_zfmisc_1(A_132, D_133))) | ~m1_subset_1(F_131, k1_zfmisc_1(k2_zfmisc_1(C_128, D_133))) | ~v1_funct_1(F_131) | ~m1_subset_1(E_130, k1_zfmisc_1(k2_zfmisc_1(A_132, B_129))) | ~v1_funct_1(E_130))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.33/1.50  tff(c_558, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_510, c_528])).
% 3.33/1.50  tff(c_575, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_58, c_54, c_558])).
% 3.33/1.50  tff(c_577, plain, $false, inference(negUnitSimplification, [status(thm)], [c_517, c_575])).
% 3.33/1.50  tff(c_578, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_309])).
% 3.33/1.50  tff(c_642, plain, (![A_152, B_150, F_153, C_154, D_149, E_151]: (k1_partfun1(A_152, B_150, C_154, D_149, E_151, F_153)=k5_relat_1(E_151, F_153) | ~m1_subset_1(F_153, k1_zfmisc_1(k2_zfmisc_1(C_154, D_149))) | ~v1_funct_1(F_153) | ~m1_subset_1(E_151, k1_zfmisc_1(k2_zfmisc_1(A_152, B_150))) | ~v1_funct_1(E_151))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.33/1.50  tff(c_646, plain, (![A_152, B_150, E_151]: (k1_partfun1(A_152, B_150, '#skF_1', '#skF_2', E_151, '#skF_3')=k5_relat_1(E_151, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_151, k1_zfmisc_1(k2_zfmisc_1(A_152, B_150))) | ~v1_funct_1(E_151))), inference(resolution, [status(thm)], [c_54, c_642])).
% 3.33/1.50  tff(c_792, plain, (![A_166, B_167, E_168]: (k1_partfun1(A_166, B_167, '#skF_1', '#skF_2', E_168, '#skF_3')=k5_relat_1(E_168, '#skF_3') | ~m1_subset_1(E_168, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))) | ~v1_funct_1(E_168))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_646])).
% 3.33/1.50  tff(c_807, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_792])).
% 3.33/1.50  tff(c_818, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_578, c_807])).
% 3.33/1.50  tff(c_16, plain, (![A_10, B_12]: (r1_tarski(k2_relat_1(k5_relat_1(A_10, B_12)), k2_relat_1(B_12)) | ~v1_relat_1(B_12) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.33/1.50  tff(c_825, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_2')), k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_818, c_16])).
% 3.33/1.50  tff(c_831, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_108, c_59, c_825])).
% 3.33/1.50  tff(c_120, plain, (![B_52, A_53]: (r1_tarski(k2_relat_1(B_52), A_53) | ~v5_relat_1(B_52, A_53) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.33/1.50  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.33/1.50  tff(c_126, plain, (![B_52, A_53]: (k2_relat_1(B_52)=A_53 | ~r1_tarski(A_53, k2_relat_1(B_52)) | ~v5_relat_1(B_52, A_53) | ~v1_relat_1(B_52))), inference(resolution, [status(thm)], [c_120, c_2])).
% 3.33/1.50  tff(c_835, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_831, c_126])).
% 3.33/1.50  tff(c_840, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_141, c_835])).
% 3.33/1.50  tff(c_842, plain, $false, inference(negUnitSimplification, [status(thm)], [c_251, c_840])).
% 3.33/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.50  
% 3.33/1.50  Inference rules
% 3.33/1.50  ----------------------
% 3.33/1.50  #Ref     : 0
% 3.33/1.50  #Sup     : 161
% 3.33/1.50  #Fact    : 0
% 3.33/1.50  #Define  : 0
% 3.33/1.50  #Split   : 1
% 3.33/1.50  #Chain   : 0
% 3.33/1.50  #Close   : 0
% 3.33/1.50  
% 3.33/1.50  Ordering : KBO
% 3.33/1.50  
% 3.33/1.50  Simplification rules
% 3.33/1.50  ----------------------
% 3.33/1.50  #Subsume      : 9
% 3.33/1.50  #Demod        : 122
% 3.33/1.50  #Tautology    : 46
% 3.33/1.50  #SimpNegUnit  : 2
% 3.33/1.50  #BackRed      : 8
% 3.33/1.50  
% 3.33/1.50  #Partial instantiations: 0
% 3.33/1.50  #Strategies tried      : 1
% 3.33/1.50  
% 3.33/1.50  Timing (in seconds)
% 3.33/1.50  ----------------------
% 3.33/1.50  Preprocessing        : 0.33
% 3.33/1.50  Parsing              : 0.18
% 3.33/1.50  CNF conversion       : 0.02
% 3.33/1.50  Main loop            : 0.39
% 3.33/1.50  Inferencing          : 0.14
% 3.33/1.50  Reduction            : 0.13
% 3.33/1.50  Demodulation         : 0.09
% 3.33/1.50  BG Simplification    : 0.02
% 3.33/1.50  Subsumption          : 0.07
% 3.33/1.50  Abstraction          : 0.02
% 3.33/1.50  MUC search           : 0.00
% 3.33/1.50  Cooper               : 0.00
% 3.33/1.50  Total                : 0.75
% 3.33/1.50  Index Insertion      : 0.00
% 3.33/1.50  Index Deletion       : 0.00
% 3.33/1.50  Index Matching       : 0.00
% 3.33/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
