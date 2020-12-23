%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:42 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 153 expanded)
%              Number of leaves         :   39 (  71 expanded)
%              Depth                    :   12
%              Number of atoms          :  143 ( 462 expanded)
%              Number of equality atoms :   57 ( 175 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,B,C)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ( ( k2_relset_1(A,B,D) = B
                & k2_relset_1(B,C,E) = C )
             => ( C = k1_xboole_0
                | k2_relset_1(A,C,k1_partfun1(A,B,B,C,D,E)) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_funct_2)).

tff(f_104,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_82,axiom,(
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

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_673,plain,(
    ! [D_133,A_136,E_135,F_137,C_138,B_134] :
      ( k1_partfun1(A_136,B_134,C_138,D_133,E_135,F_137) = k5_relat_1(E_135,F_137)
      | ~ m1_subset_1(F_137,k1_zfmisc_1(k2_zfmisc_1(C_138,D_133)))
      | ~ v1_funct_1(F_137)
      | ~ m1_subset_1(E_135,k1_zfmisc_1(k2_zfmisc_1(A_136,B_134)))
      | ~ v1_funct_1(E_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_678,plain,(
    ! [A_136,B_134,E_135] :
      ( k1_partfun1(A_136,B_134,'#skF_2','#skF_3',E_135,'#skF_5') = k5_relat_1(E_135,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_135,k1_zfmisc_1(k2_zfmisc_1(A_136,B_134)))
      | ~ v1_funct_1(E_135) ) ),
    inference(resolution,[status(thm)],[c_50,c_673])).

tff(c_852,plain,(
    ! [A_164,B_165,E_166] :
      ( k1_partfun1(A_164,B_165,'#skF_2','#skF_3',E_166,'#skF_5') = k5_relat_1(E_166,'#skF_5')
      | ~ m1_subset_1(E_166,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165)))
      | ~ v1_funct_1(E_166) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_678])).

tff(c_865,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_852])).

tff(c_877,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_865])).

tff(c_42,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_890,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_877,c_42])).

tff(c_108,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_124,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_108])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_61,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_81,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | ~ m1_subset_1(A_42,k1_zfmisc_1(B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_97,plain,(
    ! [A_2] : r1_tarski(A_2,A_2) ),
    inference(resolution,[status(thm)],[c_61,c_81])).

tff(c_46,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_151,plain,(
    ! [A_56,B_57,C_58] :
      ( k2_relset_1(A_56,B_57,C_58) = k2_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_158,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_151])).

tff(c_168,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_158])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_52,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_10,plain,(
    ! [A_5] :
      ( k10_relat_1(A_5,k2_relat_1(A_5)) = k1_relat_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_175,plain,
    ( k10_relat_1('#skF_5','#skF_3') = k1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_10])).

tff(c_179,plain,(
    k10_relat_1('#skF_5','#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_175])).

tff(c_224,plain,(
    ! [A_64,B_65,C_66,D_67] :
      ( k8_relset_1(A_64,B_65,C_66,D_67) = k10_relat_1(C_66,D_67)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_236,plain,(
    ! [D_67] : k8_relset_1('#skF_2','#skF_3','#skF_5',D_67) = k10_relat_1('#skF_5',D_67) ),
    inference(resolution,[status(thm)],[c_50,c_224])).

tff(c_284,plain,(
    ! [A_78,B_79,C_80] :
      ( k8_relset_1(A_78,B_79,C_80,B_79) = k1_relset_1(A_78,B_79,C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_289,plain,(
    k8_relset_1('#skF_2','#skF_3','#skF_5','#skF_3') = k1_relset_1('#skF_2','#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_284])).

tff(c_297,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_236,c_289])).

tff(c_428,plain,(
    ! [B_107,A_108,C_109] :
      ( k1_xboole_0 = B_107
      | k1_relset_1(A_108,B_107,C_109) = A_108
      | ~ v1_funct_2(C_109,A_108,B_107)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_108,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_435,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_428])).

tff(c_446,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_297,c_435])).

tff(c_447,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_446])).

tff(c_125,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_108])).

tff(c_48,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_161,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_151])).

tff(c_170,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_161])).

tff(c_373,plain,(
    ! [B_95,A_96] :
      ( k2_relat_1(k5_relat_1(B_95,A_96)) = k2_relat_1(A_96)
      | ~ r1_tarski(k1_relat_1(A_96),k2_relat_1(B_95))
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_376,plain,(
    ! [A_96] :
      ( k2_relat_1(k5_relat_1('#skF_4',A_96)) = k2_relat_1(A_96)
      | ~ r1_tarski(k1_relat_1(A_96),'#skF_2')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(A_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_373])).

tff(c_381,plain,(
    ! [A_96] :
      ( k2_relat_1(k5_relat_1('#skF_4',A_96)) = k2_relat_1(A_96)
      | ~ r1_tarski(k1_relat_1(A_96),'#skF_2')
      | ~ v1_relat_1(A_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_376])).

tff(c_461,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = k2_relat_1('#skF_5')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_447,c_381])).

tff(c_470,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_97,c_168,c_461])).

tff(c_36,plain,(
    ! [A_25,F_30,E_29,C_27,D_28,B_26] :
      ( m1_subset_1(k1_partfun1(A_25,B_26,C_27,D_28,E_29,F_30),k1_zfmisc_1(k2_zfmisc_1(A_25,D_28)))
      | ~ m1_subset_1(F_30,k1_zfmisc_1(k2_zfmisc_1(C_27,D_28)))
      | ~ v1_funct_1(F_30)
      | ~ m1_subset_1(E_29,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_1(E_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_894,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_877,c_36])).

tff(c_898,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_54,c_50,c_894])).

tff(c_16,plain,(
    ! [A_12,B_13,C_14] :
      ( k2_relset_1(A_12,B_13,C_14) = k2_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1066,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_898,c_16])).

tff(c_1101,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_1066])).

tff(c_1103,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_890,c_1101])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:10:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.39/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.49  
% 3.39/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.50  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.39/1.50  
% 3.39/1.50  %Foreground sorts:
% 3.39/1.50  
% 3.39/1.50  
% 3.39/1.50  %Background operators:
% 3.39/1.50  
% 3.39/1.50  
% 3.39/1.50  %Foreground operators:
% 3.39/1.50  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.39/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.39/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.50  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.39/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.39/1.50  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.39/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.39/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.39/1.50  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.39/1.50  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.39/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.39/1.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.39/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.39/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.39/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.39/1.50  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.39/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.39/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.50  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.39/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.39/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.39/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.39/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.50  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.39/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.39/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.39/1.50  
% 3.39/1.51  tff(f_126, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, B, D) = B) & (k2_relset_1(B, C, E) = C)) => ((C = k1_xboole_0) | (k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_funct_2)).
% 3.39/1.51  tff(f_104, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.39/1.51  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.39/1.51  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.39/1.51  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.39/1.51  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.39/1.51  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.39/1.51  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 3.39/1.51  tff(f_58, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.39/1.51  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 3.39/1.51  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.39/1.51  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 3.39/1.51  tff(f_94, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.39/1.51  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.39/1.51  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.39/1.51  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.39/1.51  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.39/1.51  tff(c_673, plain, (![D_133, A_136, E_135, F_137, C_138, B_134]: (k1_partfun1(A_136, B_134, C_138, D_133, E_135, F_137)=k5_relat_1(E_135, F_137) | ~m1_subset_1(F_137, k1_zfmisc_1(k2_zfmisc_1(C_138, D_133))) | ~v1_funct_1(F_137) | ~m1_subset_1(E_135, k1_zfmisc_1(k2_zfmisc_1(A_136, B_134))) | ~v1_funct_1(E_135))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.39/1.51  tff(c_678, plain, (![A_136, B_134, E_135]: (k1_partfun1(A_136, B_134, '#skF_2', '#skF_3', E_135, '#skF_5')=k5_relat_1(E_135, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_135, k1_zfmisc_1(k2_zfmisc_1(A_136, B_134))) | ~v1_funct_1(E_135))), inference(resolution, [status(thm)], [c_50, c_673])).
% 3.39/1.51  tff(c_852, plain, (![A_164, B_165, E_166]: (k1_partfun1(A_164, B_165, '#skF_2', '#skF_3', E_166, '#skF_5')=k5_relat_1(E_166, '#skF_5') | ~m1_subset_1(E_166, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))) | ~v1_funct_1(E_166))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_678])).
% 3.39/1.51  tff(c_865, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_852])).
% 3.39/1.51  tff(c_877, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_865])).
% 3.39/1.51  tff(c_42, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.39/1.51  tff(c_890, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_877, c_42])).
% 3.39/1.51  tff(c_108, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.39/1.51  tff(c_124, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_108])).
% 3.39/1.51  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.39/1.51  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.39/1.51  tff(c_61, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 3.39/1.51  tff(c_81, plain, (![A_42, B_43]: (r1_tarski(A_42, B_43) | ~m1_subset_1(A_42, k1_zfmisc_1(B_43)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.39/1.51  tff(c_97, plain, (![A_2]: (r1_tarski(A_2, A_2))), inference(resolution, [status(thm)], [c_61, c_81])).
% 3.39/1.51  tff(c_46, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.39/1.51  tff(c_151, plain, (![A_56, B_57, C_58]: (k2_relset_1(A_56, B_57, C_58)=k2_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.39/1.51  tff(c_158, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_151])).
% 3.39/1.51  tff(c_168, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_158])).
% 3.39/1.51  tff(c_44, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.39/1.51  tff(c_52, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.39/1.51  tff(c_10, plain, (![A_5]: (k10_relat_1(A_5, k2_relat_1(A_5))=k1_relat_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.39/1.51  tff(c_175, plain, (k10_relat_1('#skF_5', '#skF_3')=k1_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_168, c_10])).
% 3.39/1.51  tff(c_179, plain, (k10_relat_1('#skF_5', '#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_175])).
% 3.39/1.51  tff(c_224, plain, (![A_64, B_65, C_66, D_67]: (k8_relset_1(A_64, B_65, C_66, D_67)=k10_relat_1(C_66, D_67) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.39/1.51  tff(c_236, plain, (![D_67]: (k8_relset_1('#skF_2', '#skF_3', '#skF_5', D_67)=k10_relat_1('#skF_5', D_67))), inference(resolution, [status(thm)], [c_50, c_224])).
% 3.39/1.51  tff(c_284, plain, (![A_78, B_79, C_80]: (k8_relset_1(A_78, B_79, C_80, B_79)=k1_relset_1(A_78, B_79, C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.39/1.51  tff(c_289, plain, (k8_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_3')=k1_relset_1('#skF_2', '#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_284])).
% 3.39/1.51  tff(c_297, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_236, c_289])).
% 3.39/1.51  tff(c_428, plain, (![B_107, A_108, C_109]: (k1_xboole_0=B_107 | k1_relset_1(A_108, B_107, C_109)=A_108 | ~v1_funct_2(C_109, A_108, B_107) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_108, B_107))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.39/1.51  tff(c_435, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_428])).
% 3.39/1.51  tff(c_446, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_297, c_435])).
% 3.39/1.51  tff(c_447, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_44, c_446])).
% 3.39/1.51  tff(c_125, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_108])).
% 3.39/1.51  tff(c_48, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.39/1.51  tff(c_161, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_151])).
% 3.39/1.51  tff(c_170, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_161])).
% 3.39/1.51  tff(c_373, plain, (![B_95, A_96]: (k2_relat_1(k5_relat_1(B_95, A_96))=k2_relat_1(A_96) | ~r1_tarski(k1_relat_1(A_96), k2_relat_1(B_95)) | ~v1_relat_1(B_95) | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.39/1.51  tff(c_376, plain, (![A_96]: (k2_relat_1(k5_relat_1('#skF_4', A_96))=k2_relat_1(A_96) | ~r1_tarski(k1_relat_1(A_96), '#skF_2') | ~v1_relat_1('#skF_4') | ~v1_relat_1(A_96))), inference(superposition, [status(thm), theory('equality')], [c_170, c_373])).
% 3.39/1.51  tff(c_381, plain, (![A_96]: (k2_relat_1(k5_relat_1('#skF_4', A_96))=k2_relat_1(A_96) | ~r1_tarski(k1_relat_1(A_96), '#skF_2') | ~v1_relat_1(A_96))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_376])).
% 3.39/1.51  tff(c_461, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1('#skF_5') | ~r1_tarski('#skF_2', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_447, c_381])).
% 3.39/1.51  tff(c_470, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_97, c_168, c_461])).
% 3.39/1.51  tff(c_36, plain, (![A_25, F_30, E_29, C_27, D_28, B_26]: (m1_subset_1(k1_partfun1(A_25, B_26, C_27, D_28, E_29, F_30), k1_zfmisc_1(k2_zfmisc_1(A_25, D_28))) | ~m1_subset_1(F_30, k1_zfmisc_1(k2_zfmisc_1(C_27, D_28))) | ~v1_funct_1(F_30) | ~m1_subset_1(E_29, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_1(E_29))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.39/1.51  tff(c_894, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_877, c_36])).
% 3.39/1.51  tff(c_898, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_54, c_50, c_894])).
% 3.39/1.51  tff(c_16, plain, (![A_12, B_13, C_14]: (k2_relset_1(A_12, B_13, C_14)=k2_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.39/1.51  tff(c_1066, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_898, c_16])).
% 3.39/1.51  tff(c_1101, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_470, c_1066])).
% 3.39/1.51  tff(c_1103, plain, $false, inference(negUnitSimplification, [status(thm)], [c_890, c_1101])).
% 3.39/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.51  
% 3.39/1.51  Inference rules
% 3.39/1.51  ----------------------
% 3.39/1.51  #Ref     : 0
% 3.39/1.51  #Sup     : 227
% 3.39/1.51  #Fact    : 0
% 3.39/1.51  #Define  : 0
% 3.39/1.51  #Split   : 5
% 3.39/1.51  #Chain   : 0
% 3.39/1.51  #Close   : 0
% 3.39/1.51  
% 3.39/1.51  Ordering : KBO
% 3.39/1.51  
% 3.39/1.51  Simplification rules
% 3.39/1.51  ----------------------
% 3.39/1.51  #Subsume      : 12
% 3.39/1.51  #Demod        : 134
% 3.39/1.51  #Tautology    : 88
% 3.39/1.51  #SimpNegUnit  : 11
% 3.39/1.51  #BackRed      : 7
% 3.39/1.51  
% 3.39/1.51  #Partial instantiations: 0
% 3.39/1.51  #Strategies tried      : 1
% 3.39/1.51  
% 3.39/1.51  Timing (in seconds)
% 3.39/1.51  ----------------------
% 3.39/1.52  Preprocessing        : 0.34
% 3.39/1.52  Parsing              : 0.19
% 3.39/1.52  CNF conversion       : 0.02
% 3.39/1.52  Main loop            : 0.41
% 3.39/1.52  Inferencing          : 0.15
% 3.39/1.52  Reduction            : 0.14
% 3.39/1.52  Demodulation         : 0.10
% 3.39/1.52  BG Simplification    : 0.02
% 3.39/1.52  Subsumption          : 0.07
% 3.39/1.52  Abstraction          : 0.02
% 3.39/1.52  MUC search           : 0.00
% 3.39/1.52  Cooper               : 0.00
% 3.39/1.52  Total                : 0.79
% 3.39/1.52  Index Insertion      : 0.00
% 3.39/1.52  Index Deletion       : 0.00
% 3.39/1.52  Index Matching       : 0.00
% 3.39/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
