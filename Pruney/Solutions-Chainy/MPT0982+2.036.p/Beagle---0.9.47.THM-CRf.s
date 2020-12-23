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
% DateTime   : Thu Dec  3 10:12:00 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 189 expanded)
%              Number of leaves         :   43 (  86 expanded)
%              Depth                    :   14
%              Number of atoms          :  169 ( 594 expanded)
%              Number of equality atoms :   55 ( 178 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_143,negated_conjecture,(
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

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_99,axiom,(
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

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_121,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_111,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_66,plain,(
    ! [B_47,A_48] :
      ( v1_relat_1(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48))
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_72,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_66])).

tff(c_78,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_72])).

tff(c_89,plain,(
    ! [C_54,B_55,A_56] :
      ( v5_relat_1(C_54,B_55)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_56,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_97,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_89])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_117,plain,(
    ! [A_62,B_63,C_64] :
      ( k2_relset_1(A_62,B_63,C_64) = k2_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_125,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_117])).

tff(c_46,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_143,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_46])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_56,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_126,plain,(
    ! [A_65,B_66,C_67] :
      ( k1_relset_1(A_65,B_66,C_67) = k1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_133,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_126])).

tff(c_231,plain,(
    ! [B_91,A_92,C_93] :
      ( k1_xboole_0 = B_91
      | k1_relset_1(A_92,B_91,C_93) = A_92
      | ~ v1_funct_2(C_93,A_92,B_91)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_92,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_234,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_231])).

tff(c_240,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_133,c_234])).

tff(c_241,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_240])).

tff(c_153,plain,(
    ! [A_70,B_71,C_72,D_73] :
      ( k8_relset_1(A_70,B_71,C_72,D_73) = k10_relat_1(C_72,D_73)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_158,plain,(
    ! [D_73] : k8_relset_1('#skF_2','#skF_3','#skF_5',D_73) = k10_relat_1('#skF_5',D_73) ),
    inference(resolution,[status(thm)],[c_54,c_153])).

tff(c_197,plain,(
    ! [A_83,B_84,C_85] :
      ( k8_relset_1(A_83,B_84,C_85,B_84) = k1_relset_1(A_83,B_84,C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_199,plain,(
    k8_relset_1('#skF_2','#skF_3','#skF_5','#skF_3') = k1_relset_1('#skF_2','#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_197])).

tff(c_203,plain,(
    k10_relat_1('#skF_5','#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_133,c_199])).

tff(c_245,plain,(
    k10_relat_1('#skF_5','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_203])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_370,plain,(
    ! [B_111,F_113,C_114,A_110,D_115,E_112] :
      ( k1_partfun1(A_110,B_111,C_114,D_115,E_112,F_113) = k5_relat_1(E_112,F_113)
      | ~ m1_subset_1(F_113,k1_zfmisc_1(k2_zfmisc_1(C_114,D_115)))
      | ~ v1_funct_1(F_113)
      | ~ m1_subset_1(E_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111)))
      | ~ v1_funct_1(E_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_372,plain,(
    ! [A_110,B_111,E_112] :
      ( k1_partfun1(A_110,B_111,'#skF_2','#skF_3',E_112,'#skF_5') = k5_relat_1(E_112,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111)))
      | ~ v1_funct_1(E_112) ) ),
    inference(resolution,[status(thm)],[c_54,c_370])).

tff(c_381,plain,(
    ! [A_116,B_117,E_118] :
      ( k1_partfun1(A_116,B_117,'#skF_2','#skF_3',E_118,'#skF_5') = k5_relat_1(E_118,'#skF_5')
      | ~ m1_subset_1(E_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117)))
      | ~ v1_funct_1(E_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_372])).

tff(c_387,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_381])).

tff(c_393,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_387])).

tff(c_52,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_400,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_52])).

tff(c_427,plain,(
    ! [D_127,F_124,C_125,E_122,A_126,B_123] :
      ( m1_subset_1(k1_partfun1(A_126,B_123,C_125,D_127,E_122,F_124),k1_zfmisc_1(k2_zfmisc_1(A_126,D_127)))
      | ~ m1_subset_1(F_124,k1_zfmisc_1(k2_zfmisc_1(C_125,D_127)))
      | ~ v1_funct_1(F_124)
      | ~ m1_subset_1(E_122,k1_zfmisc_1(k2_zfmisc_1(A_126,B_123)))
      | ~ v1_funct_1(E_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_488,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_427])).

tff(c_516,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_58,c_54,c_488])).

tff(c_20,plain,(
    ! [A_19,B_20,C_21] :
      ( k2_relset_1(A_19,B_20,C_21) = k2_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_635,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_516,c_20])).

tff(c_675,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_635])).

tff(c_69,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_66])).

tff(c_75,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_69])).

tff(c_10,plain,(
    ! [B_10,A_8] :
      ( k9_relat_1(B_10,k2_relat_1(A_8)) = k2_relat_1(k5_relat_1(A_8,B_10))
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_50,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_12,plain,(
    ! [B_12,A_11] :
      ( k10_relat_1(B_12,k9_relat_1(B_12,A_11)) = A_11
      | ~ v2_funct_1(B_12)
      | ~ r1_tarski(A_11,k1_relat_1(B_12))
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_249,plain,(
    ! [A_11] :
      ( k10_relat_1('#skF_5',k9_relat_1('#skF_5',A_11)) = A_11
      | ~ v2_funct_1('#skF_5')
      | ~ r1_tarski(A_11,'#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_12])).

tff(c_282,plain,(
    ! [A_94] :
      ( k10_relat_1('#skF_5',k9_relat_1('#skF_5',A_94)) = A_94
      | ~ r1_tarski(A_94,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_58,c_50,c_249])).

tff(c_292,plain,(
    ! [A_8] :
      ( k10_relat_1('#skF_5',k2_relat_1(k5_relat_1(A_8,'#skF_5'))) = k2_relat_1(A_8)
      | ~ r1_tarski(k2_relat_1(A_8),'#skF_2')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_282])).

tff(c_296,plain,(
    ! [A_8] :
      ( k10_relat_1('#skF_5',k2_relat_1(k5_relat_1(A_8,'#skF_5'))) = k2_relat_1(A_8)
      | ~ r1_tarski(k2_relat_1(A_8),'#skF_2')
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_292])).

tff(c_687,plain,
    ( k10_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_4')
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_675,c_296])).

tff(c_702,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_245,c_687])).

tff(c_703,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_702])).

tff(c_737,plain,
    ( ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_703])).

tff(c_741,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_97,c_737])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:24:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.46  
% 2.95/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.46  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.95/1.46  
% 2.95/1.46  %Foreground sorts:
% 2.95/1.46  
% 2.95/1.46  
% 2.95/1.46  %Background operators:
% 2.95/1.46  
% 2.95/1.46  
% 2.95/1.46  %Foreground operators:
% 2.95/1.46  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.95/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.95/1.46  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.95/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.46  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.95/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.95/1.46  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.95/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.95/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.95/1.46  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.95/1.46  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.46  tff('#skF_5', type, '#skF_5': $i).
% 2.95/1.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.95/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.95/1.46  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.95/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.95/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.95/1.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.95/1.46  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.95/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.95/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.46  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.95/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.95/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.95/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.95/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.46  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.95/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.95/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.95/1.46  
% 3.30/1.48  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.30/1.48  tff(f_143, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_funct_2)).
% 3.30/1.48  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.30/1.48  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.30/1.48  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.30/1.48  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.30/1.48  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.30/1.48  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.30/1.48  tff(f_75, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.30/1.48  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 3.30/1.48  tff(f_121, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.30/1.48  tff(f_111, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.30/1.48  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 3.30/1.48  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 3.30/1.48  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.30/1.48  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.30/1.48  tff(c_66, plain, (![B_47, A_48]: (v1_relat_1(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.30/1.48  tff(c_72, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_66])).
% 3.30/1.48  tff(c_78, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_72])).
% 3.30/1.48  tff(c_89, plain, (![C_54, B_55, A_56]: (v5_relat_1(C_54, B_55) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_56, B_55))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.30/1.48  tff(c_97, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_89])).
% 3.30/1.48  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.30/1.48  tff(c_117, plain, (![A_62, B_63, C_64]: (k2_relset_1(A_62, B_63, C_64)=k2_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.30/1.48  tff(c_125, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_117])).
% 3.30/1.48  tff(c_46, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.30/1.48  tff(c_143, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_125, c_46])).
% 3.30/1.48  tff(c_48, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.30/1.48  tff(c_56, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.30/1.48  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.30/1.48  tff(c_126, plain, (![A_65, B_66, C_67]: (k1_relset_1(A_65, B_66, C_67)=k1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.30/1.48  tff(c_133, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_126])).
% 3.30/1.48  tff(c_231, plain, (![B_91, A_92, C_93]: (k1_xboole_0=B_91 | k1_relset_1(A_92, B_91, C_93)=A_92 | ~v1_funct_2(C_93, A_92, B_91) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_92, B_91))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.30/1.48  tff(c_234, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_231])).
% 3.30/1.48  tff(c_240, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_133, c_234])).
% 3.30/1.48  tff(c_241, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_48, c_240])).
% 3.30/1.48  tff(c_153, plain, (![A_70, B_71, C_72, D_73]: (k8_relset_1(A_70, B_71, C_72, D_73)=k10_relat_1(C_72, D_73) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.30/1.48  tff(c_158, plain, (![D_73]: (k8_relset_1('#skF_2', '#skF_3', '#skF_5', D_73)=k10_relat_1('#skF_5', D_73))), inference(resolution, [status(thm)], [c_54, c_153])).
% 3.30/1.48  tff(c_197, plain, (![A_83, B_84, C_85]: (k8_relset_1(A_83, B_84, C_85, B_84)=k1_relset_1(A_83, B_84, C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.30/1.48  tff(c_199, plain, (k8_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_3')=k1_relset_1('#skF_2', '#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_197])).
% 3.30/1.48  tff(c_203, plain, (k10_relat_1('#skF_5', '#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_133, c_199])).
% 3.30/1.48  tff(c_245, plain, (k10_relat_1('#skF_5', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_241, c_203])).
% 3.30/1.48  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.30/1.48  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.30/1.48  tff(c_370, plain, (![B_111, F_113, C_114, A_110, D_115, E_112]: (k1_partfun1(A_110, B_111, C_114, D_115, E_112, F_113)=k5_relat_1(E_112, F_113) | ~m1_subset_1(F_113, k1_zfmisc_1(k2_zfmisc_1(C_114, D_115))) | ~v1_funct_1(F_113) | ~m1_subset_1(E_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))) | ~v1_funct_1(E_112))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.30/1.48  tff(c_372, plain, (![A_110, B_111, E_112]: (k1_partfun1(A_110, B_111, '#skF_2', '#skF_3', E_112, '#skF_5')=k5_relat_1(E_112, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))) | ~v1_funct_1(E_112))), inference(resolution, [status(thm)], [c_54, c_370])).
% 3.30/1.48  tff(c_381, plain, (![A_116, B_117, E_118]: (k1_partfun1(A_116, B_117, '#skF_2', '#skF_3', E_118, '#skF_5')=k5_relat_1(E_118, '#skF_5') | ~m1_subset_1(E_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))) | ~v1_funct_1(E_118))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_372])).
% 3.30/1.48  tff(c_387, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_381])).
% 3.30/1.48  tff(c_393, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_387])).
% 3.30/1.48  tff(c_52, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.30/1.48  tff(c_400, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_393, c_52])).
% 3.30/1.48  tff(c_427, plain, (![D_127, F_124, C_125, E_122, A_126, B_123]: (m1_subset_1(k1_partfun1(A_126, B_123, C_125, D_127, E_122, F_124), k1_zfmisc_1(k2_zfmisc_1(A_126, D_127))) | ~m1_subset_1(F_124, k1_zfmisc_1(k2_zfmisc_1(C_125, D_127))) | ~v1_funct_1(F_124) | ~m1_subset_1(E_122, k1_zfmisc_1(k2_zfmisc_1(A_126, B_123))) | ~v1_funct_1(E_122))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.30/1.48  tff(c_488, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_393, c_427])).
% 3.30/1.48  tff(c_516, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_58, c_54, c_488])).
% 3.30/1.48  tff(c_20, plain, (![A_19, B_20, C_21]: (k2_relset_1(A_19, B_20, C_21)=k2_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.30/1.48  tff(c_635, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_516, c_20])).
% 3.30/1.48  tff(c_675, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_400, c_635])).
% 3.30/1.48  tff(c_69, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_54, c_66])).
% 3.30/1.48  tff(c_75, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_69])).
% 3.30/1.48  tff(c_10, plain, (![B_10, A_8]: (k9_relat_1(B_10, k2_relat_1(A_8))=k2_relat_1(k5_relat_1(A_8, B_10)) | ~v1_relat_1(B_10) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.30/1.48  tff(c_50, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.30/1.48  tff(c_12, plain, (![B_12, A_11]: (k10_relat_1(B_12, k9_relat_1(B_12, A_11))=A_11 | ~v2_funct_1(B_12) | ~r1_tarski(A_11, k1_relat_1(B_12)) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.30/1.48  tff(c_249, plain, (![A_11]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', A_11))=A_11 | ~v2_funct_1('#skF_5') | ~r1_tarski(A_11, '#skF_2') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_241, c_12])).
% 3.30/1.48  tff(c_282, plain, (![A_94]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', A_94))=A_94 | ~r1_tarski(A_94, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_58, c_50, c_249])).
% 3.30/1.48  tff(c_292, plain, (![A_8]: (k10_relat_1('#skF_5', k2_relat_1(k5_relat_1(A_8, '#skF_5')))=k2_relat_1(A_8) | ~r1_tarski(k2_relat_1(A_8), '#skF_2') | ~v1_relat_1('#skF_5') | ~v1_relat_1(A_8))), inference(superposition, [status(thm), theory('equality')], [c_10, c_282])).
% 3.30/1.48  tff(c_296, plain, (![A_8]: (k10_relat_1('#skF_5', k2_relat_1(k5_relat_1(A_8, '#skF_5')))=k2_relat_1(A_8) | ~r1_tarski(k2_relat_1(A_8), '#skF_2') | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_292])).
% 3.30/1.48  tff(c_687, plain, (k10_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_675, c_296])).
% 3.30/1.48  tff(c_702, plain, (k2_relat_1('#skF_4')='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_245, c_687])).
% 3.30/1.48  tff(c_703, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_143, c_702])).
% 3.30/1.48  tff(c_737, plain, (~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_703])).
% 3.30/1.48  tff(c_741, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_97, c_737])).
% 3.30/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.48  
% 3.30/1.48  Inference rules
% 3.30/1.48  ----------------------
% 3.30/1.48  #Ref     : 0
% 3.30/1.48  #Sup     : 160
% 3.30/1.48  #Fact    : 0
% 3.30/1.48  #Define  : 0
% 3.30/1.48  #Split   : 2
% 3.30/1.48  #Chain   : 0
% 3.30/1.48  #Close   : 0
% 3.30/1.48  
% 3.30/1.48  Ordering : KBO
% 3.30/1.48  
% 3.30/1.48  Simplification rules
% 3.30/1.48  ----------------------
% 3.30/1.48  #Subsume      : 0
% 3.30/1.48  #Demod        : 98
% 3.30/1.48  #Tautology    : 59
% 3.30/1.48  #SimpNegUnit  : 5
% 3.30/1.48  #BackRed      : 10
% 3.30/1.48  
% 3.30/1.48  #Partial instantiations: 0
% 3.30/1.48  #Strategies tried      : 1
% 3.30/1.48  
% 3.30/1.48  Timing (in seconds)
% 3.30/1.48  ----------------------
% 3.30/1.48  Preprocessing        : 0.36
% 3.30/1.48  Parsing              : 0.19
% 3.30/1.48  CNF conversion       : 0.02
% 3.30/1.48  Main loop            : 0.36
% 3.30/1.48  Inferencing          : 0.13
% 3.30/1.48  Reduction            : 0.12
% 3.30/1.48  Demodulation         : 0.08
% 3.30/1.48  BG Simplification    : 0.02
% 3.30/1.48  Subsumption          : 0.06
% 3.30/1.48  Abstraction          : 0.02
% 3.30/1.48  MUC search           : 0.00
% 3.30/1.48  Cooper               : 0.00
% 3.30/1.48  Total                : 0.75
% 3.30/1.48  Index Insertion      : 0.00
% 3.30/1.48  Index Deletion       : 0.00
% 3.30/1.48  Index Matching       : 0.00
% 3.30/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
