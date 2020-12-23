%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:00 EST 2020

% Result     : Theorem 3.79s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 180 expanded)
%              Number of leaves         :   45 (  83 expanded)
%              Depth                    :   13
%              Number of atoms          :  171 ( 532 expanded)
%              Number of equality atoms :   59 ( 164 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_111,axiom,(
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

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_93,axiom,(
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

tff(f_83,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

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
    ! [B_53,A_54] :
      ( v1_relat_1(B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54))
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_72,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_66])).

tff(c_78,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_72])).

tff(c_89,plain,(
    ! [C_60,B_61,A_62] :
      ( v5_relat_1(C_60,B_61)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_62,B_61))) ) ),
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

tff(c_134,plain,(
    ! [A_71,B_72,C_73] :
      ( k2_relset_1(A_71,B_72,C_73) = k2_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_142,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_134])).

tff(c_46,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_147,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_46])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_56,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_108,plain,(
    ! [A_66,B_67,C_68] :
      ( k1_relset_1(A_66,B_67,C_68) = k1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_115,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_108])).

tff(c_231,plain,(
    ! [B_97,A_98,C_99] :
      ( k1_xboole_0 = B_97
      | k1_relset_1(A_98,B_97,C_99) = A_98
      | ~ v1_funct_2(C_99,A_98,B_97)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_98,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_234,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_231])).

tff(c_240,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_115,c_234])).

tff(c_241,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_240])).

tff(c_153,plain,(
    ! [A_76,B_77,C_78,D_79] :
      ( k8_relset_1(A_76,B_77,C_78,D_79) = k10_relat_1(C_78,D_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_158,plain,(
    ! [D_79] : k8_relset_1('#skF_2','#skF_3','#skF_5',D_79) = k10_relat_1('#skF_5',D_79) ),
    inference(resolution,[status(thm)],[c_54,c_153])).

tff(c_197,plain,(
    ! [A_89,B_90,C_91] :
      ( k8_relset_1(A_89,B_90,C_91,B_90) = k1_relset_1(A_89,B_90,C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_199,plain,(
    k8_relset_1('#skF_2','#skF_3','#skF_5','#skF_3') = k1_relset_1('#skF_2','#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_197])).

tff(c_203,plain,(
    k10_relat_1('#skF_5','#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_115,c_199])).

tff(c_245,plain,(
    k10_relat_1('#skF_5','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_203])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_569,plain,(
    ! [B_126,C_125,A_127,E_122,F_123,D_124] :
      ( k1_partfun1(A_127,B_126,C_125,D_124,E_122,F_123) = k5_relat_1(E_122,F_123)
      | ~ m1_subset_1(F_123,k1_zfmisc_1(k2_zfmisc_1(C_125,D_124)))
      | ~ v1_funct_1(F_123)
      | ~ m1_subset_1(E_122,k1_zfmisc_1(k2_zfmisc_1(A_127,B_126)))
      | ~ v1_funct_1(E_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_577,plain,(
    ! [A_127,B_126,E_122] :
      ( k1_partfun1(A_127,B_126,'#skF_2','#skF_3',E_122,'#skF_5') = k5_relat_1(E_122,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_122,k1_zfmisc_1(k2_zfmisc_1(A_127,B_126)))
      | ~ v1_funct_1(E_122) ) ),
    inference(resolution,[status(thm)],[c_54,c_569])).

tff(c_754,plain,(
    ! [A_131,B_132,E_133] :
      ( k1_partfun1(A_131,B_132,'#skF_2','#skF_3',E_133,'#skF_5') = k5_relat_1(E_133,'#skF_5')
      | ~ m1_subset_1(E_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132)))
      | ~ v1_funct_1(E_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_577])).

tff(c_775,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_754])).

tff(c_786,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_775])).

tff(c_52,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_791,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_786,c_52])).

tff(c_298,plain,(
    ! [C_104,F_101,B_105,A_103,E_102,D_106] :
      ( k4_relset_1(A_103,B_105,C_104,D_106,E_102,F_101) = k5_relat_1(E_102,F_101)
      | ~ m1_subset_1(F_101,k1_zfmisc_1(k2_zfmisc_1(C_104,D_106)))
      | ~ m1_subset_1(E_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_331,plain,(
    ! [A_111,B_112,E_113] :
      ( k4_relset_1(A_111,B_112,'#skF_2','#skF_3',E_113,'#skF_5') = k5_relat_1(E_113,'#skF_5')
      | ~ m1_subset_1(E_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(resolution,[status(thm)],[c_54,c_298])).

tff(c_339,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_331])).

tff(c_374,plain,(
    ! [C_121,A_119,F_116,D_120,E_118,B_117] :
      ( m1_subset_1(k4_relset_1(A_119,B_117,C_121,D_120,E_118,F_116),k1_zfmisc_1(k2_zfmisc_1(A_119,D_120)))
      | ~ m1_subset_1(F_116,k1_zfmisc_1(k2_zfmisc_1(C_121,D_120)))
      | ~ m1_subset_1(E_118,k1_zfmisc_1(k2_zfmisc_1(A_119,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_424,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_374])).

tff(c_453,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_54,c_424])).

tff(c_22,plain,(
    ! [A_25,B_26,C_27] :
      ( k2_relset_1(A_25,B_26,C_27) = k2_relat_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_507,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_453,c_22])).

tff(c_796,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_791,c_507])).

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
    ! [A_100] :
      ( k10_relat_1('#skF_5',k9_relat_1('#skF_5',A_100)) = A_100
      | ~ r1_tarski(A_100,'#skF_2') ) ),
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

tff(c_808,plain,
    ( k10_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_4')
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_796,c_296])).

tff(c_823,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_245,c_808])).

tff(c_824,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_823])).

tff(c_834,plain,
    ( ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_824])).

tff(c_838,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_97,c_834])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:28:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.79/2.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/2.19  
% 3.79/2.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/2.19  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.79/2.19  
% 3.79/2.19  %Foreground sorts:
% 3.79/2.19  
% 3.79/2.19  
% 3.79/2.19  %Background operators:
% 3.79/2.19  
% 3.79/2.19  
% 3.79/2.19  %Foreground operators:
% 3.79/2.19  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.79/2.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.79/2.19  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.79/2.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.79/2.19  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.79/2.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.79/2.19  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.79/2.19  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.79/2.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.79/2.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.79/2.19  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.79/2.19  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.79/2.19  tff('#skF_5', type, '#skF_5': $i).
% 3.79/2.19  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.79/2.19  tff('#skF_2', type, '#skF_2': $i).
% 3.79/2.19  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.79/2.19  tff('#skF_3', type, '#skF_3': $i).
% 3.79/2.19  tff('#skF_1', type, '#skF_1': $i).
% 3.79/2.19  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.79/2.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.79/2.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.79/2.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.79/2.19  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.79/2.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.79/2.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.79/2.19  tff('#skF_4', type, '#skF_4': $i).
% 3.79/2.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.79/2.19  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.79/2.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.79/2.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.79/2.19  
% 3.79/2.21  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.79/2.21  tff(f_143, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_funct_2)).
% 3.79/2.21  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.79/2.21  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.79/2.21  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.79/2.21  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.79/2.21  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.79/2.21  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.79/2.21  tff(f_87, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.79/2.21  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 3.79/2.21  tff(f_121, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.79/2.21  tff(f_83, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 3.79/2.21  tff(f_69, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 3.79/2.21  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 3.79/2.21  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 3.79/2.21  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.79/2.21  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.79/2.21  tff(c_66, plain, (![B_53, A_54]: (v1_relat_1(B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.79/2.21  tff(c_72, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_66])).
% 3.79/2.21  tff(c_78, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_72])).
% 3.79/2.21  tff(c_89, plain, (![C_60, B_61, A_62]: (v5_relat_1(C_60, B_61) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_62, B_61))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.79/2.21  tff(c_97, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_89])).
% 3.79/2.21  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.79/2.21  tff(c_134, plain, (![A_71, B_72, C_73]: (k2_relset_1(A_71, B_72, C_73)=k2_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.79/2.21  tff(c_142, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_134])).
% 3.79/2.21  tff(c_46, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.79/2.21  tff(c_147, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_142, c_46])).
% 3.79/2.21  tff(c_48, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.79/2.21  tff(c_56, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.79/2.21  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.79/2.21  tff(c_108, plain, (![A_66, B_67, C_68]: (k1_relset_1(A_66, B_67, C_68)=k1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.79/2.21  tff(c_115, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_108])).
% 3.79/2.21  tff(c_231, plain, (![B_97, A_98, C_99]: (k1_xboole_0=B_97 | k1_relset_1(A_98, B_97, C_99)=A_98 | ~v1_funct_2(C_99, A_98, B_97) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_98, B_97))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.79/2.21  tff(c_234, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_231])).
% 3.79/2.21  tff(c_240, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_115, c_234])).
% 3.79/2.21  tff(c_241, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_48, c_240])).
% 3.79/2.21  tff(c_153, plain, (![A_76, B_77, C_78, D_79]: (k8_relset_1(A_76, B_77, C_78, D_79)=k10_relat_1(C_78, D_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.79/2.21  tff(c_158, plain, (![D_79]: (k8_relset_1('#skF_2', '#skF_3', '#skF_5', D_79)=k10_relat_1('#skF_5', D_79))), inference(resolution, [status(thm)], [c_54, c_153])).
% 3.79/2.21  tff(c_197, plain, (![A_89, B_90, C_91]: (k8_relset_1(A_89, B_90, C_91, B_90)=k1_relset_1(A_89, B_90, C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.79/2.21  tff(c_199, plain, (k8_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_3')=k1_relset_1('#skF_2', '#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_197])).
% 3.79/2.21  tff(c_203, plain, (k10_relat_1('#skF_5', '#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_115, c_199])).
% 3.79/2.21  tff(c_245, plain, (k10_relat_1('#skF_5', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_241, c_203])).
% 3.79/2.21  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.79/2.21  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.79/2.21  tff(c_569, plain, (![B_126, C_125, A_127, E_122, F_123, D_124]: (k1_partfun1(A_127, B_126, C_125, D_124, E_122, F_123)=k5_relat_1(E_122, F_123) | ~m1_subset_1(F_123, k1_zfmisc_1(k2_zfmisc_1(C_125, D_124))) | ~v1_funct_1(F_123) | ~m1_subset_1(E_122, k1_zfmisc_1(k2_zfmisc_1(A_127, B_126))) | ~v1_funct_1(E_122))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.79/2.21  tff(c_577, plain, (![A_127, B_126, E_122]: (k1_partfun1(A_127, B_126, '#skF_2', '#skF_3', E_122, '#skF_5')=k5_relat_1(E_122, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_122, k1_zfmisc_1(k2_zfmisc_1(A_127, B_126))) | ~v1_funct_1(E_122))), inference(resolution, [status(thm)], [c_54, c_569])).
% 3.79/2.21  tff(c_754, plain, (![A_131, B_132, E_133]: (k1_partfun1(A_131, B_132, '#skF_2', '#skF_3', E_133, '#skF_5')=k5_relat_1(E_133, '#skF_5') | ~m1_subset_1(E_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))) | ~v1_funct_1(E_133))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_577])).
% 3.79/2.21  tff(c_775, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_754])).
% 3.79/2.21  tff(c_786, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_775])).
% 3.79/2.21  tff(c_52, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.79/2.21  tff(c_791, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_786, c_52])).
% 3.79/2.21  tff(c_298, plain, (![C_104, F_101, B_105, A_103, E_102, D_106]: (k4_relset_1(A_103, B_105, C_104, D_106, E_102, F_101)=k5_relat_1(E_102, F_101) | ~m1_subset_1(F_101, k1_zfmisc_1(k2_zfmisc_1(C_104, D_106))) | ~m1_subset_1(E_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_105))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.79/2.21  tff(c_331, plain, (![A_111, B_112, E_113]: (k4_relset_1(A_111, B_112, '#skF_2', '#skF_3', E_113, '#skF_5')=k5_relat_1(E_113, '#skF_5') | ~m1_subset_1(E_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(resolution, [status(thm)], [c_54, c_298])).
% 3.79/2.21  tff(c_339, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_60, c_331])).
% 3.79/2.21  tff(c_374, plain, (![C_121, A_119, F_116, D_120, E_118, B_117]: (m1_subset_1(k4_relset_1(A_119, B_117, C_121, D_120, E_118, F_116), k1_zfmisc_1(k2_zfmisc_1(A_119, D_120))) | ~m1_subset_1(F_116, k1_zfmisc_1(k2_zfmisc_1(C_121, D_120))) | ~m1_subset_1(E_118, k1_zfmisc_1(k2_zfmisc_1(A_119, B_117))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.79/2.21  tff(c_424, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_339, c_374])).
% 3.79/2.21  tff(c_453, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_54, c_424])).
% 3.79/2.21  tff(c_22, plain, (![A_25, B_26, C_27]: (k2_relset_1(A_25, B_26, C_27)=k2_relat_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.79/2.21  tff(c_507, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_453, c_22])).
% 3.79/2.21  tff(c_796, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_791, c_507])).
% 3.79/2.21  tff(c_69, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_54, c_66])).
% 3.79/2.21  tff(c_75, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_69])).
% 3.79/2.21  tff(c_10, plain, (![B_10, A_8]: (k9_relat_1(B_10, k2_relat_1(A_8))=k2_relat_1(k5_relat_1(A_8, B_10)) | ~v1_relat_1(B_10) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.79/2.21  tff(c_50, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.79/2.21  tff(c_12, plain, (![B_12, A_11]: (k10_relat_1(B_12, k9_relat_1(B_12, A_11))=A_11 | ~v2_funct_1(B_12) | ~r1_tarski(A_11, k1_relat_1(B_12)) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.79/2.21  tff(c_249, plain, (![A_11]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', A_11))=A_11 | ~v2_funct_1('#skF_5') | ~r1_tarski(A_11, '#skF_2') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_241, c_12])).
% 3.79/2.21  tff(c_282, plain, (![A_100]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', A_100))=A_100 | ~r1_tarski(A_100, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_58, c_50, c_249])).
% 3.79/2.21  tff(c_292, plain, (![A_8]: (k10_relat_1('#skF_5', k2_relat_1(k5_relat_1(A_8, '#skF_5')))=k2_relat_1(A_8) | ~r1_tarski(k2_relat_1(A_8), '#skF_2') | ~v1_relat_1('#skF_5') | ~v1_relat_1(A_8))), inference(superposition, [status(thm), theory('equality')], [c_10, c_282])).
% 3.79/2.21  tff(c_296, plain, (![A_8]: (k10_relat_1('#skF_5', k2_relat_1(k5_relat_1(A_8, '#skF_5')))=k2_relat_1(A_8) | ~r1_tarski(k2_relat_1(A_8), '#skF_2') | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_292])).
% 3.79/2.21  tff(c_808, plain, (k10_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_796, c_296])).
% 3.79/2.21  tff(c_823, plain, (k2_relat_1('#skF_4')='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_245, c_808])).
% 3.79/2.21  tff(c_824, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_147, c_823])).
% 3.79/2.21  tff(c_834, plain, (~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_824])).
% 3.79/2.21  tff(c_838, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_97, c_834])).
% 3.79/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/2.21  
% 3.79/2.21  Inference rules
% 3.79/2.21  ----------------------
% 3.79/2.21  #Ref     : 0
% 3.79/2.21  #Sup     : 203
% 3.79/2.21  #Fact    : 0
% 3.79/2.21  #Define  : 0
% 3.79/2.21  #Split   : 4
% 3.79/2.21  #Chain   : 0
% 3.79/2.21  #Close   : 0
% 3.79/2.21  
% 3.79/2.21  Ordering : KBO
% 3.79/2.21  
% 3.79/2.21  Simplification rules
% 3.79/2.21  ----------------------
% 3.79/2.21  #Subsume      : 0
% 3.79/2.21  #Demod        : 65
% 3.79/2.21  #Tautology    : 75
% 3.79/2.21  #SimpNegUnit  : 9
% 3.79/2.21  #BackRed      : 7
% 3.79/2.21  
% 3.79/2.21  #Partial instantiations: 0
% 3.79/2.21  #Strategies tried      : 1
% 3.79/2.21  
% 3.79/2.21  Timing (in seconds)
% 3.79/2.21  ----------------------
% 3.79/2.22  Preprocessing        : 0.61
% 3.79/2.22  Parsing              : 0.32
% 3.79/2.22  CNF conversion       : 0.04
% 3.79/2.22  Main loop            : 0.67
% 3.79/2.22  Inferencing          : 0.24
% 3.79/2.22  Reduction            : 0.21
% 3.79/2.22  Demodulation         : 0.15
% 3.79/2.22  BG Simplification    : 0.04
% 3.79/2.22  Subsumption          : 0.11
% 3.79/2.22  Abstraction          : 0.03
% 3.79/2.22  MUC search           : 0.00
% 3.79/2.22  Cooper               : 0.00
% 3.79/2.22  Total                : 1.33
% 3.79/2.22  Index Insertion      : 0.00
% 3.79/2.22  Index Deletion       : 0.00
% 3.79/2.22  Index Matching       : 0.00
% 3.79/2.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
