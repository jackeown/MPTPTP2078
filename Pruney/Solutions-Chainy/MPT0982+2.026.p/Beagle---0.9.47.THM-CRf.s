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
% DateTime   : Thu Dec  3 10:11:58 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 168 expanded)
%              Number of leaves         :   44 (  79 expanded)
%              Depth                    :   13
%              Number of atoms          :  163 ( 508 expanded)
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

tff(f_138,negated_conjecture,(
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

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_106,axiom,(
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

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_116,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_78,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_67,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_74,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_67])).

tff(c_91,plain,(
    ! [C_59,B_60,A_61] :
      ( v5_relat_1(C_59,B_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_61,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_98,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_91])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_101,plain,(
    ! [A_63,B_64,C_65] :
      ( k2_relset_1(A_63,B_64,C_65) = k2_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_108,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_101])).

tff(c_44,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_110,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_44])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_54,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_115,plain,(
    ! [A_66,B_67,C_68] :
      ( k1_relset_1(A_66,B_67,C_68) = k1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_123,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_115])).

tff(c_212,plain,(
    ! [B_91,A_92,C_93] :
      ( k1_xboole_0 = B_91
      | k1_relset_1(A_92,B_91,C_93) = A_92
      | ~ v1_funct_2(C_93,A_92,B_91)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_92,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_218,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_212])).

tff(c_224,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_123,c_218])).

tff(c_225,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_224])).

tff(c_145,plain,(
    ! [A_71,B_72,C_73,D_74] :
      ( k8_relset_1(A_71,B_72,C_73,D_74) = k10_relat_1(C_73,D_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_151,plain,(
    ! [D_74] : k8_relset_1('#skF_2','#skF_3','#skF_5',D_74) = k10_relat_1('#skF_5',D_74) ),
    inference(resolution,[status(thm)],[c_52,c_145])).

tff(c_180,plain,(
    ! [A_82,B_83,C_84] :
      ( k8_relset_1(A_82,B_83,C_84,B_83) = k1_relset_1(A_82,B_83,C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_184,plain,(
    k8_relset_1('#skF_2','#skF_3','#skF_5','#skF_3') = k1_relset_1('#skF_2','#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_180])).

tff(c_188,plain,(
    k10_relat_1('#skF_5','#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_123,c_184])).

tff(c_226,plain,(
    k10_relat_1('#skF_5','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_188])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_451,plain,(
    ! [E_119,A_122,B_121,F_123,D_120,C_124] :
      ( k1_partfun1(A_122,B_121,C_124,D_120,E_119,F_123) = k5_relat_1(E_119,F_123)
      | ~ m1_subset_1(F_123,k1_zfmisc_1(k2_zfmisc_1(C_124,D_120)))
      | ~ v1_funct_1(F_123)
      | ~ m1_subset_1(E_119,k1_zfmisc_1(k2_zfmisc_1(A_122,B_121)))
      | ~ v1_funct_1(E_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_457,plain,(
    ! [A_122,B_121,E_119] :
      ( k1_partfun1(A_122,B_121,'#skF_2','#skF_3',E_119,'#skF_5') = k5_relat_1(E_119,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_119,k1_zfmisc_1(k2_zfmisc_1(A_122,B_121)))
      | ~ v1_funct_1(E_119) ) ),
    inference(resolution,[status(thm)],[c_52,c_451])).

tff(c_572,plain,(
    ! [A_125,B_126,E_127] :
      ( k1_partfun1(A_125,B_126,'#skF_2','#skF_3',E_127,'#skF_5') = k5_relat_1(E_127,'#skF_5')
      | ~ m1_subset_1(E_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126)))
      | ~ v1_funct_1(E_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_457])).

tff(c_584,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_572])).

tff(c_593,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_584])).

tff(c_50,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_745,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_50])).

tff(c_291,plain,(
    ! [C_102,B_99,F_101,A_100,D_98,E_103] :
      ( k4_relset_1(A_100,B_99,C_102,D_98,E_103,F_101) = k5_relat_1(E_103,F_101)
      | ~ m1_subset_1(F_101,k1_zfmisc_1(k2_zfmisc_1(C_102,D_98)))
      | ~ m1_subset_1(E_103,k1_zfmisc_1(k2_zfmisc_1(A_100,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_324,plain,(
    ! [A_108,B_109,E_110] :
      ( k4_relset_1(A_108,B_109,'#skF_2','#skF_3',E_110,'#skF_5') = k5_relat_1(E_110,'#skF_5')
      | ~ m1_subset_1(E_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(resolution,[status(thm)],[c_52,c_291])).

tff(c_331,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_324])).

tff(c_367,plain,(
    ! [D_115,A_118,C_116,E_113,F_114,B_117] :
      ( m1_subset_1(k4_relset_1(A_118,B_117,C_116,D_115,E_113,F_114),k1_zfmisc_1(k2_zfmisc_1(A_118,D_115)))
      | ~ m1_subset_1(F_114,k1_zfmisc_1(k2_zfmisc_1(C_116,D_115)))
      | ~ m1_subset_1(E_113,k1_zfmisc_1(k2_zfmisc_1(A_118,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_420,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_367])).

tff(c_446,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_420])).

tff(c_20,plain,(
    ! [A_23,B_24,C_25] :
      ( k2_relset_1(A_23,B_24,C_25) = k2_relat_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_652,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_446,c_20])).

tff(c_843,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_745,c_652])).

tff(c_75,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_67])).

tff(c_6,plain,(
    ! [B_5,A_3] :
      ( k9_relat_1(B_5,k2_relat_1(A_3)) = k2_relat_1(k5_relat_1(A_3,B_5))
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_48,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( k10_relat_1(B_7,k9_relat_1(B_7,A_6)) = A_6
      | ~ v2_funct_1(B_7)
      | ~ r1_tarski(A_6,k1_relat_1(B_7))
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_230,plain,(
    ! [A_6] :
      ( k10_relat_1('#skF_5',k9_relat_1('#skF_5',A_6)) = A_6
      | ~ v2_funct_1('#skF_5')
      | ~ r1_tarski(A_6,'#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_8])).

tff(c_275,plain,(
    ! [A_97] :
      ( k10_relat_1('#skF_5',k9_relat_1('#skF_5',A_97)) = A_97
      | ~ r1_tarski(A_97,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_56,c_48,c_230])).

tff(c_285,plain,(
    ! [A_3] :
      ( k10_relat_1('#skF_5',k2_relat_1(k5_relat_1(A_3,'#skF_5'))) = k2_relat_1(A_3)
      | ~ r1_tarski(k2_relat_1(A_3),'#skF_2')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1(A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_275])).

tff(c_289,plain,(
    ! [A_3] :
      ( k10_relat_1('#skF_5',k2_relat_1(k5_relat_1(A_3,'#skF_5'))) = k2_relat_1(A_3)
      | ~ r1_tarski(k2_relat_1(A_3),'#skF_2')
      | ~ v1_relat_1(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_285])).

tff(c_850,plain,
    ( k10_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_4')
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_843,c_289])).

tff(c_865,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_226,c_850])).

tff(c_866,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_865])).

tff(c_876,plain,
    ( ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_866])).

tff(c_880,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_98,c_876])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:14:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.49  
% 3.23/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.50  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.23/1.50  
% 3.23/1.50  %Foreground sorts:
% 3.23/1.50  
% 3.23/1.50  
% 3.23/1.50  %Background operators:
% 3.23/1.50  
% 3.23/1.50  
% 3.23/1.50  %Foreground operators:
% 3.23/1.50  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.23/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.23/1.50  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.23/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.50  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.23/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.23/1.50  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.23/1.50  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.23/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.23/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.23/1.50  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.23/1.50  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.23/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.23/1.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.23/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.23/1.50  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.23/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.23/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.23/1.50  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.23/1.50  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.23/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.23/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.50  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.23/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.23/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.23/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.23/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.50  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.23/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.23/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.23/1.50  
% 3.40/1.52  tff(f_138, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_funct_2)).
% 3.40/1.52  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.40/1.52  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.40/1.52  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.40/1.52  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.40/1.52  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.40/1.52  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.40/1.52  tff(f_82, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.40/1.52  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 3.40/1.52  tff(f_116, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.40/1.52  tff(f_78, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 3.40/1.52  tff(f_64, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 3.40/1.52  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 3.40/1.52  tff(f_48, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 3.40/1.52  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.40/1.52  tff(c_67, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.40/1.52  tff(c_74, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_67])).
% 3.40/1.52  tff(c_91, plain, (![C_59, B_60, A_61]: (v5_relat_1(C_59, B_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_61, B_60))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.40/1.52  tff(c_98, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_91])).
% 3.40/1.52  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.40/1.52  tff(c_101, plain, (![A_63, B_64, C_65]: (k2_relset_1(A_63, B_64, C_65)=k2_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.40/1.52  tff(c_108, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_101])).
% 3.40/1.52  tff(c_44, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.40/1.52  tff(c_110, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_44])).
% 3.40/1.52  tff(c_46, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.40/1.52  tff(c_54, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.40/1.52  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.40/1.52  tff(c_115, plain, (![A_66, B_67, C_68]: (k1_relset_1(A_66, B_67, C_68)=k1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.40/1.52  tff(c_123, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_115])).
% 3.40/1.52  tff(c_212, plain, (![B_91, A_92, C_93]: (k1_xboole_0=B_91 | k1_relset_1(A_92, B_91, C_93)=A_92 | ~v1_funct_2(C_93, A_92, B_91) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_92, B_91))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.40/1.52  tff(c_218, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_212])).
% 3.40/1.52  tff(c_224, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_123, c_218])).
% 3.40/1.52  tff(c_225, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_46, c_224])).
% 3.40/1.52  tff(c_145, plain, (![A_71, B_72, C_73, D_74]: (k8_relset_1(A_71, B_72, C_73, D_74)=k10_relat_1(C_73, D_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.40/1.52  tff(c_151, plain, (![D_74]: (k8_relset_1('#skF_2', '#skF_3', '#skF_5', D_74)=k10_relat_1('#skF_5', D_74))), inference(resolution, [status(thm)], [c_52, c_145])).
% 3.40/1.52  tff(c_180, plain, (![A_82, B_83, C_84]: (k8_relset_1(A_82, B_83, C_84, B_83)=k1_relset_1(A_82, B_83, C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.40/1.52  tff(c_184, plain, (k8_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_3')=k1_relset_1('#skF_2', '#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_52, c_180])).
% 3.40/1.52  tff(c_188, plain, (k10_relat_1('#skF_5', '#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_123, c_184])).
% 3.40/1.52  tff(c_226, plain, (k10_relat_1('#skF_5', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_225, c_188])).
% 3.40/1.52  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.40/1.52  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.40/1.52  tff(c_451, plain, (![E_119, A_122, B_121, F_123, D_120, C_124]: (k1_partfun1(A_122, B_121, C_124, D_120, E_119, F_123)=k5_relat_1(E_119, F_123) | ~m1_subset_1(F_123, k1_zfmisc_1(k2_zfmisc_1(C_124, D_120))) | ~v1_funct_1(F_123) | ~m1_subset_1(E_119, k1_zfmisc_1(k2_zfmisc_1(A_122, B_121))) | ~v1_funct_1(E_119))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.40/1.52  tff(c_457, plain, (![A_122, B_121, E_119]: (k1_partfun1(A_122, B_121, '#skF_2', '#skF_3', E_119, '#skF_5')=k5_relat_1(E_119, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_119, k1_zfmisc_1(k2_zfmisc_1(A_122, B_121))) | ~v1_funct_1(E_119))), inference(resolution, [status(thm)], [c_52, c_451])).
% 3.40/1.52  tff(c_572, plain, (![A_125, B_126, E_127]: (k1_partfun1(A_125, B_126, '#skF_2', '#skF_3', E_127, '#skF_5')=k5_relat_1(E_127, '#skF_5') | ~m1_subset_1(E_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))) | ~v1_funct_1(E_127))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_457])).
% 3.40/1.52  tff(c_584, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_572])).
% 3.40/1.52  tff(c_593, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_584])).
% 3.40/1.52  tff(c_50, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.40/1.52  tff(c_745, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_593, c_50])).
% 3.40/1.52  tff(c_291, plain, (![C_102, B_99, F_101, A_100, D_98, E_103]: (k4_relset_1(A_100, B_99, C_102, D_98, E_103, F_101)=k5_relat_1(E_103, F_101) | ~m1_subset_1(F_101, k1_zfmisc_1(k2_zfmisc_1(C_102, D_98))) | ~m1_subset_1(E_103, k1_zfmisc_1(k2_zfmisc_1(A_100, B_99))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.40/1.52  tff(c_324, plain, (![A_108, B_109, E_110]: (k4_relset_1(A_108, B_109, '#skF_2', '#skF_3', E_110, '#skF_5')=k5_relat_1(E_110, '#skF_5') | ~m1_subset_1(E_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(resolution, [status(thm)], [c_52, c_291])).
% 3.40/1.52  tff(c_331, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_58, c_324])).
% 3.40/1.52  tff(c_367, plain, (![D_115, A_118, C_116, E_113, F_114, B_117]: (m1_subset_1(k4_relset_1(A_118, B_117, C_116, D_115, E_113, F_114), k1_zfmisc_1(k2_zfmisc_1(A_118, D_115))) | ~m1_subset_1(F_114, k1_zfmisc_1(k2_zfmisc_1(C_116, D_115))) | ~m1_subset_1(E_113, k1_zfmisc_1(k2_zfmisc_1(A_118, B_117))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.40/1.52  tff(c_420, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_331, c_367])).
% 3.40/1.52  tff(c_446, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_52, c_420])).
% 3.40/1.52  tff(c_20, plain, (![A_23, B_24, C_25]: (k2_relset_1(A_23, B_24, C_25)=k2_relat_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.40/1.52  tff(c_652, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_446, c_20])).
% 3.40/1.52  tff(c_843, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_745, c_652])).
% 3.40/1.52  tff(c_75, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_67])).
% 3.40/1.52  tff(c_6, plain, (![B_5, A_3]: (k9_relat_1(B_5, k2_relat_1(A_3))=k2_relat_1(k5_relat_1(A_3, B_5)) | ~v1_relat_1(B_5) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.40/1.52  tff(c_48, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.40/1.52  tff(c_8, plain, (![B_7, A_6]: (k10_relat_1(B_7, k9_relat_1(B_7, A_6))=A_6 | ~v2_funct_1(B_7) | ~r1_tarski(A_6, k1_relat_1(B_7)) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.40/1.52  tff(c_230, plain, (![A_6]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', A_6))=A_6 | ~v2_funct_1('#skF_5') | ~r1_tarski(A_6, '#skF_2') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_225, c_8])).
% 3.40/1.52  tff(c_275, plain, (![A_97]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', A_97))=A_97 | ~r1_tarski(A_97, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_56, c_48, c_230])).
% 3.40/1.52  tff(c_285, plain, (![A_3]: (k10_relat_1('#skF_5', k2_relat_1(k5_relat_1(A_3, '#skF_5')))=k2_relat_1(A_3) | ~r1_tarski(k2_relat_1(A_3), '#skF_2') | ~v1_relat_1('#skF_5') | ~v1_relat_1(A_3))), inference(superposition, [status(thm), theory('equality')], [c_6, c_275])).
% 3.40/1.52  tff(c_289, plain, (![A_3]: (k10_relat_1('#skF_5', k2_relat_1(k5_relat_1(A_3, '#skF_5')))=k2_relat_1(A_3) | ~r1_tarski(k2_relat_1(A_3), '#skF_2') | ~v1_relat_1(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_285])).
% 3.40/1.52  tff(c_850, plain, (k10_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_843, c_289])).
% 3.40/1.52  tff(c_865, plain, (k2_relat_1('#skF_4')='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_226, c_850])).
% 3.40/1.52  tff(c_866, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_110, c_865])).
% 3.40/1.52  tff(c_876, plain, (~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4, c_866])).
% 3.40/1.52  tff(c_880, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_98, c_876])).
% 3.40/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/1.52  
% 3.40/1.52  Inference rules
% 3.40/1.52  ----------------------
% 3.40/1.52  #Ref     : 0
% 3.40/1.52  #Sup     : 223
% 3.40/1.52  #Fact    : 0
% 3.40/1.52  #Define  : 0
% 3.40/1.52  #Split   : 4
% 3.40/1.52  #Chain   : 0
% 3.40/1.52  #Close   : 0
% 3.40/1.52  
% 3.40/1.52  Ordering : KBO
% 3.40/1.52  
% 3.40/1.52  Simplification rules
% 3.40/1.52  ----------------------
% 3.40/1.52  #Subsume      : 0
% 3.40/1.52  #Demod        : 60
% 3.40/1.52  #Tautology    : 81
% 3.40/1.52  #SimpNegUnit  : 9
% 3.40/1.52  #BackRed      : 8
% 3.40/1.52  
% 3.40/1.52  #Partial instantiations: 0
% 3.40/1.52  #Strategies tried      : 1
% 3.40/1.52  
% 3.40/1.52  Timing (in seconds)
% 3.40/1.52  ----------------------
% 3.40/1.52  Preprocessing        : 0.34
% 3.40/1.52  Parsing              : 0.18
% 3.40/1.52  CNF conversion       : 0.02
% 3.40/1.52  Main loop            : 0.39
% 3.40/1.52  Inferencing          : 0.14
% 3.40/1.52  Reduction            : 0.13
% 3.40/1.52  Demodulation         : 0.09
% 3.40/1.52  BG Simplification    : 0.02
% 3.40/1.52  Subsumption          : 0.06
% 3.40/1.52  Abstraction          : 0.02
% 3.40/1.52  MUC search           : 0.00
% 3.40/1.52  Cooper               : 0.00
% 3.40/1.52  Total                : 0.77
% 3.40/1.52  Index Insertion      : 0.00
% 3.40/1.52  Index Deletion       : 0.00
% 3.40/1.52  Index Matching       : 0.00
% 3.40/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
