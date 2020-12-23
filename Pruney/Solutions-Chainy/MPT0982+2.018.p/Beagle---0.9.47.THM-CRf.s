%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:57 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 270 expanded)
%              Number of leaves         :   41 ( 115 expanded)
%              Depth                    :   17
%              Number of atoms          :  178 ( 971 expanded)
%              Number of equality atoms :   51 ( 261 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

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

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_77,axiom,(
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

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_166,plain,(
    ! [A_68,B_69,C_70] :
      ( k2_relset_1(A_68,B_69,C_70) = k2_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_174,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_166])).

tff(c_48,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_179,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_48])).

tff(c_76,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_84,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_76])).

tff(c_103,plain,(
    ! [C_52,B_53,A_54] :
      ( v5_relat_1(C_52,B_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_54,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_111,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_103])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_83,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_76])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_52,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_58,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_139,plain,(
    ! [A_62,B_63,C_64] :
      ( k1_relset_1(A_62,B_63,C_64) = k1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_146,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_139])).

tff(c_237,plain,(
    ! [B_90,A_91,C_92] :
      ( k1_xboole_0 = B_90
      | k1_relset_1(A_91,B_90,C_92) = A_91
      | ~ v1_funct_2(C_92,A_91,B_90)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_91,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_240,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_237])).

tff(c_246,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_146,c_240])).

tff(c_247,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_246])).

tff(c_110,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_103])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_307,plain,(
    ! [E_108,D_109,B_110,A_105,F_106,C_107] :
      ( k1_partfun1(A_105,B_110,C_107,D_109,E_108,F_106) = k5_relat_1(E_108,F_106)
      | ~ m1_subset_1(F_106,k1_zfmisc_1(k2_zfmisc_1(C_107,D_109)))
      | ~ v1_funct_1(F_106)
      | ~ m1_subset_1(E_108,k1_zfmisc_1(k2_zfmisc_1(A_105,B_110)))
      | ~ v1_funct_1(E_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_309,plain,(
    ! [A_105,B_110,E_108] :
      ( k1_partfun1(A_105,B_110,'#skF_2','#skF_3',E_108,'#skF_5') = k5_relat_1(E_108,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_108,k1_zfmisc_1(k2_zfmisc_1(A_105,B_110)))
      | ~ v1_funct_1(E_108) ) ),
    inference(resolution,[status(thm)],[c_56,c_307])).

tff(c_324,plain,(
    ! [A_113,B_114,E_115] :
      ( k1_partfun1(A_113,B_114,'#skF_2','#skF_3',E_115,'#skF_5') = k5_relat_1(E_115,'#skF_5')
      | ~ m1_subset_1(E_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114)))
      | ~ v1_funct_1(E_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_309])).

tff(c_330,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_324])).

tff(c_336,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_330])).

tff(c_54,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_343,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_54])).

tff(c_352,plain,(
    ! [C_121,D_116,A_118,F_119,E_120,B_117] :
      ( m1_subset_1(k1_partfun1(A_118,B_117,C_121,D_116,E_120,F_119),k1_zfmisc_1(k2_zfmisc_1(A_118,D_116)))
      | ~ m1_subset_1(F_119,k1_zfmisc_1(k2_zfmisc_1(C_121,D_116)))
      | ~ v1_funct_1(F_119)
      | ~ m1_subset_1(E_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_117)))
      | ~ v1_funct_1(E_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_401,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_352])).

tff(c_421,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_60,c_56,c_401])).

tff(c_28,plain,(
    ! [A_23,B_24,C_25] :
      ( k2_relset_1(A_23,B_24,C_25) = k2_relat_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_445,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_421,c_28])).

tff(c_480,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_445])).

tff(c_16,plain,(
    ! [A_9,B_11] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_9,B_11)),k2_relat_1(B_11))
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_123,plain,(
    ! [B_58,A_59] :
      ( r1_tarski(k2_relat_1(B_58),A_59)
      | ~ v5_relat_1(B_58,A_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_191,plain,(
    ! [B_73,A_74] :
      ( k2_relat_1(B_73) = A_74
      | ~ r1_tarski(A_74,k2_relat_1(B_73))
      | ~ v5_relat_1(B_73,A_74)
      | ~ v1_relat_1(B_73) ) ),
    inference(resolution,[status(thm)],[c_123,c_2])).

tff(c_208,plain,(
    ! [A_9,B_11] :
      ( k2_relat_1(k5_relat_1(A_9,B_11)) = k2_relat_1(B_11)
      | ~ v5_relat_1(B_11,k2_relat_1(k5_relat_1(A_9,B_11)))
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_9) ) ),
    inference(resolution,[status(thm)],[c_16,c_191])).

tff(c_496,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = k2_relat_1('#skF_5')
    | ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_208])).

tff(c_533,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_83,c_110,c_480,c_496])).

tff(c_14,plain,(
    ! [A_8] :
      ( k10_relat_1(A_8,k2_relat_1(A_8)) = k1_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_584,plain,
    ( k10_relat_1('#skF_5','#skF_3') = k1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_14])).

tff(c_606,plain,(
    k10_relat_1('#skF_5','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_247,c_584])).

tff(c_12,plain,(
    ! [B_7,A_5] :
      ( k9_relat_1(B_7,k2_relat_1(A_5)) = k2_relat_1(k5_relat_1(A_5,B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_184,plain,(
    ! [B_71,A_72] :
      ( r1_tarski(k10_relat_1(B_71,k9_relat_1(B_71,A_72)),A_72)
      | ~ v2_funct_1(B_71)
      | ~ v1_funct_1(B_71)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_825,plain,(
    ! [B_133,A_134] :
      ( r1_tarski(k10_relat_1(B_133,k2_relat_1(k5_relat_1(A_134,B_133))),k2_relat_1(A_134))
      | ~ v2_funct_1(B_133)
      | ~ v1_funct_1(B_133)
      | ~ v1_relat_1(B_133)
      | ~ v1_relat_1(B_133)
      | ~ v1_relat_1(A_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_184])).

tff(c_836,plain,
    ( r1_tarski(k10_relat_1('#skF_5','#skF_3'),k2_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_825])).

tff(c_845,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_83,c_83,c_60,c_52,c_606,c_836])).

tff(c_130,plain,(
    ! [B_58,A_59] :
      ( k2_relat_1(B_58) = A_59
      | ~ r1_tarski(A_59,k2_relat_1(B_58))
      | ~ v5_relat_1(B_58,A_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(resolution,[status(thm)],[c_123,c_2])).

tff(c_850,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_845,c_130])).

tff(c_855,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_111,c_850])).

tff(c_857,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_855])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:32:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.47  
% 3.17/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.47  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.17/1.47  
% 3.17/1.47  %Foreground sorts:
% 3.17/1.47  
% 3.17/1.47  
% 3.17/1.47  %Background operators:
% 3.17/1.47  
% 3.17/1.47  
% 3.17/1.47  %Foreground operators:
% 3.17/1.47  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.17/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.17/1.47  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.17/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.17/1.47  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.17/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.17/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.17/1.47  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.17/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.17/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.17/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.17/1.47  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.17/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.17/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.17/1.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.17/1.47  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.17/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.17/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.47  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.17/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.17/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.17/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.17/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.47  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.17/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.17/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.17/1.47  
% 3.17/1.49  tff(f_143, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_funct_2)).
% 3.17/1.49  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.17/1.49  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.17/1.49  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.17/1.49  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.17/1.49  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.17/1.49  tff(f_121, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.17/1.49  tff(f_111, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.17/1.49  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 3.17/1.49  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.17/1.49  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.17/1.49  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 3.17/1.49  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 3.17/1.49  tff(f_63, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 3.17/1.49  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.17/1.49  tff(c_166, plain, (![A_68, B_69, C_70]: (k2_relset_1(A_68, B_69, C_70)=k2_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.17/1.49  tff(c_174, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_166])).
% 3.17/1.49  tff(c_48, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.17/1.49  tff(c_179, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_174, c_48])).
% 3.17/1.49  tff(c_76, plain, (![C_45, A_46, B_47]: (v1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.17/1.49  tff(c_84, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_76])).
% 3.17/1.49  tff(c_103, plain, (![C_52, B_53, A_54]: (v5_relat_1(C_52, B_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_54, B_53))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.17/1.49  tff(c_111, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_103])).
% 3.17/1.49  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.17/1.49  tff(c_83, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_76])).
% 3.17/1.49  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.17/1.49  tff(c_52, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.17/1.49  tff(c_50, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.17/1.49  tff(c_58, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.17/1.49  tff(c_139, plain, (![A_62, B_63, C_64]: (k1_relset_1(A_62, B_63, C_64)=k1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.17/1.49  tff(c_146, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_139])).
% 3.17/1.49  tff(c_237, plain, (![B_90, A_91, C_92]: (k1_xboole_0=B_90 | k1_relset_1(A_91, B_90, C_92)=A_91 | ~v1_funct_2(C_92, A_91, B_90) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_91, B_90))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.17/1.49  tff(c_240, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_237])).
% 3.17/1.49  tff(c_246, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_146, c_240])).
% 3.17/1.49  tff(c_247, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_50, c_246])).
% 3.17/1.49  tff(c_110, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_103])).
% 3.17/1.49  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.17/1.49  tff(c_307, plain, (![E_108, D_109, B_110, A_105, F_106, C_107]: (k1_partfun1(A_105, B_110, C_107, D_109, E_108, F_106)=k5_relat_1(E_108, F_106) | ~m1_subset_1(F_106, k1_zfmisc_1(k2_zfmisc_1(C_107, D_109))) | ~v1_funct_1(F_106) | ~m1_subset_1(E_108, k1_zfmisc_1(k2_zfmisc_1(A_105, B_110))) | ~v1_funct_1(E_108))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.17/1.49  tff(c_309, plain, (![A_105, B_110, E_108]: (k1_partfun1(A_105, B_110, '#skF_2', '#skF_3', E_108, '#skF_5')=k5_relat_1(E_108, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_108, k1_zfmisc_1(k2_zfmisc_1(A_105, B_110))) | ~v1_funct_1(E_108))), inference(resolution, [status(thm)], [c_56, c_307])).
% 3.17/1.49  tff(c_324, plain, (![A_113, B_114, E_115]: (k1_partfun1(A_113, B_114, '#skF_2', '#skF_3', E_115, '#skF_5')=k5_relat_1(E_115, '#skF_5') | ~m1_subset_1(E_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))) | ~v1_funct_1(E_115))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_309])).
% 3.17/1.49  tff(c_330, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_324])).
% 3.17/1.49  tff(c_336, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_330])).
% 3.17/1.49  tff(c_54, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.17/1.49  tff(c_343, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_336, c_54])).
% 3.17/1.49  tff(c_352, plain, (![C_121, D_116, A_118, F_119, E_120, B_117]: (m1_subset_1(k1_partfun1(A_118, B_117, C_121, D_116, E_120, F_119), k1_zfmisc_1(k2_zfmisc_1(A_118, D_116))) | ~m1_subset_1(F_119, k1_zfmisc_1(k2_zfmisc_1(C_121, D_116))) | ~v1_funct_1(F_119) | ~m1_subset_1(E_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_117))) | ~v1_funct_1(E_120))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.17/1.49  tff(c_401, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_336, c_352])).
% 3.17/1.49  tff(c_421, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_60, c_56, c_401])).
% 3.17/1.49  tff(c_28, plain, (![A_23, B_24, C_25]: (k2_relset_1(A_23, B_24, C_25)=k2_relat_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.17/1.49  tff(c_445, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_421, c_28])).
% 3.17/1.49  tff(c_480, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_343, c_445])).
% 3.17/1.49  tff(c_16, plain, (![A_9, B_11]: (r1_tarski(k2_relat_1(k5_relat_1(A_9, B_11)), k2_relat_1(B_11)) | ~v1_relat_1(B_11) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.17/1.49  tff(c_123, plain, (![B_58, A_59]: (r1_tarski(k2_relat_1(B_58), A_59) | ~v5_relat_1(B_58, A_59) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.17/1.49  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.17/1.49  tff(c_191, plain, (![B_73, A_74]: (k2_relat_1(B_73)=A_74 | ~r1_tarski(A_74, k2_relat_1(B_73)) | ~v5_relat_1(B_73, A_74) | ~v1_relat_1(B_73))), inference(resolution, [status(thm)], [c_123, c_2])).
% 3.17/1.49  tff(c_208, plain, (![A_9, B_11]: (k2_relat_1(k5_relat_1(A_9, B_11))=k2_relat_1(B_11) | ~v5_relat_1(B_11, k2_relat_1(k5_relat_1(A_9, B_11))) | ~v1_relat_1(B_11) | ~v1_relat_1(A_9))), inference(resolution, [status(thm)], [c_16, c_191])).
% 3.17/1.49  tff(c_496, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1('#skF_5') | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_480, c_208])).
% 3.17/1.49  tff(c_533, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_83, c_110, c_480, c_496])).
% 3.17/1.49  tff(c_14, plain, (![A_8]: (k10_relat_1(A_8, k2_relat_1(A_8))=k1_relat_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.17/1.49  tff(c_584, plain, (k10_relat_1('#skF_5', '#skF_3')=k1_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_533, c_14])).
% 3.17/1.49  tff(c_606, plain, (k10_relat_1('#skF_5', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_83, c_247, c_584])).
% 3.17/1.49  tff(c_12, plain, (![B_7, A_5]: (k9_relat_1(B_7, k2_relat_1(A_5))=k2_relat_1(k5_relat_1(A_5, B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.17/1.49  tff(c_184, plain, (![B_71, A_72]: (r1_tarski(k10_relat_1(B_71, k9_relat_1(B_71, A_72)), A_72) | ~v2_funct_1(B_71) | ~v1_funct_1(B_71) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.17/1.49  tff(c_825, plain, (![B_133, A_134]: (r1_tarski(k10_relat_1(B_133, k2_relat_1(k5_relat_1(A_134, B_133))), k2_relat_1(A_134)) | ~v2_funct_1(B_133) | ~v1_funct_1(B_133) | ~v1_relat_1(B_133) | ~v1_relat_1(B_133) | ~v1_relat_1(A_134))), inference(superposition, [status(thm), theory('equality')], [c_12, c_184])).
% 3.17/1.49  tff(c_836, plain, (r1_tarski(k10_relat_1('#skF_5', '#skF_3'), k2_relat_1('#skF_4')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_480, c_825])).
% 3.17/1.49  tff(c_845, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_83, c_83, c_60, c_52, c_606, c_836])).
% 3.17/1.49  tff(c_130, plain, (![B_58, A_59]: (k2_relat_1(B_58)=A_59 | ~r1_tarski(A_59, k2_relat_1(B_58)) | ~v5_relat_1(B_58, A_59) | ~v1_relat_1(B_58))), inference(resolution, [status(thm)], [c_123, c_2])).
% 3.17/1.49  tff(c_850, plain, (k2_relat_1('#skF_4')='#skF_2' | ~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_845, c_130])).
% 3.17/1.49  tff(c_855, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_111, c_850])).
% 3.17/1.49  tff(c_857, plain, $false, inference(negUnitSimplification, [status(thm)], [c_179, c_855])).
% 3.17/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.49  
% 3.17/1.49  Inference rules
% 3.17/1.49  ----------------------
% 3.17/1.49  #Ref     : 0
% 3.17/1.49  #Sup     : 172
% 3.17/1.49  #Fact    : 0
% 3.17/1.49  #Define  : 0
% 3.17/1.49  #Split   : 3
% 3.17/1.49  #Chain   : 0
% 3.17/1.49  #Close   : 0
% 3.17/1.49  
% 3.17/1.49  Ordering : KBO
% 3.17/1.49  
% 3.17/1.49  Simplification rules
% 3.17/1.49  ----------------------
% 3.17/1.49  #Subsume      : 5
% 3.17/1.49  #Demod        : 133
% 3.17/1.49  #Tautology    : 59
% 3.17/1.49  #SimpNegUnit  : 8
% 3.17/1.49  #BackRed      : 7
% 3.17/1.49  
% 3.17/1.49  #Partial instantiations: 0
% 3.17/1.49  #Strategies tried      : 1
% 3.17/1.49  
% 3.17/1.49  Timing (in seconds)
% 3.17/1.49  ----------------------
% 3.17/1.49  Preprocessing        : 0.34
% 3.17/1.49  Parsing              : 0.18
% 3.17/1.49  CNF conversion       : 0.02
% 3.17/1.49  Main loop            : 0.37
% 3.17/1.49  Inferencing          : 0.14
% 3.17/1.49  Reduction            : 0.12
% 3.17/1.49  Demodulation         : 0.08
% 3.17/1.49  BG Simplification    : 0.02
% 3.17/1.49  Subsumption          : 0.07
% 3.17/1.49  Abstraction          : 0.02
% 3.17/1.49  MUC search           : 0.00
% 3.17/1.49  Cooper               : 0.00
% 3.17/1.49  Total                : 0.76
% 3.17/1.49  Index Insertion      : 0.00
% 3.17/1.49  Index Deletion       : 0.00
% 3.17/1.49  Index Matching       : 0.00
% 3.17/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
