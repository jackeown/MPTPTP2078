%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:59 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 233 expanded)
%              Number of leaves         :   40 (  99 expanded)
%              Depth                    :   11
%              Number of atoms          :  188 ( 772 expanded)
%              Number of equality atoms :   58 ( 216 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_144,negated_conjecture,(
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

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_122,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_94,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_112,axiom,(
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

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A)
              & v2_funct_1(A) )
           => r1_tarski(k1_relat_1(A),k2_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_1)).

tff(f_44,axiom,(
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

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_133,plain,(
    ! [A_67,B_68,C_69] :
      ( k2_relset_1(A_67,B_68,C_69) = k2_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_140,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_133])).

tff(c_46,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_142,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_46])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_68,plain,(
    ! [B_50,A_51] :
      ( v1_relat_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_71,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_68])).

tff(c_77,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_71])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_97,plain,(
    ! [C_57,B_58,A_59] :
      ( v5_relat_1(C_57,B_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_59,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_104,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_97])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_448,plain,(
    ! [E_119,D_121,A_120,B_124,C_123,F_122] :
      ( k1_partfun1(A_120,B_124,C_123,D_121,E_119,F_122) = k5_relat_1(E_119,F_122)
      | ~ m1_subset_1(F_122,k1_zfmisc_1(k2_zfmisc_1(C_123,D_121)))
      | ~ v1_funct_1(F_122)
      | ~ m1_subset_1(E_119,k1_zfmisc_1(k2_zfmisc_1(A_120,B_124)))
      | ~ v1_funct_1(E_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_456,plain,(
    ! [A_120,B_124,E_119] :
      ( k1_partfun1(A_120,B_124,'#skF_2','#skF_3',E_119,'#skF_5') = k5_relat_1(E_119,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_119,k1_zfmisc_1(k2_zfmisc_1(A_120,B_124)))
      | ~ v1_funct_1(E_119) ) ),
    inference(resolution,[status(thm)],[c_54,c_448])).

tff(c_636,plain,(
    ! [A_128,B_129,E_130] :
      ( k1_partfun1(A_128,B_129,'#skF_2','#skF_3',E_130,'#skF_5') = k5_relat_1(E_130,'#skF_5')
      | ~ m1_subset_1(E_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129)))
      | ~ v1_funct_1(E_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_456])).

tff(c_654,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_636])).

tff(c_665,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_654])).

tff(c_52,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_677,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_665,c_52])).

tff(c_285,plain,(
    ! [F_105,B_102,A_104,C_106,D_101,E_103] :
      ( k4_relset_1(A_104,B_102,C_106,D_101,E_103,F_105) = k5_relat_1(E_103,F_105)
      | ~ m1_subset_1(F_105,k1_zfmisc_1(k2_zfmisc_1(C_106,D_101)))
      | ~ m1_subset_1(E_103,k1_zfmisc_1(k2_zfmisc_1(A_104,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_309,plain,(
    ! [A_110,B_111,E_112] :
      ( k4_relset_1(A_110,B_111,'#skF_2','#skF_3',E_112,'#skF_5') = k5_relat_1(E_112,'#skF_5')
      | ~ m1_subset_1(E_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(resolution,[status(thm)],[c_54,c_285])).

tff(c_316,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_309])).

tff(c_326,plain,(
    ! [B_115,A_116,F_117,D_118,E_114,C_113] :
      ( m1_subset_1(k4_relset_1(A_116,B_115,C_113,D_118,E_114,F_117),k1_zfmisc_1(k2_zfmisc_1(A_116,D_118)))
      | ~ m1_subset_1(F_117,k1_zfmisc_1(k2_zfmisc_1(C_113,D_118)))
      | ~ m1_subset_1(E_114,k1_zfmisc_1(k2_zfmisc_1(A_116,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_373,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_326])).

tff(c_398,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_54,c_373])).

tff(c_28,plain,(
    ! [A_28,B_29,C_30] :
      ( k2_relset_1(A_28,B_29,C_30) = k2_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_630,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_398,c_28])).

tff(c_733,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_630])).

tff(c_74,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_68])).

tff(c_80,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_74])).

tff(c_50,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_56,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_152,plain,(
    ! [A_71,B_72,C_73] :
      ( k1_relset_1(A_71,B_72,C_73) = k1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_160,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_152])).

tff(c_189,plain,(
    ! [B_84,A_85,C_86] :
      ( k1_xboole_0 = B_84
      | k1_relset_1(A_85,B_84,C_86) = A_85
      | ~ v1_funct_2(C_86,A_85,B_84)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_85,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_195,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_189])).

tff(c_201,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_160,c_195])).

tff(c_202,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_201])).

tff(c_251,plain,(
    ! [A_96,B_97] :
      ( r1_tarski(k1_relat_1(A_96),k2_relat_1(B_97))
      | ~ v2_funct_1(A_96)
      | k2_relat_1(k5_relat_1(B_97,A_96)) != k2_relat_1(A_96)
      | ~ v1_funct_1(B_97)
      | ~ v1_relat_1(B_97)
      | ~ v1_funct_1(A_96)
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_262,plain,(
    ! [B_97] :
      ( r1_tarski('#skF_2',k2_relat_1(B_97))
      | ~ v2_funct_1('#skF_5')
      | k2_relat_1(k5_relat_1(B_97,'#skF_5')) != k2_relat_1('#skF_5')
      | ~ v1_funct_1(B_97)
      | ~ v1_relat_1(B_97)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_251])).

tff(c_269,plain,(
    ! [B_98] :
      ( r1_tarski('#skF_2',k2_relat_1(B_98))
      | k2_relat_1(k5_relat_1(B_98,'#skF_5')) != k2_relat_1('#skF_5')
      | ~ v1_funct_1(B_98)
      | ~ v1_relat_1(B_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_58,c_50,c_262])).

tff(c_110,plain,(
    ! [B_60,A_61] :
      ( r1_tarski(k2_relat_1(B_60),A_61)
      | ~ v5_relat_1(B_60,A_61)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_113,plain,(
    ! [B_60,A_61] :
      ( k2_relat_1(B_60) = A_61
      | ~ r1_tarski(A_61,k2_relat_1(B_60))
      | ~ v5_relat_1(B_60,A_61)
      | ~ v1_relat_1(B_60) ) ),
    inference(resolution,[status(thm)],[c_110,c_2])).

tff(c_275,plain,(
    ! [B_98] :
      ( k2_relat_1(B_98) = '#skF_2'
      | ~ v5_relat_1(B_98,'#skF_2')
      | k2_relat_1(k5_relat_1(B_98,'#skF_5')) != k2_relat_1('#skF_5')
      | ~ v1_funct_1(B_98)
      | ~ v1_relat_1(B_98) ) ),
    inference(resolution,[status(thm)],[c_269,c_113])).

tff(c_740,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ v5_relat_1('#skF_4','#skF_2')
    | k2_relat_1('#skF_5') != '#skF_3'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_733,c_275])).

tff(c_784,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | k2_relat_1('#skF_5') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_64,c_104,c_740])).

tff(c_785,plain,(
    k2_relat_1('#skF_5') != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_784])).

tff(c_105,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_97])).

tff(c_16,plain,(
    ! [A_10,B_12] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_10,B_12)),k2_relat_1(B_12))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_169,plain,(
    ! [B_74,A_75] :
      ( k2_relat_1(B_74) = A_75
      | ~ r1_tarski(A_75,k2_relat_1(B_74))
      | ~ v5_relat_1(B_74,A_75)
      | ~ v1_relat_1(B_74) ) ),
    inference(resolution,[status(thm)],[c_110,c_2])).

tff(c_181,plain,(
    ! [A_10,B_12] :
      ( k2_relat_1(k5_relat_1(A_10,B_12)) = k2_relat_1(B_12)
      | ~ v5_relat_1(B_12,k2_relat_1(k5_relat_1(A_10,B_12)))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_10) ) ),
    inference(resolution,[status(thm)],[c_16,c_169])).

tff(c_755,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = k2_relat_1('#skF_5')
    | ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_733,c_181])).

tff(c_795,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_80,c_105,c_733,c_755])).

tff(c_814,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_785,c_795])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:38:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.62  
% 3.25/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.62  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.25/1.62  
% 3.25/1.62  %Foreground sorts:
% 3.25/1.62  
% 3.25/1.62  
% 3.25/1.62  %Background operators:
% 3.25/1.62  
% 3.25/1.62  
% 3.25/1.62  %Foreground operators:
% 3.25/1.62  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.25/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.25/1.62  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.25/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.25/1.62  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.25/1.62  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.25/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.25/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.25/1.62  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.25/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.25/1.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.25/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.25/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.25/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.25/1.62  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.25/1.62  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.25/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.25/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.25/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.25/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.25/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.62  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.25/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.25/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.25/1.62  
% 3.57/1.65  tff(f_144, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_funct_2)).
% 3.57/1.65  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.57/1.65  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.57/1.65  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.57/1.65  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.57/1.65  tff(f_122, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.57/1.65  tff(f_94, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 3.57/1.65  tff(f_80, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 3.57/1.65  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.57/1.65  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.57/1.65  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A)) & v2_funct_1(A)) => r1_tarski(k1_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_funct_1)).
% 3.57/1.65  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.57/1.65  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.57/1.65  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 3.57/1.65  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.57/1.65  tff(c_133, plain, (![A_67, B_68, C_69]: (k2_relset_1(A_67, B_68, C_69)=k2_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.57/1.65  tff(c_140, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_133])).
% 3.57/1.65  tff(c_46, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.57/1.65  tff(c_142, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_140, c_46])).
% 3.57/1.65  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.57/1.65  tff(c_68, plain, (![B_50, A_51]: (v1_relat_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.57/1.65  tff(c_71, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_68])).
% 3.57/1.65  tff(c_77, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_71])).
% 3.57/1.65  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.57/1.65  tff(c_97, plain, (![C_57, B_58, A_59]: (v5_relat_1(C_57, B_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_59, B_58))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.57/1.65  tff(c_104, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_97])).
% 3.57/1.65  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.57/1.65  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.57/1.65  tff(c_448, plain, (![E_119, D_121, A_120, B_124, C_123, F_122]: (k1_partfun1(A_120, B_124, C_123, D_121, E_119, F_122)=k5_relat_1(E_119, F_122) | ~m1_subset_1(F_122, k1_zfmisc_1(k2_zfmisc_1(C_123, D_121))) | ~v1_funct_1(F_122) | ~m1_subset_1(E_119, k1_zfmisc_1(k2_zfmisc_1(A_120, B_124))) | ~v1_funct_1(E_119))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.57/1.65  tff(c_456, plain, (![A_120, B_124, E_119]: (k1_partfun1(A_120, B_124, '#skF_2', '#skF_3', E_119, '#skF_5')=k5_relat_1(E_119, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_119, k1_zfmisc_1(k2_zfmisc_1(A_120, B_124))) | ~v1_funct_1(E_119))), inference(resolution, [status(thm)], [c_54, c_448])).
% 3.57/1.65  tff(c_636, plain, (![A_128, B_129, E_130]: (k1_partfun1(A_128, B_129, '#skF_2', '#skF_3', E_130, '#skF_5')=k5_relat_1(E_130, '#skF_5') | ~m1_subset_1(E_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))) | ~v1_funct_1(E_130))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_456])).
% 3.57/1.65  tff(c_654, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_636])).
% 3.57/1.65  tff(c_665, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_654])).
% 3.57/1.65  tff(c_52, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.57/1.65  tff(c_677, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_665, c_52])).
% 3.57/1.65  tff(c_285, plain, (![F_105, B_102, A_104, C_106, D_101, E_103]: (k4_relset_1(A_104, B_102, C_106, D_101, E_103, F_105)=k5_relat_1(E_103, F_105) | ~m1_subset_1(F_105, k1_zfmisc_1(k2_zfmisc_1(C_106, D_101))) | ~m1_subset_1(E_103, k1_zfmisc_1(k2_zfmisc_1(A_104, B_102))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.57/1.65  tff(c_309, plain, (![A_110, B_111, E_112]: (k4_relset_1(A_110, B_111, '#skF_2', '#skF_3', E_112, '#skF_5')=k5_relat_1(E_112, '#skF_5') | ~m1_subset_1(E_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(resolution, [status(thm)], [c_54, c_285])).
% 3.57/1.65  tff(c_316, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_60, c_309])).
% 3.57/1.65  tff(c_326, plain, (![B_115, A_116, F_117, D_118, E_114, C_113]: (m1_subset_1(k4_relset_1(A_116, B_115, C_113, D_118, E_114, F_117), k1_zfmisc_1(k2_zfmisc_1(A_116, D_118))) | ~m1_subset_1(F_117, k1_zfmisc_1(k2_zfmisc_1(C_113, D_118))) | ~m1_subset_1(E_114, k1_zfmisc_1(k2_zfmisc_1(A_116, B_115))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.57/1.65  tff(c_373, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_316, c_326])).
% 3.57/1.65  tff(c_398, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_54, c_373])).
% 3.57/1.65  tff(c_28, plain, (![A_28, B_29, C_30]: (k2_relset_1(A_28, B_29, C_30)=k2_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.57/1.65  tff(c_630, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_398, c_28])).
% 3.57/1.65  tff(c_733, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_677, c_630])).
% 3.57/1.65  tff(c_74, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_54, c_68])).
% 3.57/1.65  tff(c_80, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_74])).
% 3.57/1.65  tff(c_50, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.57/1.65  tff(c_48, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.57/1.65  tff(c_56, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.57/1.65  tff(c_152, plain, (![A_71, B_72, C_73]: (k1_relset_1(A_71, B_72, C_73)=k1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.57/1.65  tff(c_160, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_152])).
% 3.57/1.65  tff(c_189, plain, (![B_84, A_85, C_86]: (k1_xboole_0=B_84 | k1_relset_1(A_85, B_84, C_86)=A_85 | ~v1_funct_2(C_86, A_85, B_84) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_85, B_84))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.57/1.65  tff(c_195, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_189])).
% 3.57/1.65  tff(c_201, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_160, c_195])).
% 3.57/1.65  tff(c_202, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_48, c_201])).
% 3.57/1.65  tff(c_251, plain, (![A_96, B_97]: (r1_tarski(k1_relat_1(A_96), k2_relat_1(B_97)) | ~v2_funct_1(A_96) | k2_relat_1(k5_relat_1(B_97, A_96))!=k2_relat_1(A_96) | ~v1_funct_1(B_97) | ~v1_relat_1(B_97) | ~v1_funct_1(A_96) | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.57/1.65  tff(c_262, plain, (![B_97]: (r1_tarski('#skF_2', k2_relat_1(B_97)) | ~v2_funct_1('#skF_5') | k2_relat_1(k5_relat_1(B_97, '#skF_5'))!=k2_relat_1('#skF_5') | ~v1_funct_1(B_97) | ~v1_relat_1(B_97) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_202, c_251])).
% 3.57/1.65  tff(c_269, plain, (![B_98]: (r1_tarski('#skF_2', k2_relat_1(B_98)) | k2_relat_1(k5_relat_1(B_98, '#skF_5'))!=k2_relat_1('#skF_5') | ~v1_funct_1(B_98) | ~v1_relat_1(B_98))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_58, c_50, c_262])).
% 3.57/1.65  tff(c_110, plain, (![B_60, A_61]: (r1_tarski(k2_relat_1(B_60), A_61) | ~v5_relat_1(B_60, A_61) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.57/1.65  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.57/1.65  tff(c_113, plain, (![B_60, A_61]: (k2_relat_1(B_60)=A_61 | ~r1_tarski(A_61, k2_relat_1(B_60)) | ~v5_relat_1(B_60, A_61) | ~v1_relat_1(B_60))), inference(resolution, [status(thm)], [c_110, c_2])).
% 3.57/1.65  tff(c_275, plain, (![B_98]: (k2_relat_1(B_98)='#skF_2' | ~v5_relat_1(B_98, '#skF_2') | k2_relat_1(k5_relat_1(B_98, '#skF_5'))!=k2_relat_1('#skF_5') | ~v1_funct_1(B_98) | ~v1_relat_1(B_98))), inference(resolution, [status(thm)], [c_269, c_113])).
% 3.57/1.65  tff(c_740, plain, (k2_relat_1('#skF_4')='#skF_2' | ~v5_relat_1('#skF_4', '#skF_2') | k2_relat_1('#skF_5')!='#skF_3' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_733, c_275])).
% 3.57/1.65  tff(c_784, plain, (k2_relat_1('#skF_4')='#skF_2' | k2_relat_1('#skF_5')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_64, c_104, c_740])).
% 3.57/1.65  tff(c_785, plain, (k2_relat_1('#skF_5')!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_142, c_784])).
% 3.57/1.65  tff(c_105, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_97])).
% 3.57/1.65  tff(c_16, plain, (![A_10, B_12]: (r1_tarski(k2_relat_1(k5_relat_1(A_10, B_12)), k2_relat_1(B_12)) | ~v1_relat_1(B_12) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.57/1.65  tff(c_169, plain, (![B_74, A_75]: (k2_relat_1(B_74)=A_75 | ~r1_tarski(A_75, k2_relat_1(B_74)) | ~v5_relat_1(B_74, A_75) | ~v1_relat_1(B_74))), inference(resolution, [status(thm)], [c_110, c_2])).
% 3.57/1.65  tff(c_181, plain, (![A_10, B_12]: (k2_relat_1(k5_relat_1(A_10, B_12))=k2_relat_1(B_12) | ~v5_relat_1(B_12, k2_relat_1(k5_relat_1(A_10, B_12))) | ~v1_relat_1(B_12) | ~v1_relat_1(A_10))), inference(resolution, [status(thm)], [c_16, c_169])).
% 3.57/1.65  tff(c_755, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1('#skF_5') | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_733, c_181])).
% 3.57/1.65  tff(c_795, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_80, c_105, c_733, c_755])).
% 3.57/1.65  tff(c_814, plain, $false, inference(negUnitSimplification, [status(thm)], [c_785, c_795])).
% 3.57/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.65  
% 3.57/1.65  Inference rules
% 3.57/1.65  ----------------------
% 3.57/1.65  #Ref     : 0
% 3.57/1.65  #Sup     : 187
% 3.57/1.65  #Fact    : 0
% 3.57/1.65  #Define  : 0
% 3.57/1.65  #Split   : 4
% 3.57/1.65  #Chain   : 0
% 3.57/1.65  #Close   : 0
% 3.57/1.65  
% 3.57/1.65  Ordering : KBO
% 3.57/1.65  
% 3.57/1.65  Simplification rules
% 3.57/1.65  ----------------------
% 3.57/1.65  #Subsume      : 3
% 3.57/1.65  #Demod        : 70
% 3.57/1.65  #Tautology    : 56
% 3.57/1.65  #SimpNegUnit  : 9
% 3.57/1.65  #BackRed      : 5
% 3.57/1.65  
% 3.57/1.65  #Partial instantiations: 0
% 3.57/1.65  #Strategies tried      : 1
% 3.57/1.65  
% 3.57/1.65  Timing (in seconds)
% 3.57/1.65  ----------------------
% 3.57/1.65  Preprocessing        : 0.38
% 3.57/1.65  Parsing              : 0.20
% 3.57/1.65  CNF conversion       : 0.03
% 3.57/1.65  Main loop            : 0.45
% 3.57/1.65  Inferencing          : 0.16
% 3.57/1.65  Reduction            : 0.15
% 3.57/1.65  Demodulation         : 0.10
% 3.57/1.65  BG Simplification    : 0.03
% 3.57/1.65  Subsumption          : 0.08
% 3.57/1.65  Abstraction          : 0.02
% 3.57/1.65  MUC search           : 0.00
% 3.57/1.65  Cooper               : 0.00
% 3.57/1.65  Total                : 0.88
% 3.57/1.65  Index Insertion      : 0.00
% 3.57/1.65  Index Deletion       : 0.00
% 3.57/1.65  Index Matching       : 0.00
% 3.57/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
