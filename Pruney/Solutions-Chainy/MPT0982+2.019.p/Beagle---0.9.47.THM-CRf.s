%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:57 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 287 expanded)
%              Number of leaves         :   41 ( 120 expanded)
%              Depth                    :   17
%              Number of atoms          :  186 (1038 expanded)
%              Number of equality atoms :   57 ( 294 expanded)
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

tff(f_145,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_101,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_123,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_113,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_76,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_84,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_76])).

tff(c_103,plain,(
    ! [C_52,B_53,A_54] :
      ( v5_relat_1(C_52,B_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_54,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_111,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_103])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_166,plain,(
    ! [A_68,B_69,C_70] :
      ( k2_relset_1(A_68,B_69,C_70) = k2_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_174,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_166])).

tff(c_48,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_179,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_48])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_83,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_76])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_58,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_139,plain,(
    ! [A_62,B_63,C_64] :
      ( k1_relset_1(A_62,B_63,C_64) = k1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_146,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_139])).

tff(c_243,plain,(
    ! [B_91,A_92,C_93] :
      ( k1_xboole_0 = B_91
      | k1_relset_1(A_92,B_91,C_93) = A_92
      | ~ v1_funct_2(C_93,A_92,B_91)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_92,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_246,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_243])).

tff(c_252,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_146,c_246])).

tff(c_253,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_252])).

tff(c_110,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_103])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_390,plain,(
    ! [B_115,A_110,D_114,C_112,E_113,F_111] :
      ( k1_partfun1(A_110,B_115,C_112,D_114,E_113,F_111) = k5_relat_1(E_113,F_111)
      | ~ m1_subset_1(F_111,k1_zfmisc_1(k2_zfmisc_1(C_112,D_114)))
      | ~ v1_funct_1(F_111)
      | ~ m1_subset_1(E_113,k1_zfmisc_1(k2_zfmisc_1(A_110,B_115)))
      | ~ v1_funct_1(E_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_392,plain,(
    ! [A_110,B_115,E_113] :
      ( k1_partfun1(A_110,B_115,'#skF_2','#skF_3',E_113,'#skF_5') = k5_relat_1(E_113,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_113,k1_zfmisc_1(k2_zfmisc_1(A_110,B_115)))
      | ~ v1_funct_1(E_113) ) ),
    inference(resolution,[status(thm)],[c_56,c_390])).

tff(c_401,plain,(
    ! [A_116,B_117,E_118] :
      ( k1_partfun1(A_116,B_117,'#skF_2','#skF_3',E_118,'#skF_5') = k5_relat_1(E_118,'#skF_5')
      | ~ m1_subset_1(E_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117)))
      | ~ v1_funct_1(E_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_392])).

tff(c_407,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_401])).

tff(c_413,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_407])).

tff(c_54,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_420,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_54])).

tff(c_447,plain,(
    ! [A_124,D_122,E_126,C_127,B_123,F_125] :
      ( m1_subset_1(k1_partfun1(A_124,B_123,C_127,D_122,E_126,F_125),k1_zfmisc_1(k2_zfmisc_1(A_124,D_122)))
      | ~ m1_subset_1(F_125,k1_zfmisc_1(k2_zfmisc_1(C_127,D_122)))
      | ~ v1_funct_1(F_125)
      | ~ m1_subset_1(E_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_123)))
      | ~ v1_funct_1(E_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_502,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_447])).

tff(c_525,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_60,c_56,c_502])).

tff(c_28,plain,(
    ! [A_23,B_24,C_25] :
      ( k2_relset_1(A_23,B_24,C_25) = k2_relat_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_712,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_525,c_28])).

tff(c_750,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_712])).

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

tff(c_185,plain,(
    ! [B_73,A_74] :
      ( k2_relat_1(B_73) = A_74
      | ~ r1_tarski(A_74,k2_relat_1(B_73))
      | ~ v5_relat_1(B_73,A_74)
      | ~ v1_relat_1(B_73) ) ),
    inference(resolution,[status(thm)],[c_123,c_2])).

tff(c_197,plain,(
    ! [A_9,B_11] :
      ( k2_relat_1(k5_relat_1(A_9,B_11)) = k2_relat_1(B_11)
      | ~ v5_relat_1(B_11,k2_relat_1(k5_relat_1(A_9,B_11)))
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_9) ) ),
    inference(resolution,[status(thm)],[c_16,c_185])).

tff(c_771,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = k2_relat_1('#skF_5')
    | ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_750,c_197])).

tff(c_812,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_83,c_110,c_750,c_771])).

tff(c_14,plain,(
    ! [A_8] :
      ( k10_relat_1(A_8,k2_relat_1(A_8)) = k1_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_867,plain,
    ( k10_relat_1('#skF_5','#skF_3') = k1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_812,c_14])).

tff(c_891,plain,(
    k10_relat_1('#skF_5','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_253,c_867])).

tff(c_12,plain,(
    ! [B_7,A_5] :
      ( k9_relat_1(B_7,k2_relat_1(A_5)) = k2_relat_1(k5_relat_1(A_5,B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_52,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( k10_relat_1(B_13,k9_relat_1(B_13,A_12)) = A_12
      | ~ v2_funct_1(B_13)
      | ~ r1_tarski(A_12,k1_relat_1(B_13))
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_263,plain,(
    ! [A_12] :
      ( k10_relat_1('#skF_5',k9_relat_1('#skF_5',A_12)) = A_12
      | ~ v2_funct_1('#skF_5')
      | ~ r1_tarski(A_12,'#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_18])).

tff(c_299,plain,(
    ! [A_94] :
      ( k10_relat_1('#skF_5',k9_relat_1('#skF_5',A_94)) = A_94
      | ~ r1_tarski(A_94,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_60,c_52,c_263])).

tff(c_323,plain,(
    ! [A_5] :
      ( k10_relat_1('#skF_5',k2_relat_1(k5_relat_1(A_5,'#skF_5'))) = k2_relat_1(A_5)
      | ~ r1_tarski(k2_relat_1(A_5),'#skF_2')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_299])).

tff(c_337,plain,(
    ! [A_5] :
      ( k10_relat_1('#skF_5',k2_relat_1(k5_relat_1(A_5,'#skF_5'))) = k2_relat_1(A_5)
      | ~ r1_tarski(k2_relat_1(A_5),'#skF_2')
      | ~ v1_relat_1(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_323])).

tff(c_768,plain,
    ( k10_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_4')
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_750,c_337])).

tff(c_810,plain,
    ( k10_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_4')
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_768])).

tff(c_1179,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_891,c_810])).

tff(c_1180,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_1179])).

tff(c_1183,plain,
    ( ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_1180])).

tff(c_1187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_111,c_1183])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:59:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.35/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.60  
% 3.64/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.60  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.64/1.60  
% 3.64/1.60  %Foreground sorts:
% 3.64/1.60  
% 3.64/1.60  
% 3.64/1.60  %Background operators:
% 3.64/1.60  
% 3.64/1.60  
% 3.64/1.60  %Foreground operators:
% 3.64/1.60  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.64/1.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.64/1.60  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.64/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.64/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.64/1.60  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.64/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.64/1.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.64/1.60  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.64/1.60  tff('#skF_5', type, '#skF_5': $i).
% 3.64/1.60  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.64/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.64/1.60  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.64/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.64/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.64/1.60  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.64/1.60  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.64/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.64/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.64/1.60  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.64/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.64/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.64/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.64/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.64/1.60  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.64/1.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.64/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.64/1.60  
% 3.64/1.62  tff(f_145, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_funct_2)).
% 3.64/1.62  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.64/1.62  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.64/1.62  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.64/1.62  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.64/1.62  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.64/1.62  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.64/1.62  tff(f_123, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.64/1.62  tff(f_113, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.64/1.62  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 3.64/1.62  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.64/1.62  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 3.64/1.62  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 3.64/1.62  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 3.64/1.62  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.64/1.62  tff(c_76, plain, (![C_45, A_46, B_47]: (v1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.64/1.62  tff(c_84, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_76])).
% 3.64/1.62  tff(c_103, plain, (![C_52, B_53, A_54]: (v5_relat_1(C_52, B_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_54, B_53))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.64/1.62  tff(c_111, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_103])).
% 3.64/1.62  tff(c_10, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.64/1.62  tff(c_166, plain, (![A_68, B_69, C_70]: (k2_relset_1(A_68, B_69, C_70)=k2_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.64/1.62  tff(c_174, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_166])).
% 3.64/1.62  tff(c_48, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.64/1.62  tff(c_179, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_174, c_48])).
% 3.64/1.62  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.64/1.62  tff(c_83, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_76])).
% 3.64/1.62  tff(c_50, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.64/1.62  tff(c_58, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.64/1.62  tff(c_139, plain, (![A_62, B_63, C_64]: (k1_relset_1(A_62, B_63, C_64)=k1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.64/1.62  tff(c_146, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_139])).
% 3.64/1.62  tff(c_243, plain, (![B_91, A_92, C_93]: (k1_xboole_0=B_91 | k1_relset_1(A_92, B_91, C_93)=A_92 | ~v1_funct_2(C_93, A_92, B_91) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_92, B_91))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.64/1.62  tff(c_246, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_243])).
% 3.64/1.62  tff(c_252, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_146, c_246])).
% 3.64/1.62  tff(c_253, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_50, c_252])).
% 3.64/1.62  tff(c_110, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_103])).
% 3.64/1.62  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.64/1.62  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.64/1.62  tff(c_390, plain, (![B_115, A_110, D_114, C_112, E_113, F_111]: (k1_partfun1(A_110, B_115, C_112, D_114, E_113, F_111)=k5_relat_1(E_113, F_111) | ~m1_subset_1(F_111, k1_zfmisc_1(k2_zfmisc_1(C_112, D_114))) | ~v1_funct_1(F_111) | ~m1_subset_1(E_113, k1_zfmisc_1(k2_zfmisc_1(A_110, B_115))) | ~v1_funct_1(E_113))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.64/1.62  tff(c_392, plain, (![A_110, B_115, E_113]: (k1_partfun1(A_110, B_115, '#skF_2', '#skF_3', E_113, '#skF_5')=k5_relat_1(E_113, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_113, k1_zfmisc_1(k2_zfmisc_1(A_110, B_115))) | ~v1_funct_1(E_113))), inference(resolution, [status(thm)], [c_56, c_390])).
% 3.64/1.62  tff(c_401, plain, (![A_116, B_117, E_118]: (k1_partfun1(A_116, B_117, '#skF_2', '#skF_3', E_118, '#skF_5')=k5_relat_1(E_118, '#skF_5') | ~m1_subset_1(E_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))) | ~v1_funct_1(E_118))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_392])).
% 3.64/1.62  tff(c_407, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_401])).
% 3.64/1.62  tff(c_413, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_407])).
% 3.64/1.62  tff(c_54, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.64/1.62  tff(c_420, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_413, c_54])).
% 3.64/1.62  tff(c_447, plain, (![A_124, D_122, E_126, C_127, B_123, F_125]: (m1_subset_1(k1_partfun1(A_124, B_123, C_127, D_122, E_126, F_125), k1_zfmisc_1(k2_zfmisc_1(A_124, D_122))) | ~m1_subset_1(F_125, k1_zfmisc_1(k2_zfmisc_1(C_127, D_122))) | ~v1_funct_1(F_125) | ~m1_subset_1(E_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_123))) | ~v1_funct_1(E_126))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.64/1.62  tff(c_502, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_413, c_447])).
% 3.64/1.62  tff(c_525, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_60, c_56, c_502])).
% 3.64/1.62  tff(c_28, plain, (![A_23, B_24, C_25]: (k2_relset_1(A_23, B_24, C_25)=k2_relat_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.64/1.62  tff(c_712, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_525, c_28])).
% 3.64/1.62  tff(c_750, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_420, c_712])).
% 3.64/1.62  tff(c_16, plain, (![A_9, B_11]: (r1_tarski(k2_relat_1(k5_relat_1(A_9, B_11)), k2_relat_1(B_11)) | ~v1_relat_1(B_11) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.64/1.62  tff(c_123, plain, (![B_58, A_59]: (r1_tarski(k2_relat_1(B_58), A_59) | ~v5_relat_1(B_58, A_59) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.64/1.62  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.64/1.62  tff(c_185, plain, (![B_73, A_74]: (k2_relat_1(B_73)=A_74 | ~r1_tarski(A_74, k2_relat_1(B_73)) | ~v5_relat_1(B_73, A_74) | ~v1_relat_1(B_73))), inference(resolution, [status(thm)], [c_123, c_2])).
% 3.64/1.62  tff(c_197, plain, (![A_9, B_11]: (k2_relat_1(k5_relat_1(A_9, B_11))=k2_relat_1(B_11) | ~v5_relat_1(B_11, k2_relat_1(k5_relat_1(A_9, B_11))) | ~v1_relat_1(B_11) | ~v1_relat_1(A_9))), inference(resolution, [status(thm)], [c_16, c_185])).
% 3.64/1.62  tff(c_771, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1('#skF_5') | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_750, c_197])).
% 3.64/1.62  tff(c_812, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_83, c_110, c_750, c_771])).
% 3.64/1.62  tff(c_14, plain, (![A_8]: (k10_relat_1(A_8, k2_relat_1(A_8))=k1_relat_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.64/1.62  tff(c_867, plain, (k10_relat_1('#skF_5', '#skF_3')=k1_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_812, c_14])).
% 3.64/1.62  tff(c_891, plain, (k10_relat_1('#skF_5', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_83, c_253, c_867])).
% 3.64/1.62  tff(c_12, plain, (![B_7, A_5]: (k9_relat_1(B_7, k2_relat_1(A_5))=k2_relat_1(k5_relat_1(A_5, B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.64/1.62  tff(c_52, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.64/1.62  tff(c_18, plain, (![B_13, A_12]: (k10_relat_1(B_13, k9_relat_1(B_13, A_12))=A_12 | ~v2_funct_1(B_13) | ~r1_tarski(A_12, k1_relat_1(B_13)) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.64/1.62  tff(c_263, plain, (![A_12]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', A_12))=A_12 | ~v2_funct_1('#skF_5') | ~r1_tarski(A_12, '#skF_2') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_253, c_18])).
% 3.64/1.62  tff(c_299, plain, (![A_94]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', A_94))=A_94 | ~r1_tarski(A_94, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_60, c_52, c_263])).
% 3.64/1.62  tff(c_323, plain, (![A_5]: (k10_relat_1('#skF_5', k2_relat_1(k5_relat_1(A_5, '#skF_5')))=k2_relat_1(A_5) | ~r1_tarski(k2_relat_1(A_5), '#skF_2') | ~v1_relat_1('#skF_5') | ~v1_relat_1(A_5))), inference(superposition, [status(thm), theory('equality')], [c_12, c_299])).
% 3.64/1.62  tff(c_337, plain, (![A_5]: (k10_relat_1('#skF_5', k2_relat_1(k5_relat_1(A_5, '#skF_5')))=k2_relat_1(A_5) | ~r1_tarski(k2_relat_1(A_5), '#skF_2') | ~v1_relat_1(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_323])).
% 3.64/1.62  tff(c_768, plain, (k10_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_750, c_337])).
% 3.64/1.62  tff(c_810, plain, (k10_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_768])).
% 3.64/1.62  tff(c_1179, plain, (k2_relat_1('#skF_4')='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_891, c_810])).
% 3.64/1.62  tff(c_1180, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_179, c_1179])).
% 3.64/1.62  tff(c_1183, plain, (~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_1180])).
% 3.64/1.62  tff(c_1187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_111, c_1183])).
% 3.64/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.62  
% 3.64/1.62  Inference rules
% 3.64/1.62  ----------------------
% 3.64/1.62  #Ref     : 0
% 3.64/1.62  #Sup     : 241
% 3.64/1.62  #Fact    : 0
% 3.64/1.62  #Define  : 0
% 3.64/1.62  #Split   : 5
% 3.64/1.62  #Chain   : 0
% 3.64/1.62  #Close   : 0
% 3.64/1.62  
% 3.64/1.62  Ordering : KBO
% 3.64/1.62  
% 3.64/1.62  Simplification rules
% 3.64/1.62  ----------------------
% 3.64/1.62  #Subsume      : 5
% 3.64/1.62  #Demod        : 208
% 3.64/1.62  #Tautology    : 79
% 3.64/1.62  #SimpNegUnit  : 7
% 3.64/1.62  #BackRed      : 9
% 3.64/1.62  
% 3.64/1.62  #Partial instantiations: 0
% 3.64/1.62  #Strategies tried      : 1
% 3.64/1.62  
% 3.64/1.62  Timing (in seconds)
% 3.64/1.62  ----------------------
% 3.64/1.63  Preprocessing        : 0.37
% 3.64/1.63  Parsing              : 0.20
% 3.64/1.63  CNF conversion       : 0.02
% 3.64/1.63  Main loop            : 0.46
% 3.64/1.63  Inferencing          : 0.16
% 3.64/1.63  Reduction            : 0.16
% 3.64/1.63  Demodulation         : 0.11
% 3.64/1.63  BG Simplification    : 0.02
% 3.64/1.63  Subsumption          : 0.08
% 3.64/1.63  Abstraction          : 0.02
% 3.64/1.63  MUC search           : 0.00
% 3.64/1.63  Cooper               : 0.00
% 3.64/1.63  Total                : 0.87
% 3.64/1.63  Index Insertion      : 0.00
% 3.64/1.63  Index Deletion       : 0.00
% 3.64/1.63  Index Matching       : 0.00
% 3.64/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
