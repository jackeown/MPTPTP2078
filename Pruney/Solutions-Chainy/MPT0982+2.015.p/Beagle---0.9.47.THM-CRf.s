%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:57 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 337 expanded)
%              Number of leaves         :   41 ( 138 expanded)
%              Depth                    :   16
%              Number of atoms          :  203 (1237 expanded)
%              Number of equality atoms :   63 ( 369 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_funct_2)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_75,axiom,(
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

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_123,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_113,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

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

tff(c_156,plain,(
    ! [A_65,B_66,C_67] :
      ( k2_relset_1(A_65,B_66,C_67) = k2_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_164,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_156])).

tff(c_48,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_169,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_48])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_83,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_76])).

tff(c_110,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_103])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_425,plain,(
    ! [A_109,B_114,C_111,F_110,D_113,E_112] :
      ( k1_partfun1(A_109,B_114,C_111,D_113,E_112,F_110) = k5_relat_1(E_112,F_110)
      | ~ m1_subset_1(F_110,k1_zfmisc_1(k2_zfmisc_1(C_111,D_113)))
      | ~ v1_funct_1(F_110)
      | ~ m1_subset_1(E_112,k1_zfmisc_1(k2_zfmisc_1(A_109,B_114)))
      | ~ v1_funct_1(E_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_427,plain,(
    ! [A_109,B_114,E_112] :
      ( k1_partfun1(A_109,B_114,'#skF_2','#skF_3',E_112,'#skF_5') = k5_relat_1(E_112,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_112,k1_zfmisc_1(k2_zfmisc_1(A_109,B_114)))
      | ~ v1_funct_1(E_112) ) ),
    inference(resolution,[status(thm)],[c_56,c_425])).

tff(c_465,plain,(
    ! [A_120,B_121,E_122] :
      ( k1_partfun1(A_120,B_121,'#skF_2','#skF_3',E_122,'#skF_5') = k5_relat_1(E_122,'#skF_5')
      | ~ m1_subset_1(E_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121)))
      | ~ v1_funct_1(E_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_427])).

tff(c_471,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_465])).

tff(c_477,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_471])).

tff(c_54,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_782,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_54])).

tff(c_42,plain,(
    ! [E_33,A_29,F_34,D_32,C_31,B_30] :
      ( m1_subset_1(k1_partfun1(A_29,B_30,C_31,D_32,E_33,F_34),k1_zfmisc_1(k2_zfmisc_1(A_29,D_32)))
      | ~ m1_subset_1(F_34,k1_zfmisc_1(k2_zfmisc_1(C_31,D_32)))
      | ~ v1_funct_1(F_34)
      | ~ m1_subset_1(E_33,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ v1_funct_1(E_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_786,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_477,c_42])).

tff(c_790,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_60,c_56,c_786])).

tff(c_28,plain,(
    ! [A_23,B_24,C_25] :
      ( k2_relset_1(A_23,B_24,C_25) = k2_relat_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_851,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_790,c_28])).

tff(c_892,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_782,c_851])).

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

tff(c_913,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = k2_relat_1('#skF_5')
    | ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_892,c_197])).

tff(c_954,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_83,c_110,c_892,c_913])).

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

tff(c_255,plain,(
    ! [B_92,A_93,C_94] :
      ( k1_xboole_0 = B_92
      | k1_relset_1(A_93,B_92,C_94) = A_93
      | ~ v1_funct_2(C_94,A_93,B_92)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_258,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_255])).

tff(c_264,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_146,c_258])).

tff(c_265,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_264])).

tff(c_12,plain,(
    ! [A_5] :
      ( k9_relat_1(A_5,k1_relat_1(A_5)) = k2_relat_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_278,plain,
    ( k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_12])).

tff(c_286,plain,(
    k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_278])).

tff(c_52,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_204,plain,(
    ! [B_81,A_82] :
      ( k10_relat_1(B_81,k9_relat_1(B_81,A_82)) = A_82
      | ~ v2_funct_1(B_81)
      | ~ r1_tarski(A_82,k1_relat_1(B_81))
      | ~ v1_funct_1(B_81)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_212,plain,(
    ! [B_81] :
      ( k10_relat_1(B_81,k9_relat_1(B_81,k1_relat_1(B_81))) = k1_relat_1(B_81)
      | ~ v2_funct_1(B_81)
      | ~ v1_funct_1(B_81)
      | ~ v1_relat_1(B_81) ) ),
    inference(resolution,[status(thm)],[c_6,c_204])).

tff(c_273,plain,
    ( k10_relat_1('#skF_5',k9_relat_1('#skF_5','#skF_2')) = k1_relat_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_212])).

tff(c_282,plain,(
    k10_relat_1('#skF_5',k9_relat_1('#skF_5','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_60,c_52,c_265,c_273])).

tff(c_324,plain,(
    k10_relat_1('#skF_5',k2_relat_1('#skF_5')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_282])).

tff(c_976,plain,(
    k10_relat_1('#skF_5','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_954,c_324])).

tff(c_14,plain,(
    ! [B_8,A_6] :
      ( k9_relat_1(B_8,k2_relat_1(A_6)) = k2_relat_1(k5_relat_1(A_6,B_8))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( k10_relat_1(B_13,k9_relat_1(B_13,A_12)) = A_12
      | ~ v2_funct_1(B_13)
      | ~ r1_tarski(A_12,k1_relat_1(B_13))
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_275,plain,(
    ! [A_12] :
      ( k10_relat_1('#skF_5',k9_relat_1('#skF_5',A_12)) = A_12
      | ~ v2_funct_1('#skF_5')
      | ~ r1_tarski(A_12,'#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_18])).

tff(c_352,plain,(
    ! [A_101] :
      ( k10_relat_1('#skF_5',k9_relat_1('#skF_5',A_101)) = A_101
      | ~ r1_tarski(A_101,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_60,c_52,c_275])).

tff(c_373,plain,(
    ! [A_6] :
      ( k10_relat_1('#skF_5',k2_relat_1(k5_relat_1(A_6,'#skF_5'))) = k2_relat_1(A_6)
      | ~ r1_tarski(k2_relat_1(A_6),'#skF_2')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_352])).

tff(c_387,plain,(
    ! [A_6] :
      ( k10_relat_1('#skF_5',k2_relat_1(k5_relat_1(A_6,'#skF_5'))) = k2_relat_1(A_6)
      | ~ r1_tarski(k2_relat_1(A_6),'#skF_2')
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_373])).

tff(c_910,plain,
    ( k10_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_4')
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_892,c_387])).

tff(c_952,plain,
    ( k10_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_4')
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_910])).

tff(c_1229,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_976,c_952])).

tff(c_1230,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_1229])).

tff(c_1233,plain,
    ( ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_1230])).

tff(c_1237,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_111,c_1233])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:57:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.56  
% 3.53/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.56  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.53/1.56  
% 3.53/1.56  %Foreground sorts:
% 3.53/1.56  
% 3.53/1.56  
% 3.53/1.56  %Background operators:
% 3.53/1.56  
% 3.53/1.56  
% 3.53/1.56  %Foreground operators:
% 3.53/1.56  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.53/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.53/1.56  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.53/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.53/1.56  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.53/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.53/1.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.53/1.56  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.53/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.53/1.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.53/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.53/1.56  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.53/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.53/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.53/1.56  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.53/1.56  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.53/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.53/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.56  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.53/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.53/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.53/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.53/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.56  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.53/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.53/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.53/1.56  
% 3.53/1.58  tff(f_145, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_funct_2)).
% 3.53/1.58  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.53/1.58  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.53/1.58  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.53/1.58  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.53/1.58  tff(f_123, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.53/1.58  tff(f_113, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.53/1.58  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 3.53/1.58  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.53/1.58  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.53/1.58  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.53/1.58  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 3.53/1.58  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 3.53/1.58  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 3.53/1.58  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.53/1.58  tff(c_76, plain, (![C_45, A_46, B_47]: (v1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.53/1.58  tff(c_84, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_76])).
% 3.53/1.58  tff(c_103, plain, (![C_52, B_53, A_54]: (v5_relat_1(C_52, B_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_54, B_53))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.53/1.58  tff(c_111, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_103])).
% 3.53/1.58  tff(c_10, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.53/1.58  tff(c_156, plain, (![A_65, B_66, C_67]: (k2_relset_1(A_65, B_66, C_67)=k2_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.53/1.58  tff(c_164, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_156])).
% 3.53/1.58  tff(c_48, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.53/1.58  tff(c_169, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_164, c_48])).
% 3.53/1.58  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.53/1.58  tff(c_83, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_76])).
% 3.53/1.58  tff(c_110, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_103])).
% 3.53/1.58  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.53/1.58  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.53/1.58  tff(c_425, plain, (![A_109, B_114, C_111, F_110, D_113, E_112]: (k1_partfun1(A_109, B_114, C_111, D_113, E_112, F_110)=k5_relat_1(E_112, F_110) | ~m1_subset_1(F_110, k1_zfmisc_1(k2_zfmisc_1(C_111, D_113))) | ~v1_funct_1(F_110) | ~m1_subset_1(E_112, k1_zfmisc_1(k2_zfmisc_1(A_109, B_114))) | ~v1_funct_1(E_112))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.53/1.58  tff(c_427, plain, (![A_109, B_114, E_112]: (k1_partfun1(A_109, B_114, '#skF_2', '#skF_3', E_112, '#skF_5')=k5_relat_1(E_112, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_112, k1_zfmisc_1(k2_zfmisc_1(A_109, B_114))) | ~v1_funct_1(E_112))), inference(resolution, [status(thm)], [c_56, c_425])).
% 3.53/1.58  tff(c_465, plain, (![A_120, B_121, E_122]: (k1_partfun1(A_120, B_121, '#skF_2', '#skF_3', E_122, '#skF_5')=k5_relat_1(E_122, '#skF_5') | ~m1_subset_1(E_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))) | ~v1_funct_1(E_122))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_427])).
% 3.53/1.58  tff(c_471, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_465])).
% 3.53/1.58  tff(c_477, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_471])).
% 3.53/1.58  tff(c_54, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.53/1.58  tff(c_782, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_477, c_54])).
% 3.53/1.58  tff(c_42, plain, (![E_33, A_29, F_34, D_32, C_31, B_30]: (m1_subset_1(k1_partfun1(A_29, B_30, C_31, D_32, E_33, F_34), k1_zfmisc_1(k2_zfmisc_1(A_29, D_32))) | ~m1_subset_1(F_34, k1_zfmisc_1(k2_zfmisc_1(C_31, D_32))) | ~v1_funct_1(F_34) | ~m1_subset_1(E_33, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | ~v1_funct_1(E_33))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.53/1.58  tff(c_786, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_477, c_42])).
% 3.53/1.58  tff(c_790, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_60, c_56, c_786])).
% 3.53/1.58  tff(c_28, plain, (![A_23, B_24, C_25]: (k2_relset_1(A_23, B_24, C_25)=k2_relat_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.53/1.58  tff(c_851, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_790, c_28])).
% 3.53/1.58  tff(c_892, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_782, c_851])).
% 3.53/1.58  tff(c_16, plain, (![A_9, B_11]: (r1_tarski(k2_relat_1(k5_relat_1(A_9, B_11)), k2_relat_1(B_11)) | ~v1_relat_1(B_11) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.53/1.58  tff(c_123, plain, (![B_58, A_59]: (r1_tarski(k2_relat_1(B_58), A_59) | ~v5_relat_1(B_58, A_59) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.53/1.58  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.53/1.58  tff(c_185, plain, (![B_73, A_74]: (k2_relat_1(B_73)=A_74 | ~r1_tarski(A_74, k2_relat_1(B_73)) | ~v5_relat_1(B_73, A_74) | ~v1_relat_1(B_73))), inference(resolution, [status(thm)], [c_123, c_2])).
% 3.53/1.58  tff(c_197, plain, (![A_9, B_11]: (k2_relat_1(k5_relat_1(A_9, B_11))=k2_relat_1(B_11) | ~v5_relat_1(B_11, k2_relat_1(k5_relat_1(A_9, B_11))) | ~v1_relat_1(B_11) | ~v1_relat_1(A_9))), inference(resolution, [status(thm)], [c_16, c_185])).
% 3.53/1.58  tff(c_913, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1('#skF_5') | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_892, c_197])).
% 3.53/1.58  tff(c_954, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_83, c_110, c_892, c_913])).
% 3.53/1.58  tff(c_50, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.53/1.58  tff(c_58, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.53/1.58  tff(c_139, plain, (![A_62, B_63, C_64]: (k1_relset_1(A_62, B_63, C_64)=k1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.53/1.58  tff(c_146, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_139])).
% 3.53/1.58  tff(c_255, plain, (![B_92, A_93, C_94]: (k1_xboole_0=B_92 | k1_relset_1(A_93, B_92, C_94)=A_93 | ~v1_funct_2(C_94, A_93, B_92) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.53/1.58  tff(c_258, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_255])).
% 3.53/1.58  tff(c_264, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_146, c_258])).
% 3.53/1.58  tff(c_265, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_50, c_264])).
% 3.53/1.58  tff(c_12, plain, (![A_5]: (k9_relat_1(A_5, k1_relat_1(A_5))=k2_relat_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.53/1.58  tff(c_278, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_265, c_12])).
% 3.53/1.58  tff(c_286, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_278])).
% 3.53/1.58  tff(c_52, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.53/1.58  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.53/1.58  tff(c_204, plain, (![B_81, A_82]: (k10_relat_1(B_81, k9_relat_1(B_81, A_82))=A_82 | ~v2_funct_1(B_81) | ~r1_tarski(A_82, k1_relat_1(B_81)) | ~v1_funct_1(B_81) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.53/1.58  tff(c_212, plain, (![B_81]: (k10_relat_1(B_81, k9_relat_1(B_81, k1_relat_1(B_81)))=k1_relat_1(B_81) | ~v2_funct_1(B_81) | ~v1_funct_1(B_81) | ~v1_relat_1(B_81))), inference(resolution, [status(thm)], [c_6, c_204])).
% 3.53/1.58  tff(c_273, plain, (k10_relat_1('#skF_5', k9_relat_1('#skF_5', '#skF_2'))=k1_relat_1('#skF_5') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_265, c_212])).
% 3.53/1.58  tff(c_282, plain, (k10_relat_1('#skF_5', k9_relat_1('#skF_5', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_83, c_60, c_52, c_265, c_273])).
% 3.53/1.58  tff(c_324, plain, (k10_relat_1('#skF_5', k2_relat_1('#skF_5'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_286, c_282])).
% 3.53/1.58  tff(c_976, plain, (k10_relat_1('#skF_5', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_954, c_324])).
% 3.53/1.58  tff(c_14, plain, (![B_8, A_6]: (k9_relat_1(B_8, k2_relat_1(A_6))=k2_relat_1(k5_relat_1(A_6, B_8)) | ~v1_relat_1(B_8) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.53/1.58  tff(c_18, plain, (![B_13, A_12]: (k10_relat_1(B_13, k9_relat_1(B_13, A_12))=A_12 | ~v2_funct_1(B_13) | ~r1_tarski(A_12, k1_relat_1(B_13)) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.53/1.58  tff(c_275, plain, (![A_12]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', A_12))=A_12 | ~v2_funct_1('#skF_5') | ~r1_tarski(A_12, '#skF_2') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_265, c_18])).
% 3.53/1.58  tff(c_352, plain, (![A_101]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', A_101))=A_101 | ~r1_tarski(A_101, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_60, c_52, c_275])).
% 3.53/1.58  tff(c_373, plain, (![A_6]: (k10_relat_1('#skF_5', k2_relat_1(k5_relat_1(A_6, '#skF_5')))=k2_relat_1(A_6) | ~r1_tarski(k2_relat_1(A_6), '#skF_2') | ~v1_relat_1('#skF_5') | ~v1_relat_1(A_6))), inference(superposition, [status(thm), theory('equality')], [c_14, c_352])).
% 3.53/1.58  tff(c_387, plain, (![A_6]: (k10_relat_1('#skF_5', k2_relat_1(k5_relat_1(A_6, '#skF_5')))=k2_relat_1(A_6) | ~r1_tarski(k2_relat_1(A_6), '#skF_2') | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_373])).
% 3.53/1.58  tff(c_910, plain, (k10_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_892, c_387])).
% 3.53/1.58  tff(c_952, plain, (k10_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_910])).
% 3.53/1.58  tff(c_1229, plain, (k2_relat_1('#skF_4')='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_976, c_952])).
% 3.53/1.58  tff(c_1230, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_169, c_1229])).
% 3.53/1.58  tff(c_1233, plain, (~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_1230])).
% 3.53/1.58  tff(c_1237, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_111, c_1233])).
% 3.53/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.58  
% 3.53/1.58  Inference rules
% 3.53/1.58  ----------------------
% 3.53/1.58  #Ref     : 0
% 3.53/1.58  #Sup     : 253
% 3.53/1.58  #Fact    : 0
% 3.53/1.58  #Define  : 0
% 3.53/1.58  #Split   : 4
% 3.53/1.58  #Chain   : 0
% 3.53/1.58  #Close   : 0
% 3.53/1.58  
% 3.53/1.58  Ordering : KBO
% 3.53/1.58  
% 3.53/1.58  Simplification rules
% 3.53/1.58  ----------------------
% 3.53/1.58  #Subsume      : 5
% 3.53/1.58  #Demod        : 237
% 3.53/1.58  #Tautology    : 89
% 3.53/1.58  #SimpNegUnit  : 9
% 3.53/1.58  #BackRed      : 11
% 3.53/1.58  
% 3.53/1.58  #Partial instantiations: 0
% 3.53/1.58  #Strategies tried      : 1
% 3.53/1.58  
% 3.53/1.58  Timing (in seconds)
% 3.53/1.58  ----------------------
% 3.53/1.59  Preprocessing        : 0.35
% 3.53/1.59  Parsing              : 0.18
% 3.53/1.59  CNF conversion       : 0.02
% 3.53/1.59  Main loop            : 0.48
% 3.53/1.59  Inferencing          : 0.17
% 3.53/1.59  Reduction            : 0.16
% 3.53/1.59  Demodulation         : 0.12
% 3.53/1.59  BG Simplification    : 0.03
% 3.53/1.59  Subsumption          : 0.08
% 3.53/1.59  Abstraction          : 0.02
% 3.53/1.59  MUC search           : 0.00
% 3.53/1.59  Cooper               : 0.00
% 3.53/1.59  Total                : 0.86
% 3.53/1.59  Index Insertion      : 0.00
% 3.53/1.59  Index Deletion       : 0.00
% 3.53/1.59  Index Matching       : 0.00
% 3.53/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
