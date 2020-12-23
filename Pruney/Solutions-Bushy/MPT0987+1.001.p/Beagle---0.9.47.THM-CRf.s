%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0987+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:12 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 491 expanded)
%              Number of leaves         :   34 ( 187 expanded)
%              Depth                    :   13
%              Number of atoms          :  179 (1673 expanded)
%              Number of equality atoms :   31 ( 123 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ! [C] :
            ( ~ v1_xboole_0(C)
           => ! [D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,A,B)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [E] :
                    ( ( v1_funct_1(E)
                      & v1_funct_2(E,B,C)
                      & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
                   => ( ( v2_funct_2(D,B)
                        & v2_funct_2(E,C) )
                     => v2_funct_2(k1_partfun1(A,B,B,C,D,E),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_funct_2)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_54,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_63,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_75,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_63])).

tff(c_30,plain,(
    v2_funct_2('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_77,plain,(
    ! [C_50,B_51,A_52] :
      ( v5_relat_1(C_50,B_51)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_52,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_89,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_77])).

tff(c_139,plain,(
    ! [B_66,A_67] :
      ( k2_relat_1(B_66) = A_67
      | ~ v2_funct_2(B_66,A_67)
      | ~ v5_relat_1(B_66,A_67)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_142,plain,
    ( k2_relat_1('#skF_5') = '#skF_3'
    | ~ v2_funct_2('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_89,c_139])).

tff(c_148,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_30,c_142])).

tff(c_170,plain,(
    ! [A_68,B_69,C_70] :
      ( k1_relset_1(A_68,B_69,C_70) = k1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_182,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_170])).

tff(c_203,plain,(
    ! [A_74,B_75,C_76] :
      ( m1_subset_1(k1_relset_1(A_74,B_75,C_76),k1_zfmisc_1(A_74))
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_228,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_203])).

tff(c_237,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_228])).

tff(c_22,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(A_27,B_28)
      | ~ m1_subset_1(A_27,k1_zfmisc_1(B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_245,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_237,c_22])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_76,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_63])).

tff(c_32,plain,(
    v2_funct_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_90,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_77])).

tff(c_145,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ v2_funct_2('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_139])).

tff(c_151,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_32,c_145])).

tff(c_300,plain,(
    ! [B_87,A_88] :
      ( k2_relat_1(k5_relat_1(B_87,A_88)) = k2_relat_1(A_88)
      | ~ r1_tarski(k1_relat_1(A_88),k2_relat_1(B_87))
      | ~ v1_relat_1(B_87)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_303,plain,(
    ! [A_88] :
      ( k2_relat_1(k5_relat_1('#skF_4',A_88)) = k2_relat_1(A_88)
      | ~ r1_tarski(k1_relat_1(A_88),'#skF_2')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_300])).

tff(c_311,plain,(
    ! [A_89] :
      ( k2_relat_1(k5_relat_1('#skF_4',A_89)) = k2_relat_1(A_89)
      | ~ r1_tarski(k1_relat_1(A_89),'#skF_2')
      | ~ v1_relat_1(A_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_303])).

tff(c_314,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_245,c_311])).

tff(c_317,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_148,c_314])).

tff(c_8,plain,(
    ! [B_8] :
      ( v2_funct_2(B_8,k2_relat_1(B_8))
      | ~ v5_relat_1(B_8,k2_relat_1(B_8))
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_343,plain,
    ( v2_funct_2(k5_relat_1('#skF_4','#skF_5'),k2_relat_1(k5_relat_1('#skF_4','#skF_5')))
    | ~ v5_relat_1(k5_relat_1('#skF_4','#skF_5'),'#skF_3')
    | ~ v1_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_8])).

tff(c_346,plain,
    ( v2_funct_2(k5_relat_1('#skF_4','#skF_5'),'#skF_3')
    | ~ v5_relat_1(k5_relat_1('#skF_4','#skF_5'),'#skF_3')
    | ~ v1_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_343])).

tff(c_349,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_346])).

tff(c_44,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_38,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_402,plain,(
    ! [C_108,D_111,F_110,A_107,E_109,B_112] :
      ( k1_partfun1(A_107,B_112,C_108,D_111,E_109,F_110) = k5_relat_1(E_109,F_110)
      | ~ m1_subset_1(F_110,k1_zfmisc_1(k2_zfmisc_1(C_108,D_111)))
      | ~ v1_funct_1(F_110)
      | ~ m1_subset_1(E_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_112)))
      | ~ v1_funct_1(E_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_410,plain,(
    ! [A_107,B_112,E_109] :
      ( k1_partfun1(A_107,B_112,'#skF_2','#skF_3',E_109,'#skF_5') = k5_relat_1(E_109,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_112)))
      | ~ v1_funct_1(E_109) ) ),
    inference(resolution,[status(thm)],[c_34,c_402])).

tff(c_486,plain,(
    ! [A_135,B_136,E_137] :
      ( k1_partfun1(A_135,B_136,'#skF_2','#skF_3',E_137,'#skF_5') = k5_relat_1(E_137,'#skF_5')
      | ~ m1_subset_1(E_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136)))
      | ~ v1_funct_1(E_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_410])).

tff(c_500,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_486])).

tff(c_508,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_500])).

tff(c_12,plain,(
    ! [C_11,E_13,B_10,F_14,D_12,A_9] :
      ( m1_subset_1(k1_partfun1(A_9,B_10,C_11,D_12,E_13,F_14),k1_zfmisc_1(k2_zfmisc_1(A_9,D_12)))
      | ~ m1_subset_1(F_14,k1_zfmisc_1(k2_zfmisc_1(C_11,D_12)))
      | ~ v1_funct_1(F_14)
      | ~ m1_subset_1(E_13,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10)))
      | ~ v1_funct_1(E_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_630,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_508,c_12])).

tff(c_634,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_38,c_34,c_630])).

tff(c_2,plain,(
    ! [C_3,A_1,B_2] :
      ( v1_relat_1(C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_735,plain,(
    v1_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_634,c_2])).

tff(c_764,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_349,c_735])).

tff(c_765,plain,
    ( ~ v5_relat_1(k5_relat_1('#skF_4','#skF_5'),'#skF_3')
    | v2_funct_2(k5_relat_1('#skF_4','#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_346])).

tff(c_790,plain,(
    ~ v5_relat_1(k5_relat_1('#skF_4','#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_765])).

tff(c_802,plain,(
    ! [B_159,C_155,D_158,A_154,F_157,E_156] :
      ( k1_partfun1(A_154,B_159,C_155,D_158,E_156,F_157) = k5_relat_1(E_156,F_157)
      | ~ m1_subset_1(F_157,k1_zfmisc_1(k2_zfmisc_1(C_155,D_158)))
      | ~ v1_funct_1(F_157)
      | ~ m1_subset_1(E_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_159)))
      | ~ v1_funct_1(E_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_810,plain,(
    ! [A_154,B_159,E_156] :
      ( k1_partfun1(A_154,B_159,'#skF_2','#skF_3',E_156,'#skF_5') = k5_relat_1(E_156,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_159)))
      | ~ v1_funct_1(E_156) ) ),
    inference(resolution,[status(thm)],[c_34,c_802])).

tff(c_1059,plain,(
    ! [A_194,B_195,E_196] :
      ( k1_partfun1(A_194,B_195,'#skF_2','#skF_3',E_196,'#skF_5') = k5_relat_1(E_196,'#skF_5')
      | ~ m1_subset_1(E_196,k1_zfmisc_1(k2_zfmisc_1(A_194,B_195)))
      | ~ v1_funct_1(E_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_810])).

tff(c_1079,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_1059])).

tff(c_1091,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1079])).

tff(c_1185,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1091,c_12])).

tff(c_1189,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_38,c_34,c_1185])).

tff(c_4,plain,(
    ! [C_6,B_5,A_4] :
      ( v5_relat_1(C_6,B_5)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(A_4,B_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1288,plain,(
    v5_relat_1(k5_relat_1('#skF_4','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1189,c_4])).

tff(c_1322,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_790,c_1288])).

tff(c_1323,plain,(
    v2_funct_2(k5_relat_1('#skF_4','#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_765])).

tff(c_1401,plain,(
    ! [D_220,C_217,B_221,A_216,E_218,F_219] :
      ( k1_partfun1(A_216,B_221,C_217,D_220,E_218,F_219) = k5_relat_1(E_218,F_219)
      | ~ m1_subset_1(F_219,k1_zfmisc_1(k2_zfmisc_1(C_217,D_220)))
      | ~ v1_funct_1(F_219)
      | ~ m1_subset_1(E_218,k1_zfmisc_1(k2_zfmisc_1(A_216,B_221)))
      | ~ v1_funct_1(E_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1409,plain,(
    ! [A_216,B_221,E_218] :
      ( k1_partfun1(A_216,B_221,'#skF_2','#skF_3',E_218,'#skF_5') = k5_relat_1(E_218,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_218,k1_zfmisc_1(k2_zfmisc_1(A_216,B_221)))
      | ~ v1_funct_1(E_218) ) ),
    inference(resolution,[status(thm)],[c_34,c_1401])).

tff(c_1435,plain,(
    ! [A_234,B_235,E_236] :
      ( k1_partfun1(A_234,B_235,'#skF_2','#skF_3',E_236,'#skF_5') = k5_relat_1(E_236,'#skF_5')
      | ~ m1_subset_1(E_236,k1_zfmisc_1(k2_zfmisc_1(A_234,B_235)))
      | ~ v1_funct_1(E_236) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1409])).

tff(c_1449,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_1435])).

tff(c_1457,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1449])).

tff(c_28,plain,(
    ~ v2_funct_2(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1464,plain,(
    ~ v2_funct_2(k5_relat_1('#skF_4','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1457,c_28])).

tff(c_1467,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1323,c_1464])).

%------------------------------------------------------------------------------
