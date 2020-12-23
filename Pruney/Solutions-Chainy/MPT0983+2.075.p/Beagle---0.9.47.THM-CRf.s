%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:11 EST 2020

% Result     : Theorem 5.89s
% Output     : CNFRefutation 5.89s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 580 expanded)
%              Number of leaves         :   45 ( 225 expanded)
%              Depth                    :   10
%              Number of atoms          :  254 (1791 expanded)
%              Number of equality atoms :   60 ( 232 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_160,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_101,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_99,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_79,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_140,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_46,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
           => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_60,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_153,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_72,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_68,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_66,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_52,plain,(
    ! [A_33] : k6_relat_1(A_33) = k6_partfun1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_28,plain,(
    ! [A_10] : v2_funct_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_76,plain,(
    ! [A_10] : v2_funct_1(k6_partfun1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_28])).

tff(c_48,plain,(
    ! [C_29,D_30,B_28,F_32,A_27,E_31] :
      ( m1_subset_1(k1_partfun1(A_27,B_28,C_29,D_30,E_31,F_32),k1_zfmisc_1(k2_zfmisc_1(A_27,D_30)))
      | ~ m1_subset_1(F_32,k1_zfmisc_1(k2_zfmisc_1(C_29,D_30)))
      | ~ v1_funct_1(F_32)
      | ~ m1_subset_1(E_31,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_funct_1(E_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_42,plain,(
    ! [A_24] : m1_subset_1(k6_relat_1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_75,plain,(
    ! [A_24] : m1_subset_1(k6_partfun1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_42])).

tff(c_62,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_655,plain,(
    ! [D_121,C_122,A_123,B_124] :
      ( D_121 = C_122
      | ~ r2_relset_1(A_123,B_124,C_122,D_121)
      | ~ m1_subset_1(D_121,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124)))
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_665,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_62,c_655])).

tff(c_684,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_665])).

tff(c_732,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_684])).

tff(c_1093,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_732])).

tff(c_1100,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_68,c_64,c_1093])).

tff(c_1101,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_684])).

tff(c_1687,plain,(
    ! [A_278,B_280,C_281,D_282,E_279] :
      ( k1_xboole_0 = C_281
      | v2_funct_1(D_282)
      | ~ v2_funct_1(k1_partfun1(A_278,B_280,B_280,C_281,D_282,E_279))
      | ~ m1_subset_1(E_279,k1_zfmisc_1(k2_zfmisc_1(B_280,C_281)))
      | ~ v1_funct_2(E_279,B_280,C_281)
      | ~ v1_funct_1(E_279)
      | ~ m1_subset_1(D_282,k1_zfmisc_1(k2_zfmisc_1(A_278,B_280)))
      | ~ v1_funct_2(D_282,A_278,B_280)
      | ~ v1_funct_1(D_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1689,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1101,c_1687])).

tff(c_1691,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_66,c_64,c_76,c_1689])).

tff(c_1692,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_1691])).

tff(c_16,plain,(
    ! [A_6] : v1_xboole_0('#skF_1'(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_120,plain,(
    ! [A_52] :
      ( k1_xboole_0 = A_52
      | ~ v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_124,plain,(
    ! [A_6] : '#skF_1'(A_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_120])).

tff(c_18,plain,(
    ! [A_6] : m1_subset_1('#skF_1'(A_6),k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_154,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_18])).

tff(c_172,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(A_59,B_60)
      | ~ m1_subset_1(A_59,k1_zfmisc_1(B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_192,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(resolution,[status(thm)],[c_154,c_172])).

tff(c_1722,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1692,c_192])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1724,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_2',B_5) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1692,c_1692,c_14])).

tff(c_190,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_70,c_172])).

tff(c_274,plain,(
    ! [B_70,A_71] :
      ( B_70 = A_71
      | ~ r1_tarski(B_70,A_71)
      | ~ r1_tarski(A_71,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_287,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_190,c_274])).

tff(c_402,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_287])).

tff(c_1860,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1724,c_402])).

tff(c_1865,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1722,c_1860])).

tff(c_1866,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_287])).

tff(c_1890,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1866,c_70])).

tff(c_2153,plain,(
    ! [D_329,C_330,A_331,B_332] :
      ( D_329 = C_330
      | ~ r2_relset_1(A_331,B_332,C_330,D_329)
      | ~ m1_subset_1(D_329,k1_zfmisc_1(k2_zfmisc_1(A_331,B_332)))
      | ~ m1_subset_1(C_330,k1_zfmisc_1(k2_zfmisc_1(A_331,B_332))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2161,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_62,c_2153])).

tff(c_2176,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_2161])).

tff(c_2240,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2176])).

tff(c_2627,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_2240])).

tff(c_2634,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1890,c_1866,c_68,c_64,c_2627])).

tff(c_2635,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2176])).

tff(c_3086,plain,(
    ! [C_460,E_458,D_461,B_459,A_457] :
      ( k1_xboole_0 = C_460
      | v2_funct_1(D_461)
      | ~ v2_funct_1(k1_partfun1(A_457,B_459,B_459,C_460,D_461,E_458))
      | ~ m1_subset_1(E_458,k1_zfmisc_1(k2_zfmisc_1(B_459,C_460)))
      | ~ v1_funct_2(E_458,B_459,C_460)
      | ~ v1_funct_1(E_458)
      | ~ m1_subset_1(D_461,k1_zfmisc_1(k2_zfmisc_1(A_457,B_459)))
      | ~ v1_funct_2(D_461,A_457,B_459)
      | ~ v1_funct_1(D_461) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_3088,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2635,c_3086])).

tff(c_3090,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_1890,c_1866,c_68,c_66,c_64,c_76,c_3088])).

tff(c_3091,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_3090])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1905,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1866,c_10])).

tff(c_1981,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1905])).

tff(c_3111,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3091,c_1981])).

tff(c_3366,plain,(
    ! [B_478] : k2_zfmisc_1('#skF_2',B_478) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3091,c_3091,c_14])).

tff(c_3418,plain,(
    '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3366,c_1866])).

tff(c_3454,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3111,c_3418])).

tff(c_3456,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1905])).

tff(c_96,plain,(
    ! [A_51] : k6_relat_1(A_51) = k6_partfun1(A_51) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_24,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_102,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_24])).

tff(c_115,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_76])).

tff(c_3471,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3456,c_115])).

tff(c_3477,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_3471])).

tff(c_3478,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_3567,plain,(
    ! [C_490,A_491,B_492] :
      ( v1_relat_1(C_490)
      | ~ m1_subset_1(C_490,k1_zfmisc_1(k2_zfmisc_1(A_491,B_492))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3595,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_3567])).

tff(c_3671,plain,(
    ! [C_502,B_503,A_504] :
      ( v5_relat_1(C_502,B_503)
      | ~ m1_subset_1(C_502,k1_zfmisc_1(k2_zfmisc_1(A_504,B_503))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3699,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_3671])).

tff(c_3797,plain,(
    ! [A_523,B_524,D_525] :
      ( r2_relset_1(A_523,B_524,D_525,D_525)
      | ~ m1_subset_1(D_525,k1_zfmisc_1(k2_zfmisc_1(A_523,B_524))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_3815,plain,(
    ! [A_24] : r2_relset_1(A_24,A_24,k6_partfun1(A_24),k6_partfun1(A_24)) ),
    inference(resolution,[status(thm)],[c_75,c_3797])).

tff(c_3875,plain,(
    ! [A_534,B_535,C_536] :
      ( k2_relset_1(A_534,B_535,C_536) = k2_relat_1(C_536)
      | ~ m1_subset_1(C_536,k1_zfmisc_1(k2_zfmisc_1(A_534,B_535))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3903,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_3875])).

tff(c_3919,plain,(
    ! [D_539,C_540,A_541,B_542] :
      ( D_539 = C_540
      | ~ r2_relset_1(A_541,B_542,C_540,D_539)
      | ~ m1_subset_1(D_539,k1_zfmisc_1(k2_zfmisc_1(A_541,B_542)))
      | ~ m1_subset_1(C_540,k1_zfmisc_1(k2_zfmisc_1(A_541,B_542))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_3929,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_62,c_3919])).

tff(c_3948,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_3929])).

tff(c_4324,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_3948])).

tff(c_4419,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_4324])).

tff(c_4426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_68,c_64,c_4419])).

tff(c_4427,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3948])).

tff(c_4576,plain,(
    ! [A_642,B_643,C_644,D_645] :
      ( k2_relset_1(A_642,B_643,C_644) = B_643
      | ~ r2_relset_1(B_643,B_643,k1_partfun1(B_643,A_642,A_642,B_643,D_645,C_644),k6_partfun1(B_643))
      | ~ m1_subset_1(D_645,k1_zfmisc_1(k2_zfmisc_1(B_643,A_642)))
      | ~ v1_funct_2(D_645,B_643,A_642)
      | ~ v1_funct_1(D_645)
      | ~ m1_subset_1(C_644,k1_zfmisc_1(k2_zfmisc_1(A_642,B_643)))
      | ~ v1_funct_2(C_644,A_642,B_643)
      | ~ v1_funct_1(C_644) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_4579,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4427,c_4576])).

tff(c_4584,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_74,c_72,c_70,c_3815,c_3903,c_4579])).

tff(c_44,plain,(
    ! [B_26] :
      ( v2_funct_2(B_26,k2_relat_1(B_26))
      | ~ v5_relat_1(B_26,k2_relat_1(B_26))
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4593,plain,
    ( v2_funct_2('#skF_5',k2_relat_1('#skF_5'))
    | ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4584,c_44])).

tff(c_4600,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3595,c_3699,c_4584,c_4593])).

tff(c_4602,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3478,c_4600])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.89/2.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.89/2.09  
% 5.89/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.89/2.10  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 5.89/2.10  
% 5.89/2.10  %Foreground sorts:
% 5.89/2.10  
% 5.89/2.10  
% 5.89/2.10  %Background operators:
% 5.89/2.10  
% 5.89/2.10  
% 5.89/2.10  %Foreground operators:
% 5.89/2.10  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.89/2.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.89/2.10  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.89/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.89/2.10  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.89/2.10  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.89/2.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.89/2.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.89/2.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.89/2.10  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.89/2.10  tff('#skF_5', type, '#skF_5': $i).
% 5.89/2.10  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.89/2.10  tff('#skF_2', type, '#skF_2': $i).
% 5.89/2.10  tff('#skF_3', type, '#skF_3': $i).
% 5.89/2.10  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.89/2.10  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.89/2.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.89/2.10  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.89/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.89/2.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.89/2.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.89/2.10  tff('#skF_4', type, '#skF_4': $i).
% 5.89/2.10  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.89/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.89/2.10  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.89/2.10  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.89/2.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.89/2.10  
% 5.89/2.12  tff(f_160, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 5.89/2.12  tff(f_101, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.89/2.12  tff(f_55, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.89/2.12  tff(f_99, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.89/2.12  tff(f_79, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 5.89/2.12  tff(f_77, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.89/2.12  tff(f_140, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 5.89/2.12  tff(f_46, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_subset_1)).
% 5.89/2.12  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.89/2.12  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.89/2.12  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.89/2.12  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.89/2.12  tff(f_51, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 5.89/2.12  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.89/2.12  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.89/2.12  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.89/2.12  tff(f_118, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 5.89/2.12  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 5.89/2.12  tff(c_60, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.89/2.12  tff(c_153, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_60])).
% 5.89/2.12  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.89/2.12  tff(c_72, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.89/2.12  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.89/2.12  tff(c_68, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.89/2.12  tff(c_66, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.89/2.12  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.89/2.12  tff(c_52, plain, (![A_33]: (k6_relat_1(A_33)=k6_partfun1(A_33))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.89/2.12  tff(c_28, plain, (![A_10]: (v2_funct_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.89/2.12  tff(c_76, plain, (![A_10]: (v2_funct_1(k6_partfun1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_28])).
% 5.89/2.12  tff(c_48, plain, (![C_29, D_30, B_28, F_32, A_27, E_31]: (m1_subset_1(k1_partfun1(A_27, B_28, C_29, D_30, E_31, F_32), k1_zfmisc_1(k2_zfmisc_1(A_27, D_30))) | ~m1_subset_1(F_32, k1_zfmisc_1(k2_zfmisc_1(C_29, D_30))) | ~v1_funct_1(F_32) | ~m1_subset_1(E_31, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~v1_funct_1(E_31))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.89/2.12  tff(c_42, plain, (![A_24]: (m1_subset_1(k6_relat_1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.89/2.12  tff(c_75, plain, (![A_24]: (m1_subset_1(k6_partfun1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_42])).
% 5.89/2.12  tff(c_62, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.89/2.12  tff(c_655, plain, (![D_121, C_122, A_123, B_124]: (D_121=C_122 | ~r2_relset_1(A_123, B_124, C_122, D_121) | ~m1_subset_1(D_121, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.89/2.12  tff(c_665, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_62, c_655])).
% 5.89/2.12  tff(c_684, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_665])).
% 5.89/2.12  tff(c_732, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_684])).
% 5.89/2.12  tff(c_1093, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_732])).
% 5.89/2.12  tff(c_1100, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_68, c_64, c_1093])).
% 5.89/2.12  tff(c_1101, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_684])).
% 5.89/2.12  tff(c_1687, plain, (![A_278, B_280, C_281, D_282, E_279]: (k1_xboole_0=C_281 | v2_funct_1(D_282) | ~v2_funct_1(k1_partfun1(A_278, B_280, B_280, C_281, D_282, E_279)) | ~m1_subset_1(E_279, k1_zfmisc_1(k2_zfmisc_1(B_280, C_281))) | ~v1_funct_2(E_279, B_280, C_281) | ~v1_funct_1(E_279) | ~m1_subset_1(D_282, k1_zfmisc_1(k2_zfmisc_1(A_278, B_280))) | ~v1_funct_2(D_282, A_278, B_280) | ~v1_funct_1(D_282))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.89/2.12  tff(c_1689, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1101, c_1687])).
% 5.89/2.12  tff(c_1691, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_66, c_64, c_76, c_1689])).
% 5.89/2.12  tff(c_1692, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_153, c_1691])).
% 5.89/2.12  tff(c_16, plain, (![A_6]: (v1_xboole_0('#skF_1'(A_6)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.89/2.12  tff(c_120, plain, (![A_52]: (k1_xboole_0=A_52 | ~v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.89/2.12  tff(c_124, plain, (![A_6]: ('#skF_1'(A_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_120])).
% 5.89/2.12  tff(c_18, plain, (![A_6]: (m1_subset_1('#skF_1'(A_6), k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.89/2.12  tff(c_154, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_18])).
% 5.89/2.12  tff(c_172, plain, (![A_59, B_60]: (r1_tarski(A_59, B_60) | ~m1_subset_1(A_59, k1_zfmisc_1(B_60)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.89/2.12  tff(c_192, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(resolution, [status(thm)], [c_154, c_172])).
% 5.89/2.12  tff(c_1722, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_1692, c_192])).
% 5.89/2.12  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.89/2.12  tff(c_1724, plain, (![B_5]: (k2_zfmisc_1('#skF_2', B_5)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1692, c_1692, c_14])).
% 5.89/2.12  tff(c_190, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_70, c_172])).
% 5.89/2.12  tff(c_274, plain, (![B_70, A_71]: (B_70=A_71 | ~r1_tarski(B_70, A_71) | ~r1_tarski(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.89/2.12  tff(c_287, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_190, c_274])).
% 5.89/2.12  tff(c_402, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_287])).
% 5.89/2.12  tff(c_1860, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1724, c_402])).
% 5.89/2.12  tff(c_1865, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1722, c_1860])).
% 5.89/2.12  tff(c_1866, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_287])).
% 5.89/2.12  tff(c_1890, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1866, c_70])).
% 5.89/2.12  tff(c_2153, plain, (![D_329, C_330, A_331, B_332]: (D_329=C_330 | ~r2_relset_1(A_331, B_332, C_330, D_329) | ~m1_subset_1(D_329, k1_zfmisc_1(k2_zfmisc_1(A_331, B_332))) | ~m1_subset_1(C_330, k1_zfmisc_1(k2_zfmisc_1(A_331, B_332))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.89/2.12  tff(c_2161, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_62, c_2153])).
% 5.89/2.12  tff(c_2176, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_2161])).
% 5.89/2.12  tff(c_2240, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_2176])).
% 5.89/2.12  tff(c_2627, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_2240])).
% 5.89/2.12  tff(c_2634, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_1890, c_1866, c_68, c_64, c_2627])).
% 5.89/2.12  tff(c_2635, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_2176])).
% 5.89/2.12  tff(c_3086, plain, (![C_460, E_458, D_461, B_459, A_457]: (k1_xboole_0=C_460 | v2_funct_1(D_461) | ~v2_funct_1(k1_partfun1(A_457, B_459, B_459, C_460, D_461, E_458)) | ~m1_subset_1(E_458, k1_zfmisc_1(k2_zfmisc_1(B_459, C_460))) | ~v1_funct_2(E_458, B_459, C_460) | ~v1_funct_1(E_458) | ~m1_subset_1(D_461, k1_zfmisc_1(k2_zfmisc_1(A_457, B_459))) | ~v1_funct_2(D_461, A_457, B_459) | ~v1_funct_1(D_461))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.89/2.12  tff(c_3088, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2635, c_3086])).
% 5.89/2.12  tff(c_3090, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_1890, c_1866, c_68, c_66, c_64, c_76, c_3088])).
% 5.89/2.12  tff(c_3091, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_153, c_3090])).
% 5.89/2.12  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.89/2.12  tff(c_1905, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1866, c_10])).
% 5.89/2.12  tff(c_1981, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_1905])).
% 5.89/2.12  tff(c_3111, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3091, c_1981])).
% 5.89/2.12  tff(c_3366, plain, (![B_478]: (k2_zfmisc_1('#skF_2', B_478)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3091, c_3091, c_14])).
% 5.89/2.12  tff(c_3418, plain, ('#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3366, c_1866])).
% 5.89/2.12  tff(c_3454, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3111, c_3418])).
% 5.89/2.12  tff(c_3456, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1905])).
% 5.89/2.12  tff(c_96, plain, (![A_51]: (k6_relat_1(A_51)=k6_partfun1(A_51))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.89/2.12  tff(c_24, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.89/2.12  tff(c_102, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_96, c_24])).
% 5.89/2.12  tff(c_115, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_102, c_76])).
% 5.89/2.12  tff(c_3471, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3456, c_115])).
% 5.89/2.12  tff(c_3477, plain, $false, inference(negUnitSimplification, [status(thm)], [c_153, c_3471])).
% 5.89/2.12  tff(c_3478, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_60])).
% 5.89/2.12  tff(c_3567, plain, (![C_490, A_491, B_492]: (v1_relat_1(C_490) | ~m1_subset_1(C_490, k1_zfmisc_1(k2_zfmisc_1(A_491, B_492))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.89/2.12  tff(c_3595, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_3567])).
% 5.89/2.12  tff(c_3671, plain, (![C_502, B_503, A_504]: (v5_relat_1(C_502, B_503) | ~m1_subset_1(C_502, k1_zfmisc_1(k2_zfmisc_1(A_504, B_503))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.89/2.12  tff(c_3699, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_3671])).
% 5.89/2.12  tff(c_3797, plain, (![A_523, B_524, D_525]: (r2_relset_1(A_523, B_524, D_525, D_525) | ~m1_subset_1(D_525, k1_zfmisc_1(k2_zfmisc_1(A_523, B_524))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.89/2.12  tff(c_3815, plain, (![A_24]: (r2_relset_1(A_24, A_24, k6_partfun1(A_24), k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_75, c_3797])).
% 5.89/2.12  tff(c_3875, plain, (![A_534, B_535, C_536]: (k2_relset_1(A_534, B_535, C_536)=k2_relat_1(C_536) | ~m1_subset_1(C_536, k1_zfmisc_1(k2_zfmisc_1(A_534, B_535))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.89/2.12  tff(c_3903, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_3875])).
% 5.89/2.12  tff(c_3919, plain, (![D_539, C_540, A_541, B_542]: (D_539=C_540 | ~r2_relset_1(A_541, B_542, C_540, D_539) | ~m1_subset_1(D_539, k1_zfmisc_1(k2_zfmisc_1(A_541, B_542))) | ~m1_subset_1(C_540, k1_zfmisc_1(k2_zfmisc_1(A_541, B_542))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.89/2.12  tff(c_3929, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_62, c_3919])).
% 5.89/2.12  tff(c_3948, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_3929])).
% 5.89/2.12  tff(c_4324, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_3948])).
% 5.89/2.12  tff(c_4419, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_4324])).
% 5.89/2.12  tff(c_4426, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_68, c_64, c_4419])).
% 5.89/2.12  tff(c_4427, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_3948])).
% 5.89/2.12  tff(c_4576, plain, (![A_642, B_643, C_644, D_645]: (k2_relset_1(A_642, B_643, C_644)=B_643 | ~r2_relset_1(B_643, B_643, k1_partfun1(B_643, A_642, A_642, B_643, D_645, C_644), k6_partfun1(B_643)) | ~m1_subset_1(D_645, k1_zfmisc_1(k2_zfmisc_1(B_643, A_642))) | ~v1_funct_2(D_645, B_643, A_642) | ~v1_funct_1(D_645) | ~m1_subset_1(C_644, k1_zfmisc_1(k2_zfmisc_1(A_642, B_643))) | ~v1_funct_2(C_644, A_642, B_643) | ~v1_funct_1(C_644))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.89/2.12  tff(c_4579, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4427, c_4576])).
% 5.89/2.12  tff(c_4584, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_74, c_72, c_70, c_3815, c_3903, c_4579])).
% 5.89/2.12  tff(c_44, plain, (![B_26]: (v2_funct_2(B_26, k2_relat_1(B_26)) | ~v5_relat_1(B_26, k2_relat_1(B_26)) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.89/2.12  tff(c_4593, plain, (v2_funct_2('#skF_5', k2_relat_1('#skF_5')) | ~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4584, c_44])).
% 5.89/2.12  tff(c_4600, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3595, c_3699, c_4584, c_4593])).
% 5.89/2.12  tff(c_4602, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3478, c_4600])).
% 5.89/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.89/2.12  
% 5.89/2.12  Inference rules
% 5.89/2.12  ----------------------
% 5.89/2.12  #Ref     : 0
% 6.08/2.12  #Sup     : 956
% 6.08/2.12  #Fact    : 0
% 6.08/2.12  #Define  : 0
% 6.08/2.12  #Split   : 20
% 6.08/2.12  #Chain   : 0
% 6.08/2.12  #Close   : 0
% 6.08/2.12  
% 6.08/2.12  Ordering : KBO
% 6.08/2.12  
% 6.08/2.12  Simplification rules
% 6.08/2.12  ----------------------
% 6.08/2.12  #Subsume      : 110
% 6.08/2.12  #Demod        : 895
% 6.08/2.12  #Tautology    : 446
% 6.08/2.12  #SimpNegUnit  : 8
% 6.08/2.12  #BackRed      : 156
% 6.08/2.12  
% 6.08/2.12  #Partial instantiations: 0
% 6.08/2.12  #Strategies tried      : 1
% 6.08/2.12  
% 6.08/2.12  Timing (in seconds)
% 6.08/2.12  ----------------------
% 6.08/2.12  Preprocessing        : 0.35
% 6.08/2.12  Parsing              : 0.18
% 6.08/2.12  CNF conversion       : 0.03
% 6.08/2.12  Main loop            : 0.98
% 6.08/2.12  Inferencing          : 0.35
% 6.08/2.12  Reduction            : 0.35
% 6.08/2.12  Demodulation         : 0.25
% 6.08/2.12  BG Simplification    : 0.03
% 6.08/2.12  Subsumption          : 0.16
% 6.08/2.12  Abstraction          : 0.04
% 6.08/2.12  MUC search           : 0.00
% 6.08/2.12  Cooper               : 0.00
% 6.08/2.12  Total                : 1.38
% 6.08/2.12  Index Insertion      : 0.00
% 6.08/2.12  Index Deletion       : 0.00
% 6.08/2.12  Index Matching       : 0.00
% 6.08/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
