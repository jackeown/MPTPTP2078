%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:08 EST 2020

% Result     : Theorem 5.81s
% Output     : CNFRefutation 5.95s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 307 expanded)
%              Number of leaves         :   40 ( 125 expanded)
%              Depth                    :   10
%              Number of atoms          :  204 ( 875 expanded)
%              Number of equality atoms :   36 (  90 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_150,negated_conjecture,(
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

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_91,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_89,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_69,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_130,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_108,axiom,(
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

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_124,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_xboole_0(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62)))
      | ~ v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_135,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_124])).

tff(c_138,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_42,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_71,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_56,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_54,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_48,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_34,plain,(
    ! [A_30] : k6_relat_1(A_30) = k6_partfun1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_8,plain,(
    ! [A_3] : v2_funct_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_58,plain,(
    ! [A_3] : v2_funct_1(k6_partfun1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_8])).

tff(c_30,plain,(
    ! [A_24,B_25,F_29,D_27,C_26,E_28] :
      ( m1_subset_1(k1_partfun1(A_24,B_25,C_26,D_27,E_28,F_29),k1_zfmisc_1(k2_zfmisc_1(A_24,D_27)))
      | ~ m1_subset_1(F_29,k1_zfmisc_1(k2_zfmisc_1(C_26,D_27)))
      | ~ v1_funct_1(F_29)
      | ~ m1_subset_1(E_28,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25)))
      | ~ v1_funct_1(E_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_24,plain,(
    ! [A_21] : m1_subset_1(k6_relat_1(A_21),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_57,plain,(
    ! [A_21] : m1_subset_1(k6_partfun1(A_21),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_24])).

tff(c_44,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_317,plain,(
    ! [D_77,C_78,A_79,B_80] :
      ( D_77 = C_78
      | ~ r2_relset_1(A_79,B_80,C_78,D_77)
      | ~ m1_subset_1(D_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80)))
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_325,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_44,c_317])).

tff(c_340,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_325])).

tff(c_362,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_340])).

tff(c_978,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_362])).

tff(c_982,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_46,c_978])).

tff(c_983,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_340])).

tff(c_1749,plain,(
    ! [D_173,B_174,A_171,C_175,E_172] :
      ( k1_xboole_0 = C_175
      | v2_funct_1(D_173)
      | ~ v2_funct_1(k1_partfun1(A_171,B_174,B_174,C_175,D_173,E_172))
      | ~ m1_subset_1(E_172,k1_zfmisc_1(k2_zfmisc_1(B_174,C_175)))
      | ~ v1_funct_2(E_172,B_174,C_175)
      | ~ v1_funct_1(E_172)
      | ~ m1_subset_1(D_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_174)))
      | ~ v1_funct_2(D_173,A_171,B_174)
      | ~ v1_funct_1(D_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1751,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_983,c_1749])).

tff(c_1753,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_46,c_58,c_1751])).

tff(c_1754,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_1753])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1780,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1754,c_2])).

tff(c_1782,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_1780])).

tff(c_1784,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_72,plain,(
    ! [B_46,A_47] :
      ( ~ v1_xboole_0(B_46)
      | B_46 = A_47
      | ~ v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_75,plain,(
    ! [A_47] :
      ( k1_xboole_0 = A_47
      | ~ v1_xboole_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_2,c_72])).

tff(c_1797,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1784,c_75])).

tff(c_1783,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_1790,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1783,c_75])).

tff(c_1806,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1797,c_1790])).

tff(c_1817,plain,(
    ~ v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1806,c_71])).

tff(c_1835,plain,(
    ! [A_179] :
      ( v1_xboole_0(k6_partfun1(A_179))
      | ~ v1_xboole_0(A_179) ) ),
    inference(resolution,[status(thm)],[c_57,c_124])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1791,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_1783,c_4])).

tff(c_1827,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1806,c_1791])).

tff(c_1843,plain,(
    ! [A_180] :
      ( k6_partfun1(A_180) = '#skF_1'
      | ~ v1_xboole_0(A_180) ) ),
    inference(resolution,[status(thm)],[c_1835,c_1827])).

tff(c_1851,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1784,c_1843])).

tff(c_1873,plain,(
    v2_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1851,c_58])).

tff(c_1882,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1817,c_1873])).

tff(c_1883,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1896,plain,(
    ! [C_188,A_189,B_190] :
      ( v1_relat_1(C_188)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1909,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_1896])).

tff(c_1910,plain,(
    ! [C_191,B_192,A_193] :
      ( v5_relat_1(C_191,B_192)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_193,B_192))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1922,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_1910])).

tff(c_2091,plain,(
    ! [A_209,B_210,D_211] :
      ( r2_relset_1(A_209,B_210,D_211,D_211)
      | ~ m1_subset_1(D_211,k1_zfmisc_1(k2_zfmisc_1(A_209,B_210))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2101,plain,(
    ! [A_21] : r2_relset_1(A_21,A_21,k6_partfun1(A_21),k6_partfun1(A_21)) ),
    inference(resolution,[status(thm)],[c_57,c_2091])).

tff(c_2104,plain,(
    ! [A_212,B_213,C_214] :
      ( k2_relset_1(A_212,B_213,C_214) = k2_relat_1(C_214)
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(A_212,B_213))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2120,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_2104])).

tff(c_2150,plain,(
    ! [D_216,C_217,A_218,B_219] :
      ( D_216 = C_217
      | ~ r2_relset_1(A_218,B_219,C_217,D_216)
      | ~ m1_subset_1(D_216,k1_zfmisc_1(k2_zfmisc_1(A_218,B_219)))
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(A_218,B_219))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2158,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_44,c_2150])).

tff(c_2173,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_2158])).

tff(c_2202,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2173])).

tff(c_2907,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_2202])).

tff(c_2911,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_46,c_2907])).

tff(c_2912,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2173])).

tff(c_4490,plain,(
    ! [A_325,B_326,C_327,D_328] :
      ( k2_relset_1(A_325,B_326,C_327) = B_326
      | ~ r2_relset_1(B_326,B_326,k1_partfun1(B_326,A_325,A_325,B_326,D_328,C_327),k6_partfun1(B_326))
      | ~ m1_subset_1(D_328,k1_zfmisc_1(k2_zfmisc_1(B_326,A_325)))
      | ~ v1_funct_2(D_328,B_326,A_325)
      | ~ v1_funct_1(D_328)
      | ~ m1_subset_1(C_327,k1_zfmisc_1(k2_zfmisc_1(A_325,B_326)))
      | ~ v1_funct_2(C_327,A_325,B_326)
      | ~ v1_funct_1(C_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_4508,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2912,c_4490])).

tff(c_4516,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_56,c_54,c_52,c_2101,c_2120,c_4508])).

tff(c_26,plain,(
    ! [B_23] :
      ( v2_funct_2(B_23,k2_relat_1(B_23))
      | ~ v5_relat_1(B_23,k2_relat_1(B_23))
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4521,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4516,c_26])).

tff(c_4525,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1909,c_1922,c_4516,c_4521])).

tff(c_4527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1883,c_4525])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:01:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.81/2.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.81/2.10  
% 5.81/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.81/2.10  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.81/2.10  
% 5.81/2.10  %Foreground sorts:
% 5.81/2.10  
% 5.81/2.10  
% 5.81/2.10  %Background operators:
% 5.81/2.10  
% 5.81/2.10  
% 5.81/2.10  %Foreground operators:
% 5.81/2.10  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.81/2.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.81/2.10  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.81/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.81/2.10  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.81/2.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.81/2.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.81/2.10  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.81/2.10  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.81/2.10  tff('#skF_2', type, '#skF_2': $i).
% 5.81/2.10  tff('#skF_3', type, '#skF_3': $i).
% 5.81/2.10  tff('#skF_1', type, '#skF_1': $i).
% 5.81/2.10  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.81/2.10  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.81/2.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.81/2.10  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.81/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.81/2.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.81/2.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.81/2.10  tff('#skF_4', type, '#skF_4': $i).
% 5.81/2.10  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.81/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.81/2.10  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.81/2.10  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.81/2.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.81/2.10  
% 5.95/2.12  tff(f_150, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 5.95/2.12  tff(f_55, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 5.95/2.12  tff(f_91, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.95/2.12  tff(f_38, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.95/2.12  tff(f_89, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.95/2.12  tff(f_69, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 5.95/2.12  tff(f_67, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.95/2.12  tff(f_130, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 5.95/2.12  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.95/2.12  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 5.95/2.12  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.95/2.12  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.95/2.12  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.95/2.12  tff(f_108, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 5.95/2.12  tff(f_77, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 5.95/2.12  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.95/2.12  tff(c_124, plain, (![C_60, A_61, B_62]: (v1_xboole_0(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))) | ~v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.95/2.12  tff(c_135, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_124])).
% 5.95/2.12  tff(c_138, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_135])).
% 5.95/2.12  tff(c_42, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.95/2.12  tff(c_71, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_42])).
% 5.95/2.12  tff(c_56, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.95/2.12  tff(c_54, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.95/2.12  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.95/2.12  tff(c_48, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.95/2.12  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.95/2.12  tff(c_34, plain, (![A_30]: (k6_relat_1(A_30)=k6_partfun1(A_30))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.95/2.12  tff(c_8, plain, (![A_3]: (v2_funct_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.95/2.12  tff(c_58, plain, (![A_3]: (v2_funct_1(k6_partfun1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_8])).
% 5.95/2.12  tff(c_30, plain, (![A_24, B_25, F_29, D_27, C_26, E_28]: (m1_subset_1(k1_partfun1(A_24, B_25, C_26, D_27, E_28, F_29), k1_zfmisc_1(k2_zfmisc_1(A_24, D_27))) | ~m1_subset_1(F_29, k1_zfmisc_1(k2_zfmisc_1(C_26, D_27))) | ~v1_funct_1(F_29) | ~m1_subset_1(E_28, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))) | ~v1_funct_1(E_28))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.95/2.12  tff(c_24, plain, (![A_21]: (m1_subset_1(k6_relat_1(A_21), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.95/2.12  tff(c_57, plain, (![A_21]: (m1_subset_1(k6_partfun1(A_21), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_24])).
% 5.95/2.12  tff(c_44, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.95/2.12  tff(c_317, plain, (![D_77, C_78, A_79, B_80]: (D_77=C_78 | ~r2_relset_1(A_79, B_80, C_78, D_77) | ~m1_subset_1(D_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.95/2.12  tff(c_325, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_44, c_317])).
% 5.95/2.12  tff(c_340, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_325])).
% 5.95/2.12  tff(c_362, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_340])).
% 5.95/2.12  tff(c_978, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_362])).
% 5.95/2.12  tff(c_982, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_46, c_978])).
% 5.95/2.12  tff(c_983, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_340])).
% 5.95/2.12  tff(c_1749, plain, (![D_173, B_174, A_171, C_175, E_172]: (k1_xboole_0=C_175 | v2_funct_1(D_173) | ~v2_funct_1(k1_partfun1(A_171, B_174, B_174, C_175, D_173, E_172)) | ~m1_subset_1(E_172, k1_zfmisc_1(k2_zfmisc_1(B_174, C_175))) | ~v1_funct_2(E_172, B_174, C_175) | ~v1_funct_1(E_172) | ~m1_subset_1(D_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_174))) | ~v1_funct_2(D_173, A_171, B_174) | ~v1_funct_1(D_173))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.95/2.12  tff(c_1751, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_983, c_1749])).
% 5.95/2.12  tff(c_1753, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_46, c_58, c_1751])).
% 5.95/2.12  tff(c_1754, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_71, c_1753])).
% 5.95/2.12  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.95/2.12  tff(c_1780, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1754, c_2])).
% 5.95/2.12  tff(c_1782, plain, $false, inference(negUnitSimplification, [status(thm)], [c_138, c_1780])).
% 5.95/2.12  tff(c_1784, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_135])).
% 5.95/2.12  tff(c_72, plain, (![B_46, A_47]: (~v1_xboole_0(B_46) | B_46=A_47 | ~v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.95/2.12  tff(c_75, plain, (![A_47]: (k1_xboole_0=A_47 | ~v1_xboole_0(A_47))), inference(resolution, [status(thm)], [c_2, c_72])).
% 5.95/2.12  tff(c_1797, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_1784, c_75])).
% 5.95/2.12  tff(c_1783, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_135])).
% 5.95/2.12  tff(c_1790, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1783, c_75])).
% 5.95/2.12  tff(c_1806, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1797, c_1790])).
% 5.95/2.12  tff(c_1817, plain, (~v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1806, c_71])).
% 5.95/2.12  tff(c_1835, plain, (![A_179]: (v1_xboole_0(k6_partfun1(A_179)) | ~v1_xboole_0(A_179))), inference(resolution, [status(thm)], [c_57, c_124])).
% 5.95/2.12  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.95/2.12  tff(c_1791, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_1783, c_4])).
% 5.95/2.12  tff(c_1827, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1806, c_1791])).
% 5.95/2.12  tff(c_1843, plain, (![A_180]: (k6_partfun1(A_180)='#skF_1' | ~v1_xboole_0(A_180))), inference(resolution, [status(thm)], [c_1835, c_1827])).
% 5.95/2.12  tff(c_1851, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_1784, c_1843])).
% 5.95/2.12  tff(c_1873, plain, (v2_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1851, c_58])).
% 5.95/2.12  tff(c_1882, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1817, c_1873])).
% 5.95/2.12  tff(c_1883, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_42])).
% 5.95/2.12  tff(c_1896, plain, (![C_188, A_189, B_190]: (v1_relat_1(C_188) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.95/2.12  tff(c_1909, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_1896])).
% 5.95/2.12  tff(c_1910, plain, (![C_191, B_192, A_193]: (v5_relat_1(C_191, B_192) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_193, B_192))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.95/2.12  tff(c_1922, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_1910])).
% 5.95/2.12  tff(c_2091, plain, (![A_209, B_210, D_211]: (r2_relset_1(A_209, B_210, D_211, D_211) | ~m1_subset_1(D_211, k1_zfmisc_1(k2_zfmisc_1(A_209, B_210))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.95/2.12  tff(c_2101, plain, (![A_21]: (r2_relset_1(A_21, A_21, k6_partfun1(A_21), k6_partfun1(A_21)))), inference(resolution, [status(thm)], [c_57, c_2091])).
% 5.95/2.12  tff(c_2104, plain, (![A_212, B_213, C_214]: (k2_relset_1(A_212, B_213, C_214)=k2_relat_1(C_214) | ~m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(A_212, B_213))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.95/2.12  tff(c_2120, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_2104])).
% 5.95/2.12  tff(c_2150, plain, (![D_216, C_217, A_218, B_219]: (D_216=C_217 | ~r2_relset_1(A_218, B_219, C_217, D_216) | ~m1_subset_1(D_216, k1_zfmisc_1(k2_zfmisc_1(A_218, B_219))) | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1(A_218, B_219))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.95/2.12  tff(c_2158, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_44, c_2150])).
% 5.95/2.12  tff(c_2173, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_2158])).
% 5.95/2.12  tff(c_2202, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2173])).
% 5.95/2.12  tff(c_2907, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_2202])).
% 5.95/2.12  tff(c_2911, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_46, c_2907])).
% 5.95/2.12  tff(c_2912, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2173])).
% 5.95/2.12  tff(c_4490, plain, (![A_325, B_326, C_327, D_328]: (k2_relset_1(A_325, B_326, C_327)=B_326 | ~r2_relset_1(B_326, B_326, k1_partfun1(B_326, A_325, A_325, B_326, D_328, C_327), k6_partfun1(B_326)) | ~m1_subset_1(D_328, k1_zfmisc_1(k2_zfmisc_1(B_326, A_325))) | ~v1_funct_2(D_328, B_326, A_325) | ~v1_funct_1(D_328) | ~m1_subset_1(C_327, k1_zfmisc_1(k2_zfmisc_1(A_325, B_326))) | ~v1_funct_2(C_327, A_325, B_326) | ~v1_funct_1(C_327))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.95/2.12  tff(c_4508, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2912, c_4490])).
% 5.95/2.12  tff(c_4516, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_56, c_54, c_52, c_2101, c_2120, c_4508])).
% 5.95/2.12  tff(c_26, plain, (![B_23]: (v2_funct_2(B_23, k2_relat_1(B_23)) | ~v5_relat_1(B_23, k2_relat_1(B_23)) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.95/2.12  tff(c_4521, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4516, c_26])).
% 5.95/2.12  tff(c_4525, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1909, c_1922, c_4516, c_4521])).
% 5.95/2.12  tff(c_4527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1883, c_4525])).
% 5.95/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.95/2.12  
% 5.95/2.12  Inference rules
% 5.95/2.12  ----------------------
% 5.95/2.12  #Ref     : 0
% 5.95/2.12  #Sup     : 1201
% 5.95/2.12  #Fact    : 0
% 5.95/2.12  #Define  : 0
% 5.95/2.12  #Split   : 20
% 5.95/2.12  #Chain   : 0
% 5.95/2.12  #Close   : 0
% 5.95/2.12  
% 5.95/2.12  Ordering : KBO
% 5.95/2.12  
% 5.95/2.12  Simplification rules
% 5.95/2.12  ----------------------
% 5.95/2.12  #Subsume      : 275
% 5.95/2.12  #Demod        : 634
% 5.95/2.12  #Tautology    : 249
% 5.95/2.12  #SimpNegUnit  : 4
% 5.95/2.12  #BackRed      : 41
% 5.95/2.12  
% 5.95/2.12  #Partial instantiations: 0
% 5.95/2.12  #Strategies tried      : 1
% 5.95/2.12  
% 5.95/2.12  Timing (in seconds)
% 5.95/2.12  ----------------------
% 5.95/2.12  Preprocessing        : 0.32
% 5.95/2.12  Parsing              : 0.16
% 5.95/2.12  CNF conversion       : 0.02
% 5.95/2.12  Main loop            : 1.01
% 5.95/2.12  Inferencing          : 0.31
% 5.95/2.12  Reduction            : 0.33
% 5.95/2.12  Demodulation         : 0.24
% 5.95/2.12  BG Simplification    : 0.04
% 5.95/2.12  Subsumption          : 0.23
% 5.95/2.12  Abstraction          : 0.04
% 5.95/2.12  MUC search           : 0.00
% 5.95/2.13  Cooper               : 0.00
% 5.95/2.13  Total                : 1.37
% 5.95/2.13  Index Insertion      : 0.00
% 5.95/2.13  Index Deletion       : 0.00
% 5.95/2.13  Index Matching       : 0.00
% 5.95/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
