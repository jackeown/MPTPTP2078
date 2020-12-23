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
% DateTime   : Thu Dec  3 10:12:24 EST 2020

% Result     : Theorem 7.09s
% Output     : CNFRefutation 7.09s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 876 expanded)
%              Number of leaves         :   43 ( 325 expanded)
%              Depth                    :   10
%              Number of atoms          :  303 (2697 expanded)
%              Number of equality atoms :   69 ( 352 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_156,negated_conjecture,(
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

tff(f_97,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_55,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_95,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_75,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_136,axiom,(
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

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_114,axiom,(
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

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_56,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_132,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_68,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_48,plain,(
    ! [A_33] : k6_relat_1(A_33) = k6_partfun1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_26,plain,(
    ! [A_13] : v2_funct_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_72,plain,(
    ! [A_13] : v2_funct_1(k6_partfun1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_26])).

tff(c_44,plain,(
    ! [C_29,D_30,B_28,F_32,A_27,E_31] :
      ( m1_subset_1(k1_partfun1(A_27,B_28,C_29,D_30,E_31,F_32),k1_zfmisc_1(k2_zfmisc_1(A_27,D_30)))
      | ~ m1_subset_1(F_32,k1_zfmisc_1(k2_zfmisc_1(C_29,D_30)))
      | ~ v1_funct_1(F_32)
      | ~ m1_subset_1(E_31,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_funct_1(E_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_38,plain,(
    ! [A_24] : m1_subset_1(k6_relat_1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_71,plain,(
    ! [A_24] : m1_subset_1(k6_partfun1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_38])).

tff(c_58,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_610,plain,(
    ! [D_114,C_115,A_116,B_117] :
      ( D_114 = C_115
      | ~ r2_relset_1(A_116,B_117,C_115,D_114)
      | ~ m1_subset_1(D_114,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117)))
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_620,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_610])).

tff(c_639,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_620])).

tff(c_657,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_639])).

tff(c_1027,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_657])).

tff(c_1034,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_1027])).

tff(c_1035,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_639])).

tff(c_1523,plain,(
    ! [B_249,D_251,E_248,C_250,A_247] :
      ( k1_xboole_0 = C_250
      | v2_funct_1(D_251)
      | ~ v2_funct_1(k1_partfun1(A_247,B_249,B_249,C_250,D_251,E_248))
      | ~ m1_subset_1(E_248,k1_zfmisc_1(k2_zfmisc_1(B_249,C_250)))
      | ~ v1_funct_2(E_248,B_249,C_250)
      | ~ v1_funct_1(E_248)
      | ~ m1_subset_1(D_251,k1_zfmisc_1(k2_zfmisc_1(A_247,B_249)))
      | ~ v1_funct_2(D_251,A_247,B_249)
      | ~ v1_funct_1(D_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1525,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1035,c_1523])).

tff(c_1527,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_62,c_60,c_72,c_1525])).

tff(c_1528,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_1527])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1561,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1528,c_8])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1559,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1528,c_1528,c_12])).

tff(c_151,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,B_58)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_171,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_151])).

tff(c_189,plain,(
    ! [B_60,A_61] :
      ( B_60 = A_61
      | ~ r1_tarski(B_60,A_61)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_202,plain,
    ( k2_zfmisc_1('#skF_2','#skF_1') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_171,c_189])).

tff(c_333,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_202])).

tff(c_1692,plain,(
    ~ r1_tarski('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1559,c_333])).

tff(c_1697,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1561,c_1692])).

tff(c_1698,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_1702,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1698,c_60])).

tff(c_2947,plain,(
    ! [D_430,C_431,A_432,B_433] :
      ( D_430 = C_431
      | ~ r2_relset_1(A_432,B_433,C_431,D_430)
      | ~ m1_subset_1(D_430,k1_zfmisc_1(k2_zfmisc_1(A_432,B_433)))
      | ~ m1_subset_1(C_431,k1_zfmisc_1(k2_zfmisc_1(A_432,B_433))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2955,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_2947])).

tff(c_2970,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_2955])).

tff(c_2987,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2970])).

tff(c_3366,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_2987])).

tff(c_3373,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_1702,c_1698,c_3366])).

tff(c_3374,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2970])).

tff(c_3809,plain,(
    ! [C_561,E_559,A_558,D_562,B_560] :
      ( k1_xboole_0 = C_561
      | v2_funct_1(D_562)
      | ~ v2_funct_1(k1_partfun1(A_558,B_560,B_560,C_561,D_562,E_559))
      | ~ m1_subset_1(E_559,k1_zfmisc_1(k2_zfmisc_1(B_560,C_561)))
      | ~ v1_funct_2(E_559,B_560,C_561)
      | ~ v1_funct_1(E_559)
      | ~ m1_subset_1(D_562,k1_zfmisc_1(k2_zfmisc_1(A_558,B_560)))
      | ~ v1_funct_2(D_562,A_558,B_560)
      | ~ v1_funct_1(D_562) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_3811,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3374,c_3809])).

tff(c_3813,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_62,c_1702,c_1698,c_72,c_3811])).

tff(c_3814,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_3813])).

tff(c_3848,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3814,c_8])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3845,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3814,c_3814,c_14])).

tff(c_172,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_151])).

tff(c_201,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_172,c_189])).

tff(c_1731,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_201])).

tff(c_4008,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3845,c_1731])).

tff(c_4013,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3848,c_4008])).

tff(c_4014,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_4017,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4014,c_66])).

tff(c_4475,plain,(
    ! [D_644,E_645,A_647,F_642,C_643,B_646] :
      ( m1_subset_1(k1_partfun1(A_647,B_646,C_643,D_644,E_645,F_642),k1_zfmisc_1(k2_zfmisc_1(A_647,D_644)))
      | ~ m1_subset_1(F_642,k1_zfmisc_1(k2_zfmisc_1(C_643,D_644)))
      | ~ v1_funct_1(F_642)
      | ~ m1_subset_1(E_645,k1_zfmisc_1(k2_zfmisc_1(A_647,B_646)))
      | ~ v1_funct_1(E_645) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_4252,plain,(
    ! [D_607,C_608,A_609,B_610] :
      ( D_607 = C_608
      | ~ r2_relset_1(A_609,B_610,C_608,D_607)
      | ~ m1_subset_1(D_607,k1_zfmisc_1(k2_zfmisc_1(A_609,B_610)))
      | ~ m1_subset_1(C_608,k1_zfmisc_1(k2_zfmisc_1(A_609,B_610))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4258,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_4252])).

tff(c_4269,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_4258])).

tff(c_4311,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_4269])).

tff(c_4478,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4475,c_4311])).

tff(c_4513,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_4017,c_4014,c_64,c_1702,c_1698,c_4478])).

tff(c_4514,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_4269])).

tff(c_4931,plain,(
    ! [A_706,E_707,D_710,C_709,B_708] :
      ( k1_xboole_0 = C_709
      | v2_funct_1(D_710)
      | ~ v2_funct_1(k1_partfun1(A_706,B_708,B_708,C_709,D_710,E_707))
      | ~ m1_subset_1(E_707,k1_zfmisc_1(k2_zfmisc_1(B_708,C_709)))
      | ~ v1_funct_2(E_707,B_708,C_709)
      | ~ v1_funct_1(E_707)
      | ~ m1_subset_1(D_710,k1_zfmisc_1(k2_zfmisc_1(A_706,B_708)))
      | ~ v1_funct_2(D_710,A_706,B_708)
      | ~ v1_funct_1(D_710) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_4933,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4514,c_4931])).

tff(c_4935,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_4017,c_4014,c_64,c_62,c_1702,c_1698,c_72,c_4933])).

tff(c_4936,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_4935])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4028,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_4014,c_10])).

tff(c_4048,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4028])).

tff(c_4961,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4936,c_4048])).

tff(c_4968,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4936,c_4936,c_14])).

tff(c_5136,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4968,c_4014])).

tff(c_5138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4961,c_5136])).

tff(c_5140,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4028])).

tff(c_111,plain,(
    ! [A_53] : k6_relat_1(A_53) = k6_partfun1(A_53) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_24,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_117,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_24])).

tff(c_128,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_72])).

tff(c_5148,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5140,c_128])).

tff(c_5157,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_5148])).

tff(c_5158,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_22,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_5216,plain,(
    ! [B_734,A_735] :
      ( v1_relat_1(B_734)
      | ~ m1_subset_1(B_734,k1_zfmisc_1(A_735))
      | ~ v1_relat_1(A_735) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_5228,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_5216])).

tff(c_5241,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_5228])).

tff(c_5344,plain,(
    ! [C_747,B_748,A_749] :
      ( v5_relat_1(C_747,B_748)
      | ~ m1_subset_1(C_747,k1_zfmisc_1(k2_zfmisc_1(A_749,B_748))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_5366,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_5344])).

tff(c_5450,plain,(
    ! [A_763,B_764,D_765] :
      ( r2_relset_1(A_763,B_764,D_765,D_765)
      | ~ m1_subset_1(D_765,k1_zfmisc_1(k2_zfmisc_1(A_763,B_764))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_5465,plain,(
    ! [A_24] : r2_relset_1(A_24,A_24,k6_partfun1(A_24),k6_partfun1(A_24)) ),
    inference(resolution,[status(thm)],[c_71,c_5450])).

tff(c_5479,plain,(
    ! [A_771,B_772,C_773] :
      ( k2_relset_1(A_771,B_772,C_773) = k2_relat_1(C_773)
      | ~ m1_subset_1(C_773,k1_zfmisc_1(k2_zfmisc_1(A_771,B_772))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_5501,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_5479])).

tff(c_5520,plain,(
    ! [D_775,C_776,A_777,B_778] :
      ( D_775 = C_776
      | ~ r2_relset_1(A_777,B_778,C_776,D_775)
      | ~ m1_subset_1(D_775,k1_zfmisc_1(k2_zfmisc_1(A_777,B_778)))
      | ~ m1_subset_1(C_776,k1_zfmisc_1(k2_zfmisc_1(A_777,B_778))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_5528,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_5520])).

tff(c_5543,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_5528])).

tff(c_5900,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_5543])).

tff(c_6007,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_5900])).

tff(c_6014,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_6007])).

tff(c_6015,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_5543])).

tff(c_6186,plain,(
    ! [A_878,B_879,C_880,D_881] :
      ( k2_relset_1(A_878,B_879,C_880) = B_879
      | ~ r2_relset_1(B_879,B_879,k1_partfun1(B_879,A_878,A_878,B_879,D_881,C_880),k6_partfun1(B_879))
      | ~ m1_subset_1(D_881,k1_zfmisc_1(k2_zfmisc_1(B_879,A_878)))
      | ~ v1_funct_2(D_881,B_879,A_878)
      | ~ v1_funct_1(D_881)
      | ~ m1_subset_1(C_880,k1_zfmisc_1(k2_zfmisc_1(A_878,B_879)))
      | ~ v1_funct_2(C_880,A_878,B_879)
      | ~ v1_funct_1(C_880) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_6189,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6015,c_6186])).

tff(c_6194,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_70,c_68,c_66,c_5465,c_5501,c_6189])).

tff(c_40,plain,(
    ! [B_26] :
      ( v2_funct_2(B_26,k2_relat_1(B_26))
      | ~ v5_relat_1(B_26,k2_relat_1(B_26))
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6203,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6194,c_40])).

tff(c_6210,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5241,c_5366,c_6194,c_6203])).

tff(c_6212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5158,c_6210])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:40:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.09/2.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.09/2.45  
% 7.09/2.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.09/2.45  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.09/2.45  
% 7.09/2.45  %Foreground sorts:
% 7.09/2.45  
% 7.09/2.45  
% 7.09/2.45  %Background operators:
% 7.09/2.45  
% 7.09/2.45  
% 7.09/2.45  %Foreground operators:
% 7.09/2.45  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.09/2.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.09/2.45  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.09/2.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.09/2.45  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.09/2.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.09/2.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.09/2.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.09/2.45  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.09/2.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.09/2.45  tff('#skF_2', type, '#skF_2': $i).
% 7.09/2.45  tff('#skF_3', type, '#skF_3': $i).
% 7.09/2.45  tff('#skF_1', type, '#skF_1': $i).
% 7.09/2.45  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 7.09/2.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.09/2.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.09/2.45  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.09/2.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.09/2.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.09/2.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.09/2.45  tff('#skF_4', type, '#skF_4': $i).
% 7.09/2.45  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.09/2.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.09/2.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.09/2.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.09/2.45  
% 7.09/2.48  tff(f_156, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 7.09/2.48  tff(f_97, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.09/2.48  tff(f_55, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 7.09/2.48  tff(f_95, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.09/2.48  tff(f_75, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 7.09/2.48  tff(f_73, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.09/2.48  tff(f_136, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 7.09/2.48  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.09/2.48  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.09/2.48  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.09/2.48  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.09/2.48  tff(f_53, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 7.09/2.48  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.09/2.48  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.09/2.48  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.09/2.48  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.09/2.48  tff(f_114, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 7.09/2.48  tff(f_83, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 7.09/2.48  tff(c_56, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_156])).
% 7.09/2.48  tff(c_132, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_56])).
% 7.09/2.48  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_156])).
% 7.09/2.48  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 7.09/2.48  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 7.09/2.48  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 7.09/2.48  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 7.09/2.48  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 7.09/2.48  tff(c_48, plain, (![A_33]: (k6_relat_1(A_33)=k6_partfun1(A_33))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.09/2.48  tff(c_26, plain, (![A_13]: (v2_funct_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.09/2.48  tff(c_72, plain, (![A_13]: (v2_funct_1(k6_partfun1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_26])).
% 7.09/2.48  tff(c_44, plain, (![C_29, D_30, B_28, F_32, A_27, E_31]: (m1_subset_1(k1_partfun1(A_27, B_28, C_29, D_30, E_31, F_32), k1_zfmisc_1(k2_zfmisc_1(A_27, D_30))) | ~m1_subset_1(F_32, k1_zfmisc_1(k2_zfmisc_1(C_29, D_30))) | ~v1_funct_1(F_32) | ~m1_subset_1(E_31, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~v1_funct_1(E_31))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.09/2.48  tff(c_38, plain, (![A_24]: (m1_subset_1(k6_relat_1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.09/2.48  tff(c_71, plain, (![A_24]: (m1_subset_1(k6_partfun1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_38])).
% 7.09/2.48  tff(c_58, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 7.09/2.48  tff(c_610, plain, (![D_114, C_115, A_116, B_117]: (D_114=C_115 | ~r2_relset_1(A_116, B_117, C_115, D_114) | ~m1_subset_1(D_114, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.09/2.48  tff(c_620, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_610])).
% 7.09/2.48  tff(c_639, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_620])).
% 7.09/2.48  tff(c_657, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_639])).
% 7.09/2.48  tff(c_1027, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_657])).
% 7.09/2.48  tff(c_1034, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_1027])).
% 7.09/2.48  tff(c_1035, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_639])).
% 7.09/2.48  tff(c_1523, plain, (![B_249, D_251, E_248, C_250, A_247]: (k1_xboole_0=C_250 | v2_funct_1(D_251) | ~v2_funct_1(k1_partfun1(A_247, B_249, B_249, C_250, D_251, E_248)) | ~m1_subset_1(E_248, k1_zfmisc_1(k2_zfmisc_1(B_249, C_250))) | ~v1_funct_2(E_248, B_249, C_250) | ~v1_funct_1(E_248) | ~m1_subset_1(D_251, k1_zfmisc_1(k2_zfmisc_1(A_247, B_249))) | ~v1_funct_2(D_251, A_247, B_249) | ~v1_funct_1(D_251))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.09/2.48  tff(c_1525, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1035, c_1523])).
% 7.09/2.48  tff(c_1527, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_62, c_60, c_72, c_1525])).
% 7.09/2.48  tff(c_1528, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_132, c_1527])).
% 7.09/2.48  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.09/2.48  tff(c_1561, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1528, c_8])).
% 7.09/2.48  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.09/2.48  tff(c_1559, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1528, c_1528, c_12])).
% 7.09/2.48  tff(c_151, plain, (![A_57, B_58]: (r1_tarski(A_57, B_58) | ~m1_subset_1(A_57, k1_zfmisc_1(B_58)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.09/2.48  tff(c_171, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_60, c_151])).
% 7.09/2.48  tff(c_189, plain, (![B_60, A_61]: (B_60=A_61 | ~r1_tarski(B_60, A_61) | ~r1_tarski(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.09/2.48  tff(c_202, plain, (k2_zfmisc_1('#skF_2', '#skF_1')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), '#skF_4')), inference(resolution, [status(thm)], [c_171, c_189])).
% 7.09/2.48  tff(c_333, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), '#skF_4')), inference(splitLeft, [status(thm)], [c_202])).
% 7.09/2.48  tff(c_1692, plain, (~r1_tarski('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1559, c_333])).
% 7.09/2.48  tff(c_1697, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1561, c_1692])).
% 7.09/2.48  tff(c_1698, plain, (k2_zfmisc_1('#skF_2', '#skF_1')='#skF_4'), inference(splitRight, [status(thm)], [c_202])).
% 7.09/2.48  tff(c_1702, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1698, c_60])).
% 7.09/2.48  tff(c_2947, plain, (![D_430, C_431, A_432, B_433]: (D_430=C_431 | ~r2_relset_1(A_432, B_433, C_431, D_430) | ~m1_subset_1(D_430, k1_zfmisc_1(k2_zfmisc_1(A_432, B_433))) | ~m1_subset_1(C_431, k1_zfmisc_1(k2_zfmisc_1(A_432, B_433))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.09/2.48  tff(c_2955, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_2947])).
% 7.09/2.48  tff(c_2970, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_2955])).
% 7.09/2.48  tff(c_2987, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2970])).
% 7.09/2.48  tff(c_3366, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_2987])).
% 7.09/2.48  tff(c_3373, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_1702, c_1698, c_3366])).
% 7.09/2.48  tff(c_3374, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2970])).
% 7.09/2.48  tff(c_3809, plain, (![C_561, E_559, A_558, D_562, B_560]: (k1_xboole_0=C_561 | v2_funct_1(D_562) | ~v2_funct_1(k1_partfun1(A_558, B_560, B_560, C_561, D_562, E_559)) | ~m1_subset_1(E_559, k1_zfmisc_1(k2_zfmisc_1(B_560, C_561))) | ~v1_funct_2(E_559, B_560, C_561) | ~v1_funct_1(E_559) | ~m1_subset_1(D_562, k1_zfmisc_1(k2_zfmisc_1(A_558, B_560))) | ~v1_funct_2(D_562, A_558, B_560) | ~v1_funct_1(D_562))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.09/2.48  tff(c_3811, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3374, c_3809])).
% 7.09/2.48  tff(c_3813, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_62, c_1702, c_1698, c_72, c_3811])).
% 7.09/2.48  tff(c_3814, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_132, c_3813])).
% 7.09/2.48  tff(c_3848, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_3814, c_8])).
% 7.09/2.48  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.09/2.48  tff(c_3845, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3814, c_3814, c_14])).
% 7.09/2.48  tff(c_172, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_151])).
% 7.09/2.48  tff(c_201, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_172, c_189])).
% 7.09/2.48  tff(c_1731, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_201])).
% 7.09/2.48  tff(c_4008, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3845, c_1731])).
% 7.09/2.48  tff(c_4013, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3848, c_4008])).
% 7.09/2.48  tff(c_4014, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_201])).
% 7.09/2.48  tff(c_4017, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4014, c_66])).
% 7.09/2.48  tff(c_4475, plain, (![D_644, E_645, A_647, F_642, C_643, B_646]: (m1_subset_1(k1_partfun1(A_647, B_646, C_643, D_644, E_645, F_642), k1_zfmisc_1(k2_zfmisc_1(A_647, D_644))) | ~m1_subset_1(F_642, k1_zfmisc_1(k2_zfmisc_1(C_643, D_644))) | ~v1_funct_1(F_642) | ~m1_subset_1(E_645, k1_zfmisc_1(k2_zfmisc_1(A_647, B_646))) | ~v1_funct_1(E_645))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.09/2.48  tff(c_4252, plain, (![D_607, C_608, A_609, B_610]: (D_607=C_608 | ~r2_relset_1(A_609, B_610, C_608, D_607) | ~m1_subset_1(D_607, k1_zfmisc_1(k2_zfmisc_1(A_609, B_610))) | ~m1_subset_1(C_608, k1_zfmisc_1(k2_zfmisc_1(A_609, B_610))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.09/2.48  tff(c_4258, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_4252])).
% 7.09/2.48  tff(c_4269, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_4258])).
% 7.09/2.48  tff(c_4311, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_4269])).
% 7.09/2.48  tff(c_4478, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_4475, c_4311])).
% 7.09/2.48  tff(c_4513, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_4017, c_4014, c_64, c_1702, c_1698, c_4478])).
% 7.09/2.48  tff(c_4514, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_4269])).
% 7.09/2.48  tff(c_4931, plain, (![A_706, E_707, D_710, C_709, B_708]: (k1_xboole_0=C_709 | v2_funct_1(D_710) | ~v2_funct_1(k1_partfun1(A_706, B_708, B_708, C_709, D_710, E_707)) | ~m1_subset_1(E_707, k1_zfmisc_1(k2_zfmisc_1(B_708, C_709))) | ~v1_funct_2(E_707, B_708, C_709) | ~v1_funct_1(E_707) | ~m1_subset_1(D_710, k1_zfmisc_1(k2_zfmisc_1(A_706, B_708))) | ~v1_funct_2(D_710, A_706, B_708) | ~v1_funct_1(D_710))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.09/2.48  tff(c_4933, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4514, c_4931])).
% 7.09/2.48  tff(c_4935, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_4017, c_4014, c_64, c_62, c_1702, c_1698, c_72, c_4933])).
% 7.09/2.48  tff(c_4936, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_132, c_4935])).
% 7.09/2.48  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.09/2.48  tff(c_4028, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_4014, c_10])).
% 7.09/2.48  tff(c_4048, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_4028])).
% 7.09/2.48  tff(c_4961, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4936, c_4048])).
% 7.09/2.48  tff(c_4968, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4936, c_4936, c_14])).
% 7.09/2.48  tff(c_5136, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4968, c_4014])).
% 7.09/2.48  tff(c_5138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4961, c_5136])).
% 7.09/2.48  tff(c_5140, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_4028])).
% 7.09/2.48  tff(c_111, plain, (![A_53]: (k6_relat_1(A_53)=k6_partfun1(A_53))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.09/2.48  tff(c_24, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.09/2.48  tff(c_117, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_111, c_24])).
% 7.09/2.48  tff(c_128, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_117, c_72])).
% 7.09/2.48  tff(c_5148, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5140, c_128])).
% 7.09/2.48  tff(c_5157, plain, $false, inference(negUnitSimplification, [status(thm)], [c_132, c_5148])).
% 7.09/2.48  tff(c_5158, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_56])).
% 7.09/2.48  tff(c_22, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.09/2.48  tff(c_5216, plain, (![B_734, A_735]: (v1_relat_1(B_734) | ~m1_subset_1(B_734, k1_zfmisc_1(A_735)) | ~v1_relat_1(A_735))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.09/2.48  tff(c_5228, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_60, c_5216])).
% 7.09/2.48  tff(c_5241, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_5228])).
% 7.09/2.48  tff(c_5344, plain, (![C_747, B_748, A_749]: (v5_relat_1(C_747, B_748) | ~m1_subset_1(C_747, k1_zfmisc_1(k2_zfmisc_1(A_749, B_748))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.09/2.48  tff(c_5366, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_5344])).
% 7.09/2.48  tff(c_5450, plain, (![A_763, B_764, D_765]: (r2_relset_1(A_763, B_764, D_765, D_765) | ~m1_subset_1(D_765, k1_zfmisc_1(k2_zfmisc_1(A_763, B_764))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.09/2.48  tff(c_5465, plain, (![A_24]: (r2_relset_1(A_24, A_24, k6_partfun1(A_24), k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_71, c_5450])).
% 7.09/2.48  tff(c_5479, plain, (![A_771, B_772, C_773]: (k2_relset_1(A_771, B_772, C_773)=k2_relat_1(C_773) | ~m1_subset_1(C_773, k1_zfmisc_1(k2_zfmisc_1(A_771, B_772))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.09/2.48  tff(c_5501, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_5479])).
% 7.09/2.48  tff(c_5520, plain, (![D_775, C_776, A_777, B_778]: (D_775=C_776 | ~r2_relset_1(A_777, B_778, C_776, D_775) | ~m1_subset_1(D_775, k1_zfmisc_1(k2_zfmisc_1(A_777, B_778))) | ~m1_subset_1(C_776, k1_zfmisc_1(k2_zfmisc_1(A_777, B_778))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.09/2.48  tff(c_5528, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_5520])).
% 7.09/2.48  tff(c_5543, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_5528])).
% 7.09/2.48  tff(c_5900, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_5543])).
% 7.09/2.48  tff(c_6007, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_5900])).
% 7.09/2.48  tff(c_6014, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_6007])).
% 7.09/2.48  tff(c_6015, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_5543])).
% 7.09/2.48  tff(c_6186, plain, (![A_878, B_879, C_880, D_881]: (k2_relset_1(A_878, B_879, C_880)=B_879 | ~r2_relset_1(B_879, B_879, k1_partfun1(B_879, A_878, A_878, B_879, D_881, C_880), k6_partfun1(B_879)) | ~m1_subset_1(D_881, k1_zfmisc_1(k2_zfmisc_1(B_879, A_878))) | ~v1_funct_2(D_881, B_879, A_878) | ~v1_funct_1(D_881) | ~m1_subset_1(C_880, k1_zfmisc_1(k2_zfmisc_1(A_878, B_879))) | ~v1_funct_2(C_880, A_878, B_879) | ~v1_funct_1(C_880))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.09/2.48  tff(c_6189, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6015, c_6186])).
% 7.09/2.48  tff(c_6194, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_70, c_68, c_66, c_5465, c_5501, c_6189])).
% 7.09/2.48  tff(c_40, plain, (![B_26]: (v2_funct_2(B_26, k2_relat_1(B_26)) | ~v5_relat_1(B_26, k2_relat_1(B_26)) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.09/2.48  tff(c_6203, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6194, c_40])).
% 7.09/2.48  tff(c_6210, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5241, c_5366, c_6194, c_6203])).
% 7.09/2.48  tff(c_6212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5158, c_6210])).
% 7.09/2.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.09/2.48  
% 7.09/2.48  Inference rules
% 7.09/2.48  ----------------------
% 7.09/2.48  #Ref     : 0
% 7.09/2.48  #Sup     : 1330
% 7.09/2.48  #Fact    : 0
% 7.09/2.48  #Define  : 0
% 7.09/2.48  #Split   : 26
% 7.09/2.48  #Chain   : 0
% 7.09/2.48  #Close   : 0
% 7.09/2.48  
% 7.09/2.48  Ordering : KBO
% 7.09/2.48  
% 7.09/2.48  Simplification rules
% 7.09/2.48  ----------------------
% 7.09/2.48  #Subsume      : 106
% 7.09/2.48  #Demod        : 1269
% 7.09/2.48  #Tautology    : 658
% 7.09/2.48  #SimpNegUnit  : 11
% 7.09/2.48  #BackRed      : 210
% 7.09/2.48  
% 7.09/2.48  #Partial instantiations: 0
% 7.09/2.48  #Strategies tried      : 1
% 7.09/2.48  
% 7.09/2.48  Timing (in seconds)
% 7.09/2.48  ----------------------
% 7.09/2.48  Preprocessing        : 0.35
% 7.09/2.48  Parsing              : 0.19
% 7.09/2.48  CNF conversion       : 0.03
% 7.09/2.48  Main loop            : 1.35
% 7.09/2.48  Inferencing          : 0.49
% 7.09/2.48  Reduction            : 0.48
% 7.09/2.48  Demodulation         : 0.35
% 7.09/2.48  BG Simplification    : 0.04
% 7.09/2.48  Subsumption          : 0.22
% 7.09/2.48  Abstraction          : 0.05
% 7.09/2.48  MUC search           : 0.00
% 7.09/2.48  Cooper               : 0.00
% 7.09/2.48  Total                : 1.76
% 7.09/2.48  Index Insertion      : 0.00
% 7.09/2.48  Index Deletion       : 0.00
% 7.09/2.48  Index Matching       : 0.00
% 7.09/2.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
