%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:12 EST 2020

% Result     : Theorem 6.87s
% Output     : CNFRefutation 7.21s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 873 expanded)
%              Number of leaves         :   42 ( 324 expanded)
%              Depth                    :   10
%              Number of atoms          :  297 (2691 expanded)
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

tff(f_151,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_92,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_46,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_90,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_70,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_131,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_109,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_54,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_125,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_68,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_66,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_60,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_46,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_22,plain,(
    ! [A_8] : v2_funct_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_70,plain,(
    ! [A_8] : v2_funct_1(k6_partfun1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_22])).

tff(c_42,plain,(
    ! [A_25,F_30,E_29,C_27,D_28,B_26] :
      ( m1_subset_1(k1_partfun1(A_25,B_26,C_27,D_28,E_29,F_30),k1_zfmisc_1(k2_zfmisc_1(A_25,D_28)))
      | ~ m1_subset_1(F_30,k1_zfmisc_1(k2_zfmisc_1(C_27,D_28)))
      | ~ v1_funct_1(F_30)
      | ~ m1_subset_1(E_29,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_1(E_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_36,plain,(
    ! [A_22] : m1_subset_1(k6_relat_1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_69,plain,(
    ! [A_22] : m1_subset_1(k6_partfun1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_36])).

tff(c_56,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_479,plain,(
    ! [D_98,C_99,A_100,B_101] :
      ( D_98 = C_99
      | ~ r2_relset_1(A_100,B_101,C_99,D_98)
      | ~ m1_subset_1(D_98,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_485,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_56,c_479])).

tff(c_496,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_485])).

tff(c_522,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_496])).

tff(c_847,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_522])).

tff(c_854,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_62,c_58,c_847])).

tff(c_855,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_496])).

tff(c_1236,plain,(
    ! [A_209,B_210,E_212,C_213,D_211] :
      ( k1_xboole_0 = C_213
      | v2_funct_1(D_211)
      | ~ v2_funct_1(k1_partfun1(A_209,B_210,B_210,C_213,D_211,E_212))
      | ~ m1_subset_1(E_212,k1_zfmisc_1(k2_zfmisc_1(B_210,C_213)))
      | ~ v1_funct_2(E_212,B_210,C_213)
      | ~ v1_funct_1(E_212)
      | ~ m1_subset_1(D_211,k1_zfmisc_1(k2_zfmisc_1(A_209,B_210)))
      | ~ v1_funct_2(D_211,A_209,B_210)
      | ~ v1_funct_1(D_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1238,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_855,c_1236])).

tff(c_1240,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_62,c_60,c_58,c_70,c_1238])).

tff(c_1241,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_1240])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1273,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1241,c_8])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1272,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1241,c_1241,c_12])).

tff(c_127,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(A_52,B_53)
      | ~ m1_subset_1(A_52,k1_zfmisc_1(B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_138,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_58,c_127])).

tff(c_164,plain,(
    ! [B_55,A_56] :
      ( B_55 = A_56
      | ~ r1_tarski(B_55,A_56)
      | ~ r1_tarski(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_174,plain,
    ( k2_zfmisc_1('#skF_2','#skF_1') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_138,c_164])).

tff(c_195,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_174])).

tff(c_1404,plain,(
    ~ r1_tarski('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1272,c_195])).

tff(c_1409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1273,c_1404])).

tff(c_1410,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_1413,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1410,c_58])).

tff(c_1880,plain,(
    ! [D_286,C_287,A_288,B_289] :
      ( D_286 = C_287
      | ~ r2_relset_1(A_288,B_289,C_287,D_286)
      | ~ m1_subset_1(D_286,k1_zfmisc_1(k2_zfmisc_1(A_288,B_289)))
      | ~ m1_subset_1(C_287,k1_zfmisc_1(k2_zfmisc_1(A_288,B_289))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1890,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_56,c_1880])).

tff(c_1909,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_1890])).

tff(c_1964,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1909])).

tff(c_2182,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_1964])).

tff(c_2189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_62,c_1413,c_1410,c_2182])).

tff(c_2190,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1909])).

tff(c_2588,plain,(
    ! [B_394,C_397,A_393,E_396,D_395] :
      ( k1_xboole_0 = C_397
      | v2_funct_1(D_395)
      | ~ v2_funct_1(k1_partfun1(A_393,B_394,B_394,C_397,D_395,E_396))
      | ~ m1_subset_1(E_396,k1_zfmisc_1(k2_zfmisc_1(B_394,C_397)))
      | ~ v1_funct_2(E_396,B_394,C_397)
      | ~ v1_funct_1(E_396)
      | ~ m1_subset_1(D_395,k1_zfmisc_1(k2_zfmisc_1(A_393,B_394)))
      | ~ v1_funct_2(D_395,A_393,B_394)
      | ~ v1_funct_1(D_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2590,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2190,c_2588])).

tff(c_2592,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_62,c_60,c_1413,c_1410,c_70,c_2590])).

tff(c_2593,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_2592])).

tff(c_2627,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2593,c_8])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2625,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2593,c_2593,c_14])).

tff(c_139,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_64,c_127])).

tff(c_173,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_139,c_164])).

tff(c_1481,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_173])).

tff(c_2768,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2625,c_1481])).

tff(c_2773,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2627,c_2768])).

tff(c_2774,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_2777,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2774,c_64])).

tff(c_4412,plain,(
    ! [B_634,F_633,D_630,E_635,A_631,C_632] :
      ( m1_subset_1(k1_partfun1(A_631,B_634,C_632,D_630,E_635,F_633),k1_zfmisc_1(k2_zfmisc_1(A_631,D_630)))
      | ~ m1_subset_1(F_633,k1_zfmisc_1(k2_zfmisc_1(C_632,D_630)))
      | ~ v1_funct_1(F_633)
      | ~ m1_subset_1(E_635,k1_zfmisc_1(k2_zfmisc_1(A_631,B_634)))
      | ~ v1_funct_1(E_635) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4195,plain,(
    ! [D_596,C_597,A_598,B_599] :
      ( D_596 = C_597
      | ~ r2_relset_1(A_598,B_599,C_597,D_596)
      | ~ m1_subset_1(D_596,k1_zfmisc_1(k2_zfmisc_1(A_598,B_599)))
      | ~ m1_subset_1(C_597,k1_zfmisc_1(k2_zfmisc_1(A_598,B_599))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4201,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_56,c_4195])).

tff(c_4212,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_4201])).

tff(c_4227,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_4212])).

tff(c_4415,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4412,c_4227])).

tff(c_4450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2777,c_2774,c_62,c_1413,c_1410,c_4415])).

tff(c_4451,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_4212])).

tff(c_4870,plain,(
    ! [E_698,D_697,C_699,B_696,A_695] :
      ( k1_xboole_0 = C_699
      | v2_funct_1(D_697)
      | ~ v2_funct_1(k1_partfun1(A_695,B_696,B_696,C_699,D_697,E_698))
      | ~ m1_subset_1(E_698,k1_zfmisc_1(k2_zfmisc_1(B_696,C_699)))
      | ~ v1_funct_2(E_698,B_696,C_699)
      | ~ v1_funct_1(E_698)
      | ~ m1_subset_1(D_697,k1_zfmisc_1(k2_zfmisc_1(A_695,B_696)))
      | ~ v1_funct_2(D_697,A_695,B_696)
      | ~ v1_funct_1(D_697) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_4872,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4451,c_4870])).

tff(c_4874,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_2777,c_2774,c_62,c_60,c_1413,c_1410,c_70,c_4872])).

tff(c_4875,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_4874])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2784,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2774,c_10])).

tff(c_2917,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2784])).

tff(c_4901,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4875,c_2917])).

tff(c_4911,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4875,c_4875,c_14])).

tff(c_5069,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4911,c_2774])).

tff(c_5071,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4901,c_5069])).

tff(c_5073,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2784])).

tff(c_103,plain,(
    ! [A_49] : k6_relat_1(A_49) = k6_partfun1(A_49) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_20,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_109,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_20])).

tff(c_120,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_70])).

tff(c_5083,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5073,c_120])).

tff(c_5092,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_5083])).

tff(c_5093,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_5150,plain,(
    ! [C_720,A_721,B_722] :
      ( v1_relat_1(C_720)
      | ~ m1_subset_1(C_720,k1_zfmisc_1(k2_zfmisc_1(A_721,B_722))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_5171,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_5150])).

tff(c_5281,plain,(
    ! [C_736,B_737,A_738] :
      ( v5_relat_1(C_736,B_737)
      | ~ m1_subset_1(C_736,k1_zfmisc_1(k2_zfmisc_1(A_738,B_737))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_5304,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_5281])).

tff(c_5363,plain,(
    ! [A_749,B_750,D_751] :
      ( r2_relset_1(A_749,B_750,D_751,D_751)
      | ~ m1_subset_1(D_751,k1_zfmisc_1(k2_zfmisc_1(A_749,B_750))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_5378,plain,(
    ! [A_22] : r2_relset_1(A_22,A_22,k6_partfun1(A_22),k6_partfun1(A_22)) ),
    inference(resolution,[status(thm)],[c_69,c_5363])).

tff(c_5438,plain,(
    ! [A_759,B_760,C_761] :
      ( k2_relset_1(A_759,B_760,C_761) = k2_relat_1(C_761)
      | ~ m1_subset_1(C_761,k1_zfmisc_1(k2_zfmisc_1(A_759,B_760))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_5461,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_5438])).

tff(c_5485,plain,(
    ! [D_764,C_765,A_766,B_767] :
      ( D_764 = C_765
      | ~ r2_relset_1(A_766,B_767,C_765,D_764)
      | ~ m1_subset_1(D_764,k1_zfmisc_1(k2_zfmisc_1(A_766,B_767)))
      | ~ m1_subset_1(C_765,k1_zfmisc_1(k2_zfmisc_1(A_766,B_767))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_5495,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_56,c_5485])).

tff(c_5514,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_5495])).

tff(c_5526,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_5514])).

tff(c_5866,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_5526])).

tff(c_5873,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_62,c_58,c_5866])).

tff(c_5874,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_5514])).

tff(c_6386,plain,(
    ! [A_906,B_907,C_908,D_909] :
      ( k2_relset_1(A_906,B_907,C_908) = B_907
      | ~ r2_relset_1(B_907,B_907,k1_partfun1(B_907,A_906,A_906,B_907,D_909,C_908),k6_partfun1(B_907))
      | ~ m1_subset_1(D_909,k1_zfmisc_1(k2_zfmisc_1(B_907,A_906)))
      | ~ v1_funct_2(D_909,B_907,A_906)
      | ~ v1_funct_1(D_909)
      | ~ m1_subset_1(C_908,k1_zfmisc_1(k2_zfmisc_1(A_906,B_907)))
      | ~ v1_funct_2(C_908,A_906,B_907)
      | ~ v1_funct_1(C_908) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_6389,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5874,c_6386])).

tff(c_6394,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_68,c_66,c_64,c_5378,c_5461,c_6389])).

tff(c_38,plain,(
    ! [B_24] :
      ( v2_funct_2(B_24,k2_relat_1(B_24))
      | ~ v5_relat_1(B_24,k2_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6403,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6394,c_38])).

tff(c_6410,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5171,c_5304,c_6394,c_6403])).

tff(c_6412,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5093,c_6410])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:19:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.87/2.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.87/2.50  
% 6.87/2.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.21/2.51  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.21/2.51  
% 7.21/2.51  %Foreground sorts:
% 7.21/2.51  
% 7.21/2.51  
% 7.21/2.51  %Background operators:
% 7.21/2.51  
% 7.21/2.51  
% 7.21/2.51  %Foreground operators:
% 7.21/2.51  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.21/2.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.21/2.51  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.21/2.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.21/2.51  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.21/2.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.21/2.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.21/2.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.21/2.51  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.21/2.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.21/2.51  tff('#skF_2', type, '#skF_2': $i).
% 7.21/2.51  tff('#skF_3', type, '#skF_3': $i).
% 7.21/2.51  tff('#skF_1', type, '#skF_1': $i).
% 7.21/2.51  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 7.21/2.51  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.21/2.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.21/2.51  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.21/2.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.21/2.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.21/2.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.21/2.51  tff('#skF_4', type, '#skF_4': $i).
% 7.21/2.51  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.21/2.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.21/2.51  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.21/2.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.21/2.51  
% 7.21/2.53  tff(f_151, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 7.21/2.53  tff(f_92, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.21/2.53  tff(f_46, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 7.21/2.53  tff(f_90, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.21/2.53  tff(f_70, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 7.21/2.53  tff(f_68, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.21/2.53  tff(f_131, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 7.21/2.53  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.21/2.53  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.21/2.53  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.21/2.53  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.21/2.53  tff(f_44, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 7.21/2.53  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.21/2.53  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.21/2.53  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.21/2.53  tff(f_109, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 7.21/2.53  tff(f_78, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 7.21/2.53  tff(c_54, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.21/2.53  tff(c_125, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_54])).
% 7.21/2.53  tff(c_68, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.21/2.53  tff(c_66, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.21/2.53  tff(c_64, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.21/2.53  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.21/2.53  tff(c_60, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.21/2.53  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.21/2.53  tff(c_46, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.21/2.53  tff(c_22, plain, (![A_8]: (v2_funct_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.21/2.53  tff(c_70, plain, (![A_8]: (v2_funct_1(k6_partfun1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_22])).
% 7.21/2.53  tff(c_42, plain, (![A_25, F_30, E_29, C_27, D_28, B_26]: (m1_subset_1(k1_partfun1(A_25, B_26, C_27, D_28, E_29, F_30), k1_zfmisc_1(k2_zfmisc_1(A_25, D_28))) | ~m1_subset_1(F_30, k1_zfmisc_1(k2_zfmisc_1(C_27, D_28))) | ~v1_funct_1(F_30) | ~m1_subset_1(E_29, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_1(E_29))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.21/2.53  tff(c_36, plain, (![A_22]: (m1_subset_1(k6_relat_1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.21/2.53  tff(c_69, plain, (![A_22]: (m1_subset_1(k6_partfun1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_36])).
% 7.21/2.53  tff(c_56, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.21/2.53  tff(c_479, plain, (![D_98, C_99, A_100, B_101]: (D_98=C_99 | ~r2_relset_1(A_100, B_101, C_99, D_98) | ~m1_subset_1(D_98, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.21/2.53  tff(c_485, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_56, c_479])).
% 7.21/2.53  tff(c_496, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_485])).
% 7.21/2.53  tff(c_522, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_496])).
% 7.21/2.53  tff(c_847, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_522])).
% 7.21/2.53  tff(c_854, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_62, c_58, c_847])).
% 7.21/2.53  tff(c_855, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_496])).
% 7.21/2.53  tff(c_1236, plain, (![A_209, B_210, E_212, C_213, D_211]: (k1_xboole_0=C_213 | v2_funct_1(D_211) | ~v2_funct_1(k1_partfun1(A_209, B_210, B_210, C_213, D_211, E_212)) | ~m1_subset_1(E_212, k1_zfmisc_1(k2_zfmisc_1(B_210, C_213))) | ~v1_funct_2(E_212, B_210, C_213) | ~v1_funct_1(E_212) | ~m1_subset_1(D_211, k1_zfmisc_1(k2_zfmisc_1(A_209, B_210))) | ~v1_funct_2(D_211, A_209, B_210) | ~v1_funct_1(D_211))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.21/2.53  tff(c_1238, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_855, c_1236])).
% 7.21/2.53  tff(c_1240, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_62, c_60, c_58, c_70, c_1238])).
% 7.21/2.53  tff(c_1241, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_125, c_1240])).
% 7.21/2.53  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.21/2.53  tff(c_1273, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1241, c_8])).
% 7.21/2.53  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.21/2.53  tff(c_1272, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1241, c_1241, c_12])).
% 7.21/2.53  tff(c_127, plain, (![A_52, B_53]: (r1_tarski(A_52, B_53) | ~m1_subset_1(A_52, k1_zfmisc_1(B_53)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.21/2.53  tff(c_138, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_58, c_127])).
% 7.21/2.53  tff(c_164, plain, (![B_55, A_56]: (B_55=A_56 | ~r1_tarski(B_55, A_56) | ~r1_tarski(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.21/2.53  tff(c_174, plain, (k2_zfmisc_1('#skF_2', '#skF_1')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), '#skF_4')), inference(resolution, [status(thm)], [c_138, c_164])).
% 7.21/2.53  tff(c_195, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), '#skF_4')), inference(splitLeft, [status(thm)], [c_174])).
% 7.21/2.53  tff(c_1404, plain, (~r1_tarski('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1272, c_195])).
% 7.21/2.53  tff(c_1409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1273, c_1404])).
% 7.21/2.53  tff(c_1410, plain, (k2_zfmisc_1('#skF_2', '#skF_1')='#skF_4'), inference(splitRight, [status(thm)], [c_174])).
% 7.21/2.53  tff(c_1413, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1410, c_58])).
% 7.21/2.53  tff(c_1880, plain, (![D_286, C_287, A_288, B_289]: (D_286=C_287 | ~r2_relset_1(A_288, B_289, C_287, D_286) | ~m1_subset_1(D_286, k1_zfmisc_1(k2_zfmisc_1(A_288, B_289))) | ~m1_subset_1(C_287, k1_zfmisc_1(k2_zfmisc_1(A_288, B_289))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.21/2.53  tff(c_1890, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_56, c_1880])).
% 7.21/2.53  tff(c_1909, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_1890])).
% 7.21/2.53  tff(c_1964, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1909])).
% 7.21/2.53  tff(c_2182, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_1964])).
% 7.21/2.53  tff(c_2189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_62, c_1413, c_1410, c_2182])).
% 7.21/2.53  tff(c_2190, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1909])).
% 7.21/2.53  tff(c_2588, plain, (![B_394, C_397, A_393, E_396, D_395]: (k1_xboole_0=C_397 | v2_funct_1(D_395) | ~v2_funct_1(k1_partfun1(A_393, B_394, B_394, C_397, D_395, E_396)) | ~m1_subset_1(E_396, k1_zfmisc_1(k2_zfmisc_1(B_394, C_397))) | ~v1_funct_2(E_396, B_394, C_397) | ~v1_funct_1(E_396) | ~m1_subset_1(D_395, k1_zfmisc_1(k2_zfmisc_1(A_393, B_394))) | ~v1_funct_2(D_395, A_393, B_394) | ~v1_funct_1(D_395))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.21/2.53  tff(c_2590, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2190, c_2588])).
% 7.21/2.53  tff(c_2592, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_62, c_60, c_1413, c_1410, c_70, c_2590])).
% 7.21/2.53  tff(c_2593, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_125, c_2592])).
% 7.21/2.53  tff(c_2627, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2593, c_8])).
% 7.21/2.53  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.21/2.53  tff(c_2625, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2593, c_2593, c_14])).
% 7.21/2.53  tff(c_139, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_64, c_127])).
% 7.21/2.53  tff(c_173, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_139, c_164])).
% 7.21/2.53  tff(c_1481, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_173])).
% 7.21/2.53  tff(c_2768, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2625, c_1481])).
% 7.21/2.53  tff(c_2773, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2627, c_2768])).
% 7.21/2.53  tff(c_2774, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_173])).
% 7.21/2.53  tff(c_2777, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2774, c_64])).
% 7.21/2.53  tff(c_4412, plain, (![B_634, F_633, D_630, E_635, A_631, C_632]: (m1_subset_1(k1_partfun1(A_631, B_634, C_632, D_630, E_635, F_633), k1_zfmisc_1(k2_zfmisc_1(A_631, D_630))) | ~m1_subset_1(F_633, k1_zfmisc_1(k2_zfmisc_1(C_632, D_630))) | ~v1_funct_1(F_633) | ~m1_subset_1(E_635, k1_zfmisc_1(k2_zfmisc_1(A_631, B_634))) | ~v1_funct_1(E_635))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.21/2.53  tff(c_4195, plain, (![D_596, C_597, A_598, B_599]: (D_596=C_597 | ~r2_relset_1(A_598, B_599, C_597, D_596) | ~m1_subset_1(D_596, k1_zfmisc_1(k2_zfmisc_1(A_598, B_599))) | ~m1_subset_1(C_597, k1_zfmisc_1(k2_zfmisc_1(A_598, B_599))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.21/2.53  tff(c_4201, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_56, c_4195])).
% 7.21/2.53  tff(c_4212, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_4201])).
% 7.21/2.53  tff(c_4227, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_4212])).
% 7.21/2.53  tff(c_4415, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_4412, c_4227])).
% 7.21/2.53  tff(c_4450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_2777, c_2774, c_62, c_1413, c_1410, c_4415])).
% 7.21/2.53  tff(c_4451, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_4212])).
% 7.21/2.53  tff(c_4870, plain, (![E_698, D_697, C_699, B_696, A_695]: (k1_xboole_0=C_699 | v2_funct_1(D_697) | ~v2_funct_1(k1_partfun1(A_695, B_696, B_696, C_699, D_697, E_698)) | ~m1_subset_1(E_698, k1_zfmisc_1(k2_zfmisc_1(B_696, C_699))) | ~v1_funct_2(E_698, B_696, C_699) | ~v1_funct_1(E_698) | ~m1_subset_1(D_697, k1_zfmisc_1(k2_zfmisc_1(A_695, B_696))) | ~v1_funct_2(D_697, A_695, B_696) | ~v1_funct_1(D_697))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.21/2.53  tff(c_4872, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4451, c_4870])).
% 7.21/2.53  tff(c_4874, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_2777, c_2774, c_62, c_60, c_1413, c_1410, c_70, c_4872])).
% 7.21/2.53  tff(c_4875, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_125, c_4874])).
% 7.21/2.53  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.21/2.53  tff(c_2784, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2774, c_10])).
% 7.21/2.53  tff(c_2917, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_2784])).
% 7.21/2.53  tff(c_4901, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4875, c_2917])).
% 7.21/2.53  tff(c_4911, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4875, c_4875, c_14])).
% 7.21/2.53  tff(c_5069, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4911, c_2774])).
% 7.21/2.53  tff(c_5071, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4901, c_5069])).
% 7.21/2.53  tff(c_5073, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_2784])).
% 7.21/2.53  tff(c_103, plain, (![A_49]: (k6_relat_1(A_49)=k6_partfun1(A_49))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.21/2.53  tff(c_20, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.21/2.53  tff(c_109, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_103, c_20])).
% 7.21/2.53  tff(c_120, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_109, c_70])).
% 7.21/2.53  tff(c_5083, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5073, c_120])).
% 7.21/2.53  tff(c_5092, plain, $false, inference(negUnitSimplification, [status(thm)], [c_125, c_5083])).
% 7.21/2.53  tff(c_5093, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_54])).
% 7.21/2.53  tff(c_5150, plain, (![C_720, A_721, B_722]: (v1_relat_1(C_720) | ~m1_subset_1(C_720, k1_zfmisc_1(k2_zfmisc_1(A_721, B_722))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.21/2.53  tff(c_5171, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_5150])).
% 7.21/2.53  tff(c_5281, plain, (![C_736, B_737, A_738]: (v5_relat_1(C_736, B_737) | ~m1_subset_1(C_736, k1_zfmisc_1(k2_zfmisc_1(A_738, B_737))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.21/2.53  tff(c_5304, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_5281])).
% 7.21/2.53  tff(c_5363, plain, (![A_749, B_750, D_751]: (r2_relset_1(A_749, B_750, D_751, D_751) | ~m1_subset_1(D_751, k1_zfmisc_1(k2_zfmisc_1(A_749, B_750))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.21/2.53  tff(c_5378, plain, (![A_22]: (r2_relset_1(A_22, A_22, k6_partfun1(A_22), k6_partfun1(A_22)))), inference(resolution, [status(thm)], [c_69, c_5363])).
% 7.21/2.53  tff(c_5438, plain, (![A_759, B_760, C_761]: (k2_relset_1(A_759, B_760, C_761)=k2_relat_1(C_761) | ~m1_subset_1(C_761, k1_zfmisc_1(k2_zfmisc_1(A_759, B_760))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.21/2.53  tff(c_5461, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_5438])).
% 7.21/2.53  tff(c_5485, plain, (![D_764, C_765, A_766, B_767]: (D_764=C_765 | ~r2_relset_1(A_766, B_767, C_765, D_764) | ~m1_subset_1(D_764, k1_zfmisc_1(k2_zfmisc_1(A_766, B_767))) | ~m1_subset_1(C_765, k1_zfmisc_1(k2_zfmisc_1(A_766, B_767))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.21/2.53  tff(c_5495, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_56, c_5485])).
% 7.21/2.53  tff(c_5514, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_5495])).
% 7.21/2.53  tff(c_5526, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_5514])).
% 7.21/2.53  tff(c_5866, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_5526])).
% 7.21/2.53  tff(c_5873, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_62, c_58, c_5866])).
% 7.21/2.53  tff(c_5874, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_5514])).
% 7.21/2.53  tff(c_6386, plain, (![A_906, B_907, C_908, D_909]: (k2_relset_1(A_906, B_907, C_908)=B_907 | ~r2_relset_1(B_907, B_907, k1_partfun1(B_907, A_906, A_906, B_907, D_909, C_908), k6_partfun1(B_907)) | ~m1_subset_1(D_909, k1_zfmisc_1(k2_zfmisc_1(B_907, A_906))) | ~v1_funct_2(D_909, B_907, A_906) | ~v1_funct_1(D_909) | ~m1_subset_1(C_908, k1_zfmisc_1(k2_zfmisc_1(A_906, B_907))) | ~v1_funct_2(C_908, A_906, B_907) | ~v1_funct_1(C_908))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.21/2.53  tff(c_6389, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5874, c_6386])).
% 7.21/2.53  tff(c_6394, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_68, c_66, c_64, c_5378, c_5461, c_6389])).
% 7.21/2.53  tff(c_38, plain, (![B_24]: (v2_funct_2(B_24, k2_relat_1(B_24)) | ~v5_relat_1(B_24, k2_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.21/2.53  tff(c_6403, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6394, c_38])).
% 7.21/2.53  tff(c_6410, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5171, c_5304, c_6394, c_6403])).
% 7.21/2.53  tff(c_6412, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5093, c_6410])).
% 7.21/2.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.21/2.53  
% 7.21/2.53  Inference rules
% 7.21/2.53  ----------------------
% 7.21/2.53  #Ref     : 0
% 7.21/2.53  #Sup     : 1404
% 7.21/2.53  #Fact    : 0
% 7.21/2.53  #Define  : 0
% 7.21/2.53  #Split   : 24
% 7.21/2.53  #Chain   : 0
% 7.21/2.53  #Close   : 0
% 7.21/2.53  
% 7.21/2.53  Ordering : KBO
% 7.21/2.53  
% 7.21/2.53  Simplification rules
% 7.21/2.53  ----------------------
% 7.21/2.53  #Subsume      : 129
% 7.21/2.53  #Demod        : 1149
% 7.21/2.53  #Tautology    : 636
% 7.21/2.53  #SimpNegUnit  : 9
% 7.21/2.53  #BackRed      : 182
% 7.21/2.53  
% 7.21/2.53  #Partial instantiations: 0
% 7.21/2.53  #Strategies tried      : 1
% 7.21/2.53  
% 7.21/2.53  Timing (in seconds)
% 7.21/2.53  ----------------------
% 7.21/2.53  Preprocessing        : 0.37
% 7.21/2.53  Parsing              : 0.20
% 7.21/2.53  CNF conversion       : 0.02
% 7.21/2.53  Main loop            : 1.36
% 7.21/2.53  Inferencing          : 0.47
% 7.21/2.53  Reduction            : 0.49
% 7.21/2.53  Demodulation         : 0.35
% 7.21/2.53  BG Simplification    : 0.05
% 7.21/2.53  Subsumption          : 0.24
% 7.21/2.53  Abstraction          : 0.05
% 7.21/2.54  MUC search           : 0.00
% 7.21/2.54  Cooper               : 0.00
% 7.21/2.54  Total                : 1.78
% 7.21/2.54  Index Insertion      : 0.00
% 7.21/2.54  Index Deletion       : 0.00
% 7.21/2.54  Index Matching       : 0.00
% 7.21/2.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
