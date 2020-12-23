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
% DateTime   : Thu Dec  3 10:12:14 EST 2020

% Result     : Theorem 5.18s
% Output     : CNFRefutation 5.45s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 662 expanded)
%              Number of leaves         :   41 ( 264 expanded)
%              Depth                    :   13
%              Number of atoms          :  197 (2375 expanded)
%              Number of equality atoms :   39 ( 241 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(f_148,negated_conjecture,(
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

tff(f_89,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_41,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_83,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_128,axiom,(
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

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_106,axiom,(
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

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_48,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_99,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_62,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_60,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_54,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_40,plain,(
    ! [A_29] : k6_relat_1(A_29) = k6_partfun1(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_14,plain,(
    ! [A_6] : v2_funct_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_63,plain,(
    ! [A_6] : v2_funct_1(k6_partfun1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_14])).

tff(c_32,plain,(
    ! [E_26,F_27,A_22,B_23,D_25,C_24] :
      ( m1_subset_1(k1_partfun1(A_22,B_23,C_24,D_25,E_26,F_27),k1_zfmisc_1(k2_zfmisc_1(A_22,D_25)))
      | ~ m1_subset_1(F_27,k1_zfmisc_1(k2_zfmisc_1(C_24,D_25)))
      | ~ v1_funct_1(F_27)
      | ~ m1_subset_1(E_26,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_1(E_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_38,plain,(
    ! [A_28] : m1_subset_1(k6_partfun1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_50,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_450,plain,(
    ! [D_96,C_97,A_98,B_99] :
      ( D_96 = C_97
      | ~ r2_relset_1(A_98,B_99,C_97,D_96)
      | ~ m1_subset_1(D_96,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99)))
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_460,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_50,c_450])).

tff(c_479,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_460])).

tff(c_498,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_479])).

tff(c_825,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_498])).

tff(c_832,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_56,c_52,c_825])).

tff(c_833,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_479])).

tff(c_1258,plain,(
    ! [E_234,D_233,C_232,A_231,B_235] :
      ( k1_xboole_0 = C_232
      | v2_funct_1(D_233)
      | ~ v2_funct_1(k1_partfun1(A_231,B_235,B_235,C_232,D_233,E_234))
      | ~ m1_subset_1(E_234,k1_zfmisc_1(k2_zfmisc_1(B_235,C_232)))
      | ~ v1_funct_2(E_234,B_235,C_232)
      | ~ v1_funct_1(E_234)
      | ~ m1_subset_1(D_233,k1_zfmisc_1(k2_zfmisc_1(A_231,B_235)))
      | ~ v1_funct_2(D_233,A_231,B_235)
      | ~ v1_funct_1(D_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1260,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_833,c_1258])).

tff(c_1262,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_54,c_52,c_63,c_1260])).

tff(c_1263,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_1262])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1301,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1263,c_1263,c_6])).

tff(c_101,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | ~ m1_subset_1(A_48,k1_zfmisc_1(B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_109,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_52,c_101])).

tff(c_1457,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1301,c_109])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1623,plain,(
    ! [A_259] :
      ( A_259 = '#skF_1'
      | ~ r1_tarski(A_259,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1263,c_1263,c_2])).

tff(c_1633,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1457,c_1623])).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1300,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_1',B_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1263,c_1263,c_8])).

tff(c_108,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_101])).

tff(c_1400,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1300,c_108])).

tff(c_1634,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1400,c_1623])).

tff(c_1682,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1633,c_1634])).

tff(c_1686,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1682,c_99])).

tff(c_110,plain,(
    ! [A_50] : m1_subset_1(k6_partfun1(A_50),k1_zfmisc_1(k2_zfmisc_1(A_50,A_50))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_117,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_110])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_126,plain,(
    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_117,c_10])).

tff(c_130,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_126,c_2])).

tff(c_141,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_63])).

tff(c_1297,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1263,c_141])).

tff(c_1655,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1633,c_1297])).

tff(c_1698,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1686,c_1655])).

tff(c_1699,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1790,plain,(
    ! [C_269,A_270,B_271] :
      ( v1_relat_1(C_269)
      | ~ m1_subset_1(C_269,k1_zfmisc_1(k2_zfmisc_1(A_270,B_271))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1811,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_1790])).

tff(c_1843,plain,(
    ! [C_277,B_278,A_279] :
      ( v5_relat_1(C_277,B_278)
      | ~ m1_subset_1(C_277,k1_zfmisc_1(k2_zfmisc_1(A_279,B_278))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1866,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_1843])).

tff(c_1974,plain,(
    ! [A_295,B_296,D_297] :
      ( r2_relset_1(A_295,B_296,D_297,D_297)
      | ~ m1_subset_1(D_297,k1_zfmisc_1(k2_zfmisc_1(A_295,B_296))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1989,plain,(
    ! [A_28] : r2_relset_1(A_28,A_28,k6_partfun1(A_28),k6_partfun1(A_28)) ),
    inference(resolution,[status(thm)],[c_38,c_1974])).

tff(c_2003,plain,(
    ! [A_299,B_300,C_301] :
      ( k2_relset_1(A_299,B_300,C_301) = k2_relat_1(C_301)
      | ~ m1_subset_1(C_301,k1_zfmisc_1(k2_zfmisc_1(A_299,B_300))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2026,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_2003])).

tff(c_2045,plain,(
    ! [D_304,C_305,A_306,B_307] :
      ( D_304 = C_305
      | ~ r2_relset_1(A_306,B_307,C_305,D_304)
      | ~ m1_subset_1(D_304,k1_zfmisc_1(k2_zfmisc_1(A_306,B_307)))
      | ~ m1_subset_1(C_305,k1_zfmisc_1(k2_zfmisc_1(A_306,B_307))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2055,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_50,c_2045])).

tff(c_2074,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2055])).

tff(c_2086,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2074])).

tff(c_2396,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_2086])).

tff(c_2403,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_56,c_52,c_2396])).

tff(c_2404,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2074])).

tff(c_2811,plain,(
    ! [A_449,B_450,C_451,D_452] :
      ( k2_relset_1(A_449,B_450,C_451) = B_450
      | ~ r2_relset_1(B_450,B_450,k1_partfun1(B_450,A_449,A_449,B_450,D_452,C_451),k6_partfun1(B_450))
      | ~ m1_subset_1(D_452,k1_zfmisc_1(k2_zfmisc_1(B_450,A_449)))
      | ~ v1_funct_2(D_452,B_450,A_449)
      | ~ v1_funct_1(D_452)
      | ~ m1_subset_1(C_451,k1_zfmisc_1(k2_zfmisc_1(A_449,B_450)))
      | ~ v1_funct_2(C_451,A_449,B_450)
      | ~ v1_funct_1(C_451) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2814,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2404,c_2811])).

tff(c_2819,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_62,c_60,c_58,c_1989,c_2026,c_2814])).

tff(c_28,plain,(
    ! [B_21] :
      ( v2_funct_2(B_21,k2_relat_1(B_21))
      | ~ v5_relat_1(B_21,k2_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2828,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2819,c_28])).

tff(c_2835,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1811,c_1866,c_2819,c_2828])).

tff(c_2837,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1699,c_2835])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:11:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.18/1.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.45/1.97  
% 5.45/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.45/1.97  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.45/1.97  
% 5.45/1.97  %Foreground sorts:
% 5.45/1.97  
% 5.45/1.97  
% 5.45/1.97  %Background operators:
% 5.45/1.97  
% 5.45/1.97  
% 5.45/1.97  %Foreground operators:
% 5.45/1.97  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.45/1.97  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.45/1.97  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.45/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.45/1.97  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.45/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.45/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.45/1.97  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.45/1.97  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.45/1.97  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.45/1.97  tff('#skF_2', type, '#skF_2': $i).
% 5.45/1.97  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.45/1.97  tff('#skF_3', type, '#skF_3': $i).
% 5.45/1.97  tff('#skF_1', type, '#skF_1': $i).
% 5.45/1.97  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.45/1.97  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.45/1.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.45/1.97  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.45/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.45/1.97  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.45/1.97  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.45/1.97  tff('#skF_4', type, '#skF_4': $i).
% 5.45/1.97  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.45/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.45/1.97  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.45/1.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.45/1.97  
% 5.45/1.99  tff(f_148, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 5.45/1.99  tff(f_89, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.45/1.99  tff(f_41, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 5.45/1.99  tff(f_83, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.45/1.99  tff(f_87, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.45/1.99  tff(f_63, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.45/1.99  tff(f_128, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 5.45/1.99  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.45/1.99  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.45/1.99  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 5.45/1.99  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.45/1.99  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.45/1.99  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.45/1.99  tff(f_106, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 5.45/1.99  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 5.45/1.99  tff(c_48, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.45/1.99  tff(c_99, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_48])).
% 5.45/1.99  tff(c_62, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.45/1.99  tff(c_60, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.45/1.99  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.45/1.99  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.45/1.99  tff(c_54, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.45/1.99  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.45/1.99  tff(c_40, plain, (![A_29]: (k6_relat_1(A_29)=k6_partfun1(A_29))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.45/1.99  tff(c_14, plain, (![A_6]: (v2_funct_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.45/1.99  tff(c_63, plain, (![A_6]: (v2_funct_1(k6_partfun1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_14])).
% 5.45/1.99  tff(c_32, plain, (![E_26, F_27, A_22, B_23, D_25, C_24]: (m1_subset_1(k1_partfun1(A_22, B_23, C_24, D_25, E_26, F_27), k1_zfmisc_1(k2_zfmisc_1(A_22, D_25))) | ~m1_subset_1(F_27, k1_zfmisc_1(k2_zfmisc_1(C_24, D_25))) | ~v1_funct_1(F_27) | ~m1_subset_1(E_26, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_1(E_26))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.45/1.99  tff(c_38, plain, (![A_28]: (m1_subset_1(k6_partfun1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.45/1.99  tff(c_50, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.45/1.99  tff(c_450, plain, (![D_96, C_97, A_98, B_99]: (D_96=C_97 | ~r2_relset_1(A_98, B_99, C_97, D_96) | ~m1_subset_1(D_96, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.45/1.99  tff(c_460, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_50, c_450])).
% 5.45/1.99  tff(c_479, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_460])).
% 5.45/1.99  tff(c_498, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_479])).
% 5.45/1.99  tff(c_825, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_498])).
% 5.45/1.99  tff(c_832, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_56, c_52, c_825])).
% 5.45/1.99  tff(c_833, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_479])).
% 5.45/1.99  tff(c_1258, plain, (![E_234, D_233, C_232, A_231, B_235]: (k1_xboole_0=C_232 | v2_funct_1(D_233) | ~v2_funct_1(k1_partfun1(A_231, B_235, B_235, C_232, D_233, E_234)) | ~m1_subset_1(E_234, k1_zfmisc_1(k2_zfmisc_1(B_235, C_232))) | ~v1_funct_2(E_234, B_235, C_232) | ~v1_funct_1(E_234) | ~m1_subset_1(D_233, k1_zfmisc_1(k2_zfmisc_1(A_231, B_235))) | ~v1_funct_2(D_233, A_231, B_235) | ~v1_funct_1(D_233))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.45/1.99  tff(c_1260, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_833, c_1258])).
% 5.45/1.99  tff(c_1262, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_54, c_52, c_63, c_1260])).
% 5.45/1.99  tff(c_1263, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_99, c_1262])).
% 5.45/1.99  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.45/1.99  tff(c_1301, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1263, c_1263, c_6])).
% 5.45/1.99  tff(c_101, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | ~m1_subset_1(A_48, k1_zfmisc_1(B_49)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.45/1.99  tff(c_109, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_52, c_101])).
% 5.45/1.99  tff(c_1457, plain, (r1_tarski('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1301, c_109])).
% 5.45/2.00  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.45/2.00  tff(c_1623, plain, (![A_259]: (A_259='#skF_1' | ~r1_tarski(A_259, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1263, c_1263, c_2])).
% 5.45/2.00  tff(c_1633, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_1457, c_1623])).
% 5.45/2.00  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.45/2.00  tff(c_1300, plain, (![B_3]: (k2_zfmisc_1('#skF_1', B_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1263, c_1263, c_8])).
% 5.45/2.00  tff(c_108, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_101])).
% 5.45/2.00  tff(c_1400, plain, (r1_tarski('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1300, c_108])).
% 5.45/2.00  tff(c_1634, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_1400, c_1623])).
% 5.45/2.00  tff(c_1682, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1633, c_1634])).
% 5.45/2.00  tff(c_1686, plain, (~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1682, c_99])).
% 5.45/2.00  tff(c_110, plain, (![A_50]: (m1_subset_1(k6_partfun1(A_50), k1_zfmisc_1(k2_zfmisc_1(A_50, A_50))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.45/2.00  tff(c_117, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_110])).
% 5.45/2.00  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.45/2.00  tff(c_126, plain, (r1_tarski(k6_partfun1(k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_117, c_10])).
% 5.45/2.00  tff(c_130, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_126, c_2])).
% 5.45/2.00  tff(c_141, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_130, c_63])).
% 5.45/2.00  tff(c_1297, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1263, c_141])).
% 5.45/2.00  tff(c_1655, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1633, c_1297])).
% 5.45/2.00  tff(c_1698, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1686, c_1655])).
% 5.45/2.00  tff(c_1699, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 5.45/2.00  tff(c_1790, plain, (![C_269, A_270, B_271]: (v1_relat_1(C_269) | ~m1_subset_1(C_269, k1_zfmisc_1(k2_zfmisc_1(A_270, B_271))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.45/2.00  tff(c_1811, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_1790])).
% 5.45/2.00  tff(c_1843, plain, (![C_277, B_278, A_279]: (v5_relat_1(C_277, B_278) | ~m1_subset_1(C_277, k1_zfmisc_1(k2_zfmisc_1(A_279, B_278))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.45/2.00  tff(c_1866, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_52, c_1843])).
% 5.45/2.00  tff(c_1974, plain, (![A_295, B_296, D_297]: (r2_relset_1(A_295, B_296, D_297, D_297) | ~m1_subset_1(D_297, k1_zfmisc_1(k2_zfmisc_1(A_295, B_296))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.45/2.00  tff(c_1989, plain, (![A_28]: (r2_relset_1(A_28, A_28, k6_partfun1(A_28), k6_partfun1(A_28)))), inference(resolution, [status(thm)], [c_38, c_1974])).
% 5.45/2.00  tff(c_2003, plain, (![A_299, B_300, C_301]: (k2_relset_1(A_299, B_300, C_301)=k2_relat_1(C_301) | ~m1_subset_1(C_301, k1_zfmisc_1(k2_zfmisc_1(A_299, B_300))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.45/2.00  tff(c_2026, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_2003])).
% 5.45/2.00  tff(c_2045, plain, (![D_304, C_305, A_306, B_307]: (D_304=C_305 | ~r2_relset_1(A_306, B_307, C_305, D_304) | ~m1_subset_1(D_304, k1_zfmisc_1(k2_zfmisc_1(A_306, B_307))) | ~m1_subset_1(C_305, k1_zfmisc_1(k2_zfmisc_1(A_306, B_307))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.45/2.00  tff(c_2055, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_50, c_2045])).
% 5.45/2.00  tff(c_2074, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2055])).
% 5.45/2.00  tff(c_2086, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2074])).
% 5.45/2.00  tff(c_2396, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_2086])).
% 5.45/2.00  tff(c_2403, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_56, c_52, c_2396])).
% 5.45/2.00  tff(c_2404, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2074])).
% 5.45/2.00  tff(c_2811, plain, (![A_449, B_450, C_451, D_452]: (k2_relset_1(A_449, B_450, C_451)=B_450 | ~r2_relset_1(B_450, B_450, k1_partfun1(B_450, A_449, A_449, B_450, D_452, C_451), k6_partfun1(B_450)) | ~m1_subset_1(D_452, k1_zfmisc_1(k2_zfmisc_1(B_450, A_449))) | ~v1_funct_2(D_452, B_450, A_449) | ~v1_funct_1(D_452) | ~m1_subset_1(C_451, k1_zfmisc_1(k2_zfmisc_1(A_449, B_450))) | ~v1_funct_2(C_451, A_449, B_450) | ~v1_funct_1(C_451))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.45/2.00  tff(c_2814, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2404, c_2811])).
% 5.45/2.00  tff(c_2819, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_62, c_60, c_58, c_1989, c_2026, c_2814])).
% 5.45/2.00  tff(c_28, plain, (![B_21]: (v2_funct_2(B_21, k2_relat_1(B_21)) | ~v5_relat_1(B_21, k2_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.45/2.00  tff(c_2828, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2819, c_28])).
% 5.45/2.00  tff(c_2835, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1811, c_1866, c_2819, c_2828])).
% 5.45/2.00  tff(c_2837, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1699, c_2835])).
% 5.45/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.45/2.00  
% 5.45/2.00  Inference rules
% 5.45/2.00  ----------------------
% 5.45/2.00  #Ref     : 0
% 5.45/2.00  #Sup     : 609
% 5.45/2.00  #Fact    : 0
% 5.45/2.00  #Define  : 0
% 5.45/2.00  #Split   : 8
% 5.45/2.00  #Chain   : 0
% 5.45/2.00  #Close   : 0
% 5.45/2.00  
% 5.45/2.00  Ordering : KBO
% 5.45/2.00  
% 5.45/2.00  Simplification rules
% 5.45/2.00  ----------------------
% 5.45/2.00  #Subsume      : 58
% 5.45/2.00  #Demod        : 552
% 5.45/2.00  #Tautology    : 243
% 5.45/2.00  #SimpNegUnit  : 6
% 5.45/2.00  #BackRed      : 136
% 5.45/2.00  
% 5.45/2.00  #Partial instantiations: 0
% 5.45/2.00  #Strategies tried      : 1
% 5.45/2.00  
% 5.45/2.00  Timing (in seconds)
% 5.45/2.00  ----------------------
% 5.45/2.00  Preprocessing        : 0.36
% 5.45/2.00  Parsing              : 0.19
% 5.45/2.00  CNF conversion       : 0.02
% 5.45/2.00  Main loop            : 0.86
% 5.45/2.00  Inferencing          : 0.30
% 5.45/2.00  Reduction            : 0.30
% 5.45/2.00  Demodulation         : 0.22
% 5.45/2.00  BG Simplification    : 0.03
% 5.45/2.00  Subsumption          : 0.14
% 5.45/2.00  Abstraction          : 0.03
% 5.45/2.00  MUC search           : 0.00
% 5.45/2.00  Cooper               : 0.00
% 5.45/2.00  Total                : 1.26
% 5.45/2.00  Index Insertion      : 0.00
% 5.45/2.00  Index Deletion       : 0.00
% 5.45/2.00  Index Matching       : 0.00
% 5.45/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
