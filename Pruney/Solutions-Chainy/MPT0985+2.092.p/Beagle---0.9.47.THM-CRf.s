%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:40 EST 2020

% Result     : Theorem 8.68s
% Output     : CNFRefutation 8.78s
% Verified   : 
% Statistics : Number of formulae       :  161 (1120 expanded)
%              Number of leaves         :   34 ( 399 expanded)
%              Depth                    :   16
%              Number of atoms          :  322 (3734 expanded)
%              Number of equality atoms :   58 (1047 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_110,axiom,(
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

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_122,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_15646,plain,(
    ! [A_1483,B_1484,C_1485] :
      ( k1_relset_1(A_1483,B_1484,C_1485) = k1_relat_1(C_1485)
      | ~ m1_subset_1(C_1485,k1_zfmisc_1(k2_zfmisc_1(A_1483,B_1484))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_15663,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_15646])).

tff(c_15737,plain,(
    ! [A_1496,B_1497,C_1498] :
      ( m1_subset_1(k1_relset_1(A_1496,B_1497,C_1498),k1_zfmisc_1(A_1496))
      | ~ m1_subset_1(C_1498,k1_zfmisc_1(k2_zfmisc_1(A_1496,B_1497))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_15766,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_15663,c_15737])).

tff(c_15778,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_15766])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_15851,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_15778,c_12])).

tff(c_181,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_194,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_181])).

tff(c_66,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_60,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_26,plain,(
    ! [A_14] :
      ( k2_relat_1(k2_funct_1(A_14)) = k1_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_167,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(A_56,B_57)
      | ~ m1_subset_1(A_56,k1_zfmisc_1(B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_178,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_167])).

tff(c_329,plain,(
    ! [A_88,B_89,C_90] :
      ( k1_relset_1(A_88,B_89,C_90) = k1_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_342,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_329])).

tff(c_10922,plain,(
    ! [B_1053,A_1054,C_1055] :
      ( k1_xboole_0 = B_1053
      | k1_relset_1(A_1054,B_1053,C_1055) = A_1054
      | ~ v1_funct_2(C_1055,A_1054,B_1053)
      | ~ m1_subset_1(C_1055,k1_zfmisc_1(k2_zfmisc_1(A_1054,B_1053))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_10936,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_10922])).

tff(c_10946,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_342,c_10936])).

tff(c_10949,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_10946])).

tff(c_425,plain,(
    ! [A_106,B_107,C_108] :
      ( m1_subset_1(k1_relset_1(A_106,B_107,C_108),k1_zfmisc_1(A_106))
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_454,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_425])).

tff(c_464,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_454])).

tff(c_531,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_464,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_549,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_531,c_2])).

tff(c_10665,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_549])).

tff(c_10950,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10949,c_10665])).

tff(c_10958,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10950])).

tff(c_10959,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_10946])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10666,plain,(
    ! [C_1025,A_1026] :
      ( k1_xboole_0 = C_1025
      | ~ v1_funct_2(C_1025,A_1026,k1_xboole_0)
      | k1_xboole_0 = A_1026
      | ~ m1_subset_1(C_1025,k1_zfmisc_1(k2_zfmisc_1(A_1026,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_10680,plain,(
    ! [A_5,A_1026] :
      ( k1_xboole_0 = A_5
      | ~ v1_funct_2(A_5,A_1026,k1_xboole_0)
      | k1_xboole_0 = A_1026
      | ~ r1_tarski(A_5,k2_zfmisc_1(A_1026,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_14,c_10666])).

tff(c_11208,plain,(
    ! [A_1075,A_1076] :
      ( A_1075 = '#skF_2'
      | ~ v1_funct_2(A_1075,A_1076,'#skF_2')
      | A_1076 = '#skF_2'
      | ~ r1_tarski(A_1075,k2_zfmisc_1(A_1076,'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10959,c_10959,c_10959,c_10959,c_10680])).

tff(c_11223,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_178,c_11208])).

tff(c_11233,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_11223])).

tff(c_11235,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_11233])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10977,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10959,c_8])).

tff(c_11249,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11235,c_10977])).

tff(c_11279,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11249,c_10665])).

tff(c_11280,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_11233])).

tff(c_11295,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11280,c_10977])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_343,plain,(
    ! [A_88,B_89] : k1_relset_1(A_88,B_89,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_329])).

tff(c_451,plain,(
    ! [A_88,B_89] :
      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_88))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_425])).

tff(c_465,plain,(
    ! [A_109] : m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_109)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_451])).

tff(c_492,plain,(
    ! [A_110] : r1_tarski(k1_relat_1(k1_xboole_0),A_110) ),
    inference(resolution,[status(thm)],[c_465,c_12])).

tff(c_214,plain,(
    ! [B_66,A_67] :
      ( B_66 = A_67
      | ~ r1_tarski(B_66,A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_226,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_214])).

tff(c_517,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_492,c_226])).

tff(c_10969,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10959,c_10959,c_517])).

tff(c_11294,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11280,c_11280,c_10969])).

tff(c_24,plain,(
    ! [A_13] :
      ( v1_relat_1(k2_funct_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_107,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_120,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_107])).

tff(c_156,plain,(
    ! [A_53] :
      ( v1_funct_1(k2_funct_1(A_53))
      | ~ v2_funct_1(A_53)
      | ~ v1_funct_1(A_53)
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_56,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_78,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_159,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_156,c_78])).

tff(c_163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_66,c_60,c_159])).

tff(c_165,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_58,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_355,plain,(
    ! [A_93,B_94,C_95] :
      ( k2_relset_1(A_93,B_94,C_95) = k2_relat_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_362,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_355])).

tff(c_369,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_362])).

tff(c_11299,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11280,c_369])).

tff(c_28,plain,(
    ! [A_14] :
      ( k1_relat_1(k2_funct_1(A_14)) = k2_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_564,plain,(
    ! [B_114,A_115] :
      ( v1_funct_2(B_114,k1_relat_1(B_114),A_115)
      | ~ r1_tarski(k2_relat_1(B_114),A_115)
      | ~ v1_funct_1(B_114)
      | ~ v1_relat_1(B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_12922,plain,(
    ! [A_1230,A_1231] :
      ( v1_funct_2(k2_funct_1(A_1230),k2_relat_1(A_1230),A_1231)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_1230)),A_1231)
      | ~ v1_funct_1(k2_funct_1(A_1230))
      | ~ v1_relat_1(k2_funct_1(A_1230))
      | ~ v2_funct_1(A_1230)
      | ~ v1_funct_1(A_1230)
      | ~ v1_relat_1(A_1230) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_564])).

tff(c_12925,plain,(
    ! [A_1231] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',A_1231)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_1231)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11299,c_12922])).

tff(c_12930,plain,(
    ! [A_1231] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',A_1231)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_1231)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_66,c_60,c_165,c_12925])).

tff(c_12931,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_12930])).

tff(c_12934,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_12931])).

tff(c_12938,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_66,c_60,c_12934])).

tff(c_12940,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_12930])).

tff(c_10802,plain,(
    ! [B_1041,A_1042] :
      ( m1_subset_1(B_1041,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1041),A_1042)))
      | ~ r1_tarski(k2_relat_1(B_1041),A_1042)
      | ~ v1_funct_1(B_1041)
      | ~ v1_relat_1(B_1041) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_13224,plain,(
    ! [A_1263,A_1264] :
      ( m1_subset_1(k2_funct_1(A_1263),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1263),A_1264)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_1263)),A_1264)
      | ~ v1_funct_1(k2_funct_1(A_1263))
      | ~ v1_relat_1(k2_funct_1(A_1263))
      | ~ v2_funct_1(A_1263)
      | ~ v1_funct_1(A_1263)
      | ~ v1_relat_1(A_1263) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_10802])).

tff(c_13259,plain,(
    ! [A_1264] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_1264)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_1264)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11299,c_13224])).

tff(c_13278,plain,(
    ! [A_1265] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_1265)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_1265) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_66,c_60,c_12940,c_165,c_13259])).

tff(c_164,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_242,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_11304,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11280,c_242])).

tff(c_13333,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_13278,c_11304])).

tff(c_13350,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_13333])).

tff(c_13353,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_66,c_60,c_11295,c_11294,c_13350])).

tff(c_13354,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_549])).

tff(c_15124,plain,(
    ! [A_1435,A_1436] :
      ( v1_funct_2(k2_funct_1(A_1435),k2_relat_1(A_1435),A_1436)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_1435)),A_1436)
      | ~ v1_funct_1(k2_funct_1(A_1435))
      | ~ v1_relat_1(k2_funct_1(A_1435))
      | ~ v2_funct_1(A_1435)
      | ~ v1_funct_1(A_1435)
      | ~ v1_relat_1(A_1435) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_564])).

tff(c_15127,plain,(
    ! [A_1436] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_1436)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_1436)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_15124])).

tff(c_15132,plain,(
    ! [A_1436] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_1436)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_1436)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_66,c_60,c_165,c_15127])).

tff(c_15133,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_15132])).

tff(c_15136,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_15133])).

tff(c_15140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_66,c_60,c_15136])).

tff(c_15142,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_15132])).

tff(c_13529,plain,(
    ! [B_1283,A_1284] :
      ( m1_subset_1(B_1283,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1283),A_1284)))
      | ~ r1_tarski(k2_relat_1(B_1283),A_1284)
      | ~ v1_funct_1(B_1283)
      | ~ v1_relat_1(B_1283) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_15358,plain,(
    ! [A_1461,A_1462] :
      ( m1_subset_1(k2_funct_1(A_1461),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1461),A_1462)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_1461)),A_1462)
      | ~ v1_funct_1(k2_funct_1(A_1461))
      | ~ v1_relat_1(k2_funct_1(A_1461))
      | ~ v2_funct_1(A_1461)
      | ~ v1_funct_1(A_1461)
      | ~ v1_relat_1(A_1461) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_13529])).

tff(c_15393,plain,(
    ! [A_1462] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_1462)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_1462)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_15358])).

tff(c_15471,plain,(
    ! [A_1464] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_1464)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_1464) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_66,c_60,c_15142,c_165,c_15393])).

tff(c_15518,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_15471,c_242])).

tff(c_15524,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_15518])).

tff(c_15527,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_66,c_60,c_6,c_13354,c_15524])).

tff(c_15529,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_30,plain,(
    ! [C_17,A_15,B_16] :
      ( v1_relat_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_15536,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_15529,c_30])).

tff(c_15702,plain,(
    ! [A_1491,B_1492,C_1493] :
      ( k2_relset_1(A_1491,B_1492,C_1493) = k2_relat_1(C_1493)
      | ~ m1_subset_1(C_1493,k1_zfmisc_1(k2_zfmisc_1(A_1491,B_1492))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_15712,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_15702])).

tff(c_15720,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_15712])).

tff(c_15661,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_15529,c_15646])).

tff(c_15760,plain,
    ( m1_subset_1(k1_relat_1(k2_funct_1('#skF_3')),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_15661,c_15737])).

tff(c_15774,plain,(
    m1_subset_1(k1_relat_1(k2_funct_1('#skF_3')),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15529,c_15760])).

tff(c_15893,plain,(
    r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_15774,c_12])).

tff(c_15918,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_15893,c_2])).

tff(c_15975,plain,(
    ~ r1_tarski('#skF_2',k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_15918])).

tff(c_15978,plain,
    ( ~ r1_tarski('#skF_2',k2_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_15975])).

tff(c_15981,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_66,c_60,c_6,c_15720,c_15978])).

tff(c_15982,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_15918])).

tff(c_52,plain,(
    ! [B_31,A_30] :
      ( v1_funct_2(B_31,k1_relat_1(B_31),A_30)
      | ~ r1_tarski(k2_relat_1(B_31),A_30)
      | ~ v1_funct_1(B_31)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_16011,plain,(
    ! [A_30] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_30)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_30)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15982,c_52])).

tff(c_16037,plain,(
    ! [A_1515] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_1515)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_1515) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15536,c_165,c_16011])).

tff(c_16040,plain,(
    ! [A_1515] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_1515)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_1515)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_16037])).

tff(c_16053,plain,(
    ! [A_1516] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_1516)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_1516) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_66,c_60,c_16040])).

tff(c_15528,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_16056,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_16053,c_15528])).

tff(c_16060,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15851,c_16056])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:39:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.68/3.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.78/3.42  
% 8.78/3.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.78/3.43  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 8.78/3.43  
% 8.78/3.43  %Foreground sorts:
% 8.78/3.43  
% 8.78/3.43  
% 8.78/3.43  %Background operators:
% 8.78/3.43  
% 8.78/3.43  
% 8.78/3.43  %Foreground operators:
% 8.78/3.43  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.78/3.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.78/3.43  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.78/3.43  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.78/3.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.78/3.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.78/3.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.78/3.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.78/3.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.78/3.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.78/3.43  tff('#skF_2', type, '#skF_2': $i).
% 8.78/3.43  tff('#skF_3', type, '#skF_3': $i).
% 8.78/3.43  tff('#skF_1', type, '#skF_1': $i).
% 8.78/3.43  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.78/3.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.78/3.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.78/3.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.78/3.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.78/3.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.78/3.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.78/3.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.78/3.43  
% 8.78/3.45  tff(f_139, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 8.78/3.45  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.78/3.45  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 8.78/3.45  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.78/3.45  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.78/3.45  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 8.78/3.45  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.78/3.45  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 8.78/3.45  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.78/3.45  tff(f_35, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 8.78/3.45  tff(f_66, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 8.78/3.45  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.78/3.45  tff(f_122, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 8.78/3.45  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.78/3.45  tff(c_15646, plain, (![A_1483, B_1484, C_1485]: (k1_relset_1(A_1483, B_1484, C_1485)=k1_relat_1(C_1485) | ~m1_subset_1(C_1485, k1_zfmisc_1(k2_zfmisc_1(A_1483, B_1484))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.78/3.45  tff(c_15663, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_15646])).
% 8.78/3.45  tff(c_15737, plain, (![A_1496, B_1497, C_1498]: (m1_subset_1(k1_relset_1(A_1496, B_1497, C_1498), k1_zfmisc_1(A_1496)) | ~m1_subset_1(C_1498, k1_zfmisc_1(k2_zfmisc_1(A_1496, B_1497))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.78/3.45  tff(c_15766, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_15663, c_15737])).
% 8.78/3.45  tff(c_15778, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_15766])).
% 8.78/3.45  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.78/3.45  tff(c_15851, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_15778, c_12])).
% 8.78/3.45  tff(c_181, plain, (![C_58, A_59, B_60]: (v1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.78/3.45  tff(c_194, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_181])).
% 8.78/3.45  tff(c_66, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.78/3.45  tff(c_60, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.78/3.45  tff(c_26, plain, (![A_14]: (k2_relat_1(k2_funct_1(A_14))=k1_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.78/3.45  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.78/3.45  tff(c_64, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.78/3.45  tff(c_167, plain, (![A_56, B_57]: (r1_tarski(A_56, B_57) | ~m1_subset_1(A_56, k1_zfmisc_1(B_57)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.78/3.45  tff(c_178, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_62, c_167])).
% 8.78/3.45  tff(c_329, plain, (![A_88, B_89, C_90]: (k1_relset_1(A_88, B_89, C_90)=k1_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.78/3.45  tff(c_342, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_329])).
% 8.78/3.45  tff(c_10922, plain, (![B_1053, A_1054, C_1055]: (k1_xboole_0=B_1053 | k1_relset_1(A_1054, B_1053, C_1055)=A_1054 | ~v1_funct_2(C_1055, A_1054, B_1053) | ~m1_subset_1(C_1055, k1_zfmisc_1(k2_zfmisc_1(A_1054, B_1053))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 8.78/3.45  tff(c_10936, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_10922])).
% 8.78/3.45  tff(c_10946, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_342, c_10936])).
% 8.78/3.45  tff(c_10949, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_10946])).
% 8.78/3.45  tff(c_425, plain, (![A_106, B_107, C_108]: (m1_subset_1(k1_relset_1(A_106, B_107, C_108), k1_zfmisc_1(A_106)) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.78/3.45  tff(c_454, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_342, c_425])).
% 8.78/3.45  tff(c_464, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_454])).
% 8.78/3.45  tff(c_531, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_464, c_12])).
% 8.78/3.45  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.78/3.45  tff(c_549, plain, (k1_relat_1('#skF_3')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_531, c_2])).
% 8.78/3.45  tff(c_10665, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_549])).
% 8.78/3.45  tff(c_10950, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10949, c_10665])).
% 8.78/3.45  tff(c_10958, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_10950])).
% 8.78/3.45  tff(c_10959, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_10946])).
% 8.78/3.45  tff(c_14, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.78/3.45  tff(c_10666, plain, (![C_1025, A_1026]: (k1_xboole_0=C_1025 | ~v1_funct_2(C_1025, A_1026, k1_xboole_0) | k1_xboole_0=A_1026 | ~m1_subset_1(C_1025, k1_zfmisc_1(k2_zfmisc_1(A_1026, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 8.78/3.45  tff(c_10680, plain, (![A_5, A_1026]: (k1_xboole_0=A_5 | ~v1_funct_2(A_5, A_1026, k1_xboole_0) | k1_xboole_0=A_1026 | ~r1_tarski(A_5, k2_zfmisc_1(A_1026, k1_xboole_0)))), inference(resolution, [status(thm)], [c_14, c_10666])).
% 8.78/3.45  tff(c_11208, plain, (![A_1075, A_1076]: (A_1075='#skF_2' | ~v1_funct_2(A_1075, A_1076, '#skF_2') | A_1076='#skF_2' | ~r1_tarski(A_1075, k2_zfmisc_1(A_1076, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_10959, c_10959, c_10959, c_10959, c_10680])).
% 8.78/3.45  tff(c_11223, plain, ('#skF_2'='#skF_3' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_178, c_11208])).
% 8.78/3.45  tff(c_11233, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_11223])).
% 8.78/3.45  tff(c_11235, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_11233])).
% 8.78/3.45  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.78/3.45  tff(c_10977, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_10959, c_8])).
% 8.78/3.45  tff(c_11249, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_11235, c_10977])).
% 8.78/3.45  tff(c_11279, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11249, c_10665])).
% 8.78/3.45  tff(c_11280, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_11233])).
% 8.78/3.45  tff(c_11295, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_11280, c_10977])).
% 8.78/3.45  tff(c_10, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.78/3.45  tff(c_343, plain, (![A_88, B_89]: (k1_relset_1(A_88, B_89, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_329])).
% 8.78/3.45  tff(c_451, plain, (![A_88, B_89]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_88)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(superposition, [status(thm), theory('equality')], [c_343, c_425])).
% 8.78/3.45  tff(c_465, plain, (![A_109]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_109)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_451])).
% 8.78/3.45  tff(c_492, plain, (![A_110]: (r1_tarski(k1_relat_1(k1_xboole_0), A_110))), inference(resolution, [status(thm)], [c_465, c_12])).
% 8.78/3.45  tff(c_214, plain, (![B_66, A_67]: (B_66=A_67 | ~r1_tarski(B_66, A_67) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.78/3.45  tff(c_226, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_214])).
% 8.78/3.45  tff(c_517, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_492, c_226])).
% 8.78/3.45  tff(c_10969, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10959, c_10959, c_517])).
% 8.78/3.45  tff(c_11294, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11280, c_11280, c_10969])).
% 8.78/3.45  tff(c_24, plain, (![A_13]: (v1_relat_1(k2_funct_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.78/3.45  tff(c_107, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.78/3.45  tff(c_120, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_107])).
% 8.78/3.45  tff(c_156, plain, (![A_53]: (v1_funct_1(k2_funct_1(A_53)) | ~v2_funct_1(A_53) | ~v1_funct_1(A_53) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.78/3.45  tff(c_56, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.78/3.45  tff(c_78, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_56])).
% 8.78/3.45  tff(c_159, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_156, c_78])).
% 8.78/3.45  tff(c_163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_120, c_66, c_60, c_159])).
% 8.78/3.45  tff(c_165, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_56])).
% 8.78/3.45  tff(c_58, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.78/3.45  tff(c_355, plain, (![A_93, B_94, C_95]: (k2_relset_1(A_93, B_94, C_95)=k2_relat_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.78/3.45  tff(c_362, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_355])).
% 8.78/3.45  tff(c_369, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_362])).
% 8.78/3.45  tff(c_11299, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11280, c_369])).
% 8.78/3.45  tff(c_28, plain, (![A_14]: (k1_relat_1(k2_funct_1(A_14))=k2_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.78/3.45  tff(c_564, plain, (![B_114, A_115]: (v1_funct_2(B_114, k1_relat_1(B_114), A_115) | ~r1_tarski(k2_relat_1(B_114), A_115) | ~v1_funct_1(B_114) | ~v1_relat_1(B_114))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.78/3.45  tff(c_12922, plain, (![A_1230, A_1231]: (v1_funct_2(k2_funct_1(A_1230), k2_relat_1(A_1230), A_1231) | ~r1_tarski(k2_relat_1(k2_funct_1(A_1230)), A_1231) | ~v1_funct_1(k2_funct_1(A_1230)) | ~v1_relat_1(k2_funct_1(A_1230)) | ~v2_funct_1(A_1230) | ~v1_funct_1(A_1230) | ~v1_relat_1(A_1230))), inference(superposition, [status(thm), theory('equality')], [c_28, c_564])).
% 8.78/3.45  tff(c_12925, plain, (![A_1231]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', A_1231) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_1231) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_11299, c_12922])).
% 8.78/3.45  tff(c_12930, plain, (![A_1231]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', A_1231) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_1231) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_66, c_60, c_165, c_12925])).
% 8.78/3.45  tff(c_12931, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_12930])).
% 8.78/3.45  tff(c_12934, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_12931])).
% 8.78/3.45  tff(c_12938, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_194, c_66, c_60, c_12934])).
% 8.78/3.45  tff(c_12940, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_12930])).
% 8.78/3.45  tff(c_10802, plain, (![B_1041, A_1042]: (m1_subset_1(B_1041, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1041), A_1042))) | ~r1_tarski(k2_relat_1(B_1041), A_1042) | ~v1_funct_1(B_1041) | ~v1_relat_1(B_1041))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.78/3.45  tff(c_13224, plain, (![A_1263, A_1264]: (m1_subset_1(k2_funct_1(A_1263), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1263), A_1264))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_1263)), A_1264) | ~v1_funct_1(k2_funct_1(A_1263)) | ~v1_relat_1(k2_funct_1(A_1263)) | ~v2_funct_1(A_1263) | ~v1_funct_1(A_1263) | ~v1_relat_1(A_1263))), inference(superposition, [status(thm), theory('equality')], [c_28, c_10802])).
% 8.78/3.45  tff(c_13259, plain, (![A_1264]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_1264))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_1264) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_11299, c_13224])).
% 8.78/3.45  tff(c_13278, plain, (![A_1265]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_1265))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_1265))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_66, c_60, c_12940, c_165, c_13259])).
% 8.78/3.45  tff(c_164, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_56])).
% 8.78/3.45  tff(c_242, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_164])).
% 8.78/3.45  tff(c_11304, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_11280, c_242])).
% 8.78/3.45  tff(c_13333, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(resolution, [status(thm)], [c_13278, c_11304])).
% 8.78/3.45  tff(c_13350, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_13333])).
% 8.78/3.45  tff(c_13353, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_194, c_66, c_60, c_11295, c_11294, c_13350])).
% 8.78/3.45  tff(c_13354, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_549])).
% 8.78/3.45  tff(c_15124, plain, (![A_1435, A_1436]: (v1_funct_2(k2_funct_1(A_1435), k2_relat_1(A_1435), A_1436) | ~r1_tarski(k2_relat_1(k2_funct_1(A_1435)), A_1436) | ~v1_funct_1(k2_funct_1(A_1435)) | ~v1_relat_1(k2_funct_1(A_1435)) | ~v2_funct_1(A_1435) | ~v1_funct_1(A_1435) | ~v1_relat_1(A_1435))), inference(superposition, [status(thm), theory('equality')], [c_28, c_564])).
% 8.78/3.45  tff(c_15127, plain, (![A_1436]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_1436) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_1436) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_369, c_15124])).
% 8.78/3.45  tff(c_15132, plain, (![A_1436]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_1436) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_1436) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_66, c_60, c_165, c_15127])).
% 8.78/3.45  tff(c_15133, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_15132])).
% 8.78/3.45  tff(c_15136, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_15133])).
% 8.78/3.45  tff(c_15140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_194, c_66, c_60, c_15136])).
% 8.78/3.45  tff(c_15142, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_15132])).
% 8.78/3.45  tff(c_13529, plain, (![B_1283, A_1284]: (m1_subset_1(B_1283, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1283), A_1284))) | ~r1_tarski(k2_relat_1(B_1283), A_1284) | ~v1_funct_1(B_1283) | ~v1_relat_1(B_1283))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.78/3.45  tff(c_15358, plain, (![A_1461, A_1462]: (m1_subset_1(k2_funct_1(A_1461), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1461), A_1462))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_1461)), A_1462) | ~v1_funct_1(k2_funct_1(A_1461)) | ~v1_relat_1(k2_funct_1(A_1461)) | ~v2_funct_1(A_1461) | ~v1_funct_1(A_1461) | ~v1_relat_1(A_1461))), inference(superposition, [status(thm), theory('equality')], [c_28, c_13529])).
% 8.78/3.45  tff(c_15393, plain, (![A_1462]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_1462))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_1462) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_369, c_15358])).
% 8.78/3.45  tff(c_15471, plain, (![A_1464]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_1464))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_1464))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_66, c_60, c_15142, c_165, c_15393])).
% 8.78/3.45  tff(c_15518, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(resolution, [status(thm)], [c_15471, c_242])).
% 8.78/3.45  tff(c_15524, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_15518])).
% 8.78/3.45  tff(c_15527, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_194, c_66, c_60, c_6, c_13354, c_15524])).
% 8.78/3.45  tff(c_15529, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_164])).
% 8.78/3.45  tff(c_30, plain, (![C_17, A_15, B_16]: (v1_relat_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.78/3.45  tff(c_15536, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_15529, c_30])).
% 8.78/3.45  tff(c_15702, plain, (![A_1491, B_1492, C_1493]: (k2_relset_1(A_1491, B_1492, C_1493)=k2_relat_1(C_1493) | ~m1_subset_1(C_1493, k1_zfmisc_1(k2_zfmisc_1(A_1491, B_1492))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.78/3.45  tff(c_15712, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_15702])).
% 8.78/3.45  tff(c_15720, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_15712])).
% 8.78/3.45  tff(c_15661, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_15529, c_15646])).
% 8.78/3.45  tff(c_15760, plain, (m1_subset_1(k1_relat_1(k2_funct_1('#skF_3')), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_15661, c_15737])).
% 8.78/3.45  tff(c_15774, plain, (m1_subset_1(k1_relat_1(k2_funct_1('#skF_3')), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_15529, c_15760])).
% 8.78/3.45  tff(c_15893, plain, (r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2')), inference(resolution, [status(thm)], [c_15774, c_12])).
% 8.78/3.45  tff(c_15918, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2' | ~r1_tarski('#skF_2', k1_relat_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_15893, c_2])).
% 8.78/3.45  tff(c_15975, plain, (~r1_tarski('#skF_2', k1_relat_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_15918])).
% 8.78/3.45  tff(c_15978, plain, (~r1_tarski('#skF_2', k2_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_15975])).
% 8.78/3.45  tff(c_15981, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_194, c_66, c_60, c_6, c_15720, c_15978])).
% 8.78/3.45  tff(c_15982, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_15918])).
% 8.78/3.45  tff(c_52, plain, (![B_31, A_30]: (v1_funct_2(B_31, k1_relat_1(B_31), A_30) | ~r1_tarski(k2_relat_1(B_31), A_30) | ~v1_funct_1(B_31) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.78/3.45  tff(c_16011, plain, (![A_30]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_30) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_30) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_15982, c_52])).
% 8.78/3.45  tff(c_16037, plain, (![A_1515]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_1515) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_1515))), inference(demodulation, [status(thm), theory('equality')], [c_15536, c_165, c_16011])).
% 8.78/3.45  tff(c_16040, plain, (![A_1515]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_1515) | ~r1_tarski(k1_relat_1('#skF_3'), A_1515) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_26, c_16037])).
% 8.78/3.45  tff(c_16053, plain, (![A_1516]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_1516) | ~r1_tarski(k1_relat_1('#skF_3'), A_1516))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_66, c_60, c_16040])).
% 8.78/3.45  tff(c_15528, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_164])).
% 8.78/3.45  tff(c_16056, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_16053, c_15528])).
% 8.78/3.45  tff(c_16060, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15851, c_16056])).
% 8.78/3.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.78/3.45  
% 8.78/3.45  Inference rules
% 8.78/3.45  ----------------------
% 8.78/3.45  #Ref     : 0
% 8.78/3.45  #Sup     : 3185
% 8.78/3.45  #Fact    : 0
% 8.78/3.45  #Define  : 0
% 8.78/3.45  #Split   : 40
% 8.78/3.45  #Chain   : 0
% 8.78/3.45  #Close   : 0
% 8.78/3.45  
% 8.78/3.45  Ordering : KBO
% 8.78/3.45  
% 8.78/3.45  Simplification rules
% 8.78/3.45  ----------------------
% 8.78/3.45  #Subsume      : 546
% 8.78/3.45  #Demod        : 3748
% 8.78/3.45  #Tautology    : 1402
% 8.78/3.45  #SimpNegUnit  : 8
% 8.78/3.45  #BackRed      : 291
% 8.78/3.45  
% 8.78/3.45  #Partial instantiations: 0
% 8.78/3.45  #Strategies tried      : 1
% 8.78/3.45  
% 8.78/3.45  Timing (in seconds)
% 8.78/3.45  ----------------------
% 8.78/3.45  Preprocessing        : 0.36
% 8.78/3.45  Parsing              : 0.20
% 8.78/3.45  CNF conversion       : 0.02
% 8.78/3.45  Main loop            : 2.29
% 8.78/3.45  Inferencing          : 0.77
% 8.78/3.45  Reduction            : 0.82
% 8.78/3.45  Demodulation         : 0.60
% 8.78/3.45  BG Simplification    : 0.08
% 8.78/3.45  Subsumption          : 0.43
% 8.78/3.45  Abstraction          : 0.11
% 8.78/3.45  MUC search           : 0.00
% 8.78/3.45  Cooper               : 0.00
% 8.78/3.45  Total                : 2.70
% 8.78/3.45  Index Insertion      : 0.00
% 8.78/3.45  Index Deletion       : 0.00
% 8.78/3.45  Index Matching       : 0.00
% 8.78/3.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
