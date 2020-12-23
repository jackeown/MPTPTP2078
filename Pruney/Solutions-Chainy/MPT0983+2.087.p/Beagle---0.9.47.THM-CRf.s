%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:13 EST 2020

% Result     : Theorem 5.38s
% Output     : CNFRefutation 5.67s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 238 expanded)
%              Number of leaves         :   44 ( 104 expanded)
%              Depth                    :   12
%              Number of atoms          :  191 ( 667 expanded)
%              Number of equality atoms :   30 (  58 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_101,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_99,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_79,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_48,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_77,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( v1_xboole_0(k2_zfmisc_1(A_7,B_8))
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_186,plain,(
    ! [C_77,B_78,A_79] :
      ( ~ v1_xboole_0(C_77)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(C_77))
      | ~ r2_hidden(A_79,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_200,plain,(
    ! [A_79] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_79,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_186])).

tff(c_218,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_200])).

tff(c_262,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_218])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_60,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_54,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_40,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_16,plain,(
    ! [A_12] : v2_funct_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_64,plain,(
    ! [A_12] : v2_funct_1(k6_partfun1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_16])).

tff(c_36,plain,(
    ! [E_33,A_29,F_34,D_32,C_31,B_30] :
      ( m1_subset_1(k1_partfun1(A_29,B_30,C_31,D_32,E_33,F_34),k1_zfmisc_1(k2_zfmisc_1(A_29,D_32)))
      | ~ m1_subset_1(F_34,k1_zfmisc_1(k2_zfmisc_1(C_31,D_32)))
      | ~ v1_funct_1(F_34)
      | ~ m1_subset_1(E_33,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ v1_funct_1(E_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_30,plain,(
    ! [A_26] : m1_subset_1(k6_relat_1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_63,plain,(
    ! [A_26] : m1_subset_1(k6_partfun1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_30])).

tff(c_50,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_377,plain,(
    ! [D_99,C_100,A_101,B_102] :
      ( D_99 = C_100
      | ~ r2_relset_1(A_101,B_102,C_100,D_99)
      | ~ m1_subset_1(D_99,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102)))
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_387,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_50,c_377])).

tff(c_406,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_387])).

tff(c_447,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_406])).

tff(c_1226,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_447])).

tff(c_1230,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_56,c_52,c_1226])).

tff(c_1231,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_406])).

tff(c_2302,plain,(
    ! [C_222,D_223,A_221,B_224,E_220] :
      ( k1_xboole_0 = C_222
      | v2_funct_1(D_223)
      | ~ v2_funct_1(k1_partfun1(A_221,B_224,B_224,C_222,D_223,E_220))
      | ~ m1_subset_1(E_220,k1_zfmisc_1(k2_zfmisc_1(B_224,C_222)))
      | ~ v1_funct_2(E_220,B_224,C_222)
      | ~ v1_funct_1(E_220)
      | ~ m1_subset_1(D_223,k1_zfmisc_1(k2_zfmisc_1(A_221,B_224)))
      | ~ v1_funct_2(D_223,A_221,B_224)
      | ~ v1_funct_1(D_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_2304,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1231,c_2302])).

tff(c_2306,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_54,c_52,c_64,c_2304])).

tff(c_2307,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_2306])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2340,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2307,c_6])).

tff(c_2342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_262,c_2340])).

tff(c_2345,plain,(
    ! [A_225] : ~ r2_hidden(A_225,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_2350,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_2345])).

tff(c_85,plain,(
    ! [B_56,A_57] :
      ( ~ v1_xboole_0(B_56)
      | B_56 = A_57
      | ~ v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_91,plain,(
    ! [A_57] :
      ( k1_xboole_0 = A_57
      | ~ v1_xboole_0(A_57) ) ),
    inference(resolution,[status(thm)],[c_6,c_85])).

tff(c_2359,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2350,c_91])).

tff(c_92,plain,(
    ! [A_58] :
      ( k1_xboole_0 = A_58
      | ~ v1_xboole_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_6,c_85])).

tff(c_102,plain,(
    ! [A_59,B_60] :
      ( k2_zfmisc_1(A_59,B_60) = k1_xboole_0
      | ~ v1_xboole_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_10,c_92])).

tff(c_108,plain,(
    ! [B_60] : k2_zfmisc_1(k1_xboole_0,B_60) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_102])).

tff(c_121,plain,(
    ! [A_62] : m1_subset_1(k6_partfun1(A_62),k1_zfmisc_1(k2_zfmisc_1(A_62,A_62))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_30])).

tff(c_125,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_121])).

tff(c_188,plain,(
    ! [A_79] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_79,k6_partfun1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_125,c_186])).

tff(c_202,plain,(
    ! [A_81] : ~ r2_hidden(A_81,k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_188])).

tff(c_207,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_4,c_202])).

tff(c_216,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_207,c_91])).

tff(c_2380,plain,(
    k6_partfun1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2359,c_2359,c_216])).

tff(c_2394,plain,(
    v2_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2380,c_64])).

tff(c_2400,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_2394])).

tff(c_2401,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2451,plain,(
    ! [C_238,A_239,B_240] :
      ( v1_relat_1(C_238)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_239,B_240))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2466,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_2451])).

tff(c_2512,plain,(
    ! [C_248,B_249,A_250] :
      ( v5_relat_1(C_248,B_249)
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(A_250,B_249))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2530,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_2512])).

tff(c_2715,plain,(
    ! [A_272,B_273,C_274] :
      ( k2_relset_1(A_272,B_273,C_274) = k2_relat_1(C_274)
      | ~ m1_subset_1(C_274,k1_zfmisc_1(k2_zfmisc_1(A_272,B_273))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2733,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_2715])).

tff(c_4254,plain,(
    ! [A_356,B_357,C_358,D_359] :
      ( k2_relset_1(A_356,B_357,C_358) = B_357
      | ~ r2_relset_1(B_357,B_357,k1_partfun1(B_357,A_356,A_356,B_357,D_359,C_358),k6_partfun1(B_357))
      | ~ m1_subset_1(D_359,k1_zfmisc_1(k2_zfmisc_1(B_357,A_356)))
      | ~ v1_funct_2(D_359,B_357,A_356)
      | ~ v1_funct_1(D_359)
      | ~ m1_subset_1(C_358,k1_zfmisc_1(k2_zfmisc_1(A_356,B_357)))
      | ~ v1_funct_2(C_358,A_356,B_357)
      | ~ v1_funct_1(C_358) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_4275,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_4254])).

tff(c_4279,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_62,c_60,c_58,c_2733,c_4275])).

tff(c_32,plain,(
    ! [B_28] :
      ( v2_funct_2(B_28,k2_relat_1(B_28))
      | ~ v5_relat_1(B_28,k2_relat_1(B_28))
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4284,plain,
    ( v2_funct_2('#skF_5',k2_relat_1('#skF_5'))
    | ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4279,c_32])).

tff(c_4288,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2466,c_2530,c_4279,c_4284])).

tff(c_4290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2401,c_4288])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:53:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.38/2.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.38/2.05  
% 5.38/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.67/2.05  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 5.67/2.05  
% 5.67/2.05  %Foreground sorts:
% 5.67/2.05  
% 5.67/2.05  
% 5.67/2.05  %Background operators:
% 5.67/2.05  
% 5.67/2.05  
% 5.67/2.05  %Foreground operators:
% 5.67/2.05  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.67/2.05  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.67/2.05  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.67/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.67/2.05  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.67/2.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.67/2.05  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.67/2.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.67/2.05  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.67/2.05  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.67/2.05  tff('#skF_5', type, '#skF_5': $i).
% 5.67/2.05  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.67/2.05  tff('#skF_2', type, '#skF_2': $i).
% 5.67/2.05  tff('#skF_3', type, '#skF_3': $i).
% 5.67/2.05  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.67/2.05  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.67/2.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.67/2.05  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.67/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.67/2.05  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.67/2.05  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.67/2.05  tff('#skF_4', type, '#skF_4': $i).
% 5.67/2.05  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.67/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.67/2.05  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.67/2.05  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.67/2.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.67/2.05  
% 5.67/2.06  tff(f_160, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 5.67/2.06  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.67/2.06  tff(f_44, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 5.67/2.06  tff(f_51, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 5.67/2.06  tff(f_101, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.67/2.06  tff(f_55, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.67/2.06  tff(f_99, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.67/2.06  tff(f_79, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 5.67/2.06  tff(f_77, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.67/2.06  tff(f_140, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 5.67/2.06  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.67/2.06  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 5.67/2.06  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.67/2.06  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.67/2.06  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.67/2.06  tff(f_118, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 5.67/2.06  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 5.67/2.06  tff(c_48, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.67/2.06  tff(c_77, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_48])).
% 5.67/2.06  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.67/2.06  tff(c_10, plain, (![A_7, B_8]: (v1_xboole_0(k2_zfmisc_1(A_7, B_8)) | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.67/2.06  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.67/2.06  tff(c_186, plain, (![C_77, B_78, A_79]: (~v1_xboole_0(C_77) | ~m1_subset_1(B_78, k1_zfmisc_1(C_77)) | ~r2_hidden(A_79, B_78))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.67/2.06  tff(c_200, plain, (![A_79]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_79, '#skF_4'))), inference(resolution, [status(thm)], [c_58, c_186])).
% 5.67/2.06  tff(c_218, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_200])).
% 5.67/2.06  tff(c_262, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_10, c_218])).
% 5.67/2.06  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.67/2.06  tff(c_60, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.67/2.06  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.67/2.06  tff(c_54, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.67/2.06  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.67/2.06  tff(c_40, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.67/2.06  tff(c_16, plain, (![A_12]: (v2_funct_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.67/2.06  tff(c_64, plain, (![A_12]: (v2_funct_1(k6_partfun1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_16])).
% 5.67/2.06  tff(c_36, plain, (![E_33, A_29, F_34, D_32, C_31, B_30]: (m1_subset_1(k1_partfun1(A_29, B_30, C_31, D_32, E_33, F_34), k1_zfmisc_1(k2_zfmisc_1(A_29, D_32))) | ~m1_subset_1(F_34, k1_zfmisc_1(k2_zfmisc_1(C_31, D_32))) | ~v1_funct_1(F_34) | ~m1_subset_1(E_33, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | ~v1_funct_1(E_33))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.67/2.06  tff(c_30, plain, (![A_26]: (m1_subset_1(k6_relat_1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.67/2.06  tff(c_63, plain, (![A_26]: (m1_subset_1(k6_partfun1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_30])).
% 5.67/2.06  tff(c_50, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.67/2.06  tff(c_377, plain, (![D_99, C_100, A_101, B_102]: (D_99=C_100 | ~r2_relset_1(A_101, B_102, C_100, D_99) | ~m1_subset_1(D_99, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.67/2.06  tff(c_387, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_50, c_377])).
% 5.67/2.06  tff(c_406, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_387])).
% 5.67/2.06  tff(c_447, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_406])).
% 5.67/2.06  tff(c_1226, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_447])).
% 5.67/2.06  tff(c_1230, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_56, c_52, c_1226])).
% 5.67/2.06  tff(c_1231, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_406])).
% 5.67/2.06  tff(c_2302, plain, (![C_222, D_223, A_221, B_224, E_220]: (k1_xboole_0=C_222 | v2_funct_1(D_223) | ~v2_funct_1(k1_partfun1(A_221, B_224, B_224, C_222, D_223, E_220)) | ~m1_subset_1(E_220, k1_zfmisc_1(k2_zfmisc_1(B_224, C_222))) | ~v1_funct_2(E_220, B_224, C_222) | ~v1_funct_1(E_220) | ~m1_subset_1(D_223, k1_zfmisc_1(k2_zfmisc_1(A_221, B_224))) | ~v1_funct_2(D_223, A_221, B_224) | ~v1_funct_1(D_223))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.67/2.06  tff(c_2304, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1231, c_2302])).
% 5.67/2.06  tff(c_2306, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_54, c_52, c_64, c_2304])).
% 5.67/2.06  tff(c_2307, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_77, c_2306])).
% 5.67/2.06  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.67/2.06  tff(c_2340, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2307, c_6])).
% 5.67/2.06  tff(c_2342, plain, $false, inference(negUnitSimplification, [status(thm)], [c_262, c_2340])).
% 5.67/2.06  tff(c_2345, plain, (![A_225]: (~r2_hidden(A_225, '#skF_4'))), inference(splitRight, [status(thm)], [c_200])).
% 5.67/2.06  tff(c_2350, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_2345])).
% 5.67/2.06  tff(c_85, plain, (![B_56, A_57]: (~v1_xboole_0(B_56) | B_56=A_57 | ~v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.67/2.06  tff(c_91, plain, (![A_57]: (k1_xboole_0=A_57 | ~v1_xboole_0(A_57))), inference(resolution, [status(thm)], [c_6, c_85])).
% 5.67/2.06  tff(c_2359, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2350, c_91])).
% 5.67/2.06  tff(c_92, plain, (![A_58]: (k1_xboole_0=A_58 | ~v1_xboole_0(A_58))), inference(resolution, [status(thm)], [c_6, c_85])).
% 5.67/2.06  tff(c_102, plain, (![A_59, B_60]: (k2_zfmisc_1(A_59, B_60)=k1_xboole_0 | ~v1_xboole_0(A_59))), inference(resolution, [status(thm)], [c_10, c_92])).
% 5.67/2.06  tff(c_108, plain, (![B_60]: (k2_zfmisc_1(k1_xboole_0, B_60)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_102])).
% 5.67/2.06  tff(c_121, plain, (![A_62]: (m1_subset_1(k6_partfun1(A_62), k1_zfmisc_1(k2_zfmisc_1(A_62, A_62))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_30])).
% 5.67/2.06  tff(c_125, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_108, c_121])).
% 5.67/2.06  tff(c_188, plain, (![A_79]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_79, k6_partfun1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_125, c_186])).
% 5.67/2.06  tff(c_202, plain, (![A_81]: (~r2_hidden(A_81, k6_partfun1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_188])).
% 5.67/2.06  tff(c_207, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_202])).
% 5.67/2.06  tff(c_216, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_207, c_91])).
% 5.67/2.06  tff(c_2380, plain, (k6_partfun1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2359, c_2359, c_216])).
% 5.67/2.06  tff(c_2394, plain, (v2_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2380, c_64])).
% 5.67/2.06  tff(c_2400, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_2394])).
% 5.67/2.06  tff(c_2401, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 5.67/2.06  tff(c_2451, plain, (![C_238, A_239, B_240]: (v1_relat_1(C_238) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_239, B_240))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.67/2.06  tff(c_2466, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_2451])).
% 5.67/2.06  tff(c_2512, plain, (![C_248, B_249, A_250]: (v5_relat_1(C_248, B_249) | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(A_250, B_249))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.67/2.06  tff(c_2530, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_2512])).
% 5.67/2.06  tff(c_2715, plain, (![A_272, B_273, C_274]: (k2_relset_1(A_272, B_273, C_274)=k2_relat_1(C_274) | ~m1_subset_1(C_274, k1_zfmisc_1(k2_zfmisc_1(A_272, B_273))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.67/2.06  tff(c_2733, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_2715])).
% 5.67/2.07  tff(c_4254, plain, (![A_356, B_357, C_358, D_359]: (k2_relset_1(A_356, B_357, C_358)=B_357 | ~r2_relset_1(B_357, B_357, k1_partfun1(B_357, A_356, A_356, B_357, D_359, C_358), k6_partfun1(B_357)) | ~m1_subset_1(D_359, k1_zfmisc_1(k2_zfmisc_1(B_357, A_356))) | ~v1_funct_2(D_359, B_357, A_356) | ~v1_funct_1(D_359) | ~m1_subset_1(C_358, k1_zfmisc_1(k2_zfmisc_1(A_356, B_357))) | ~v1_funct_2(C_358, A_356, B_357) | ~v1_funct_1(C_358))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.67/2.07  tff(c_4275, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_4254])).
% 5.67/2.07  tff(c_4279, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_62, c_60, c_58, c_2733, c_4275])).
% 5.67/2.07  tff(c_32, plain, (![B_28]: (v2_funct_2(B_28, k2_relat_1(B_28)) | ~v5_relat_1(B_28, k2_relat_1(B_28)) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.67/2.07  tff(c_4284, plain, (v2_funct_2('#skF_5', k2_relat_1('#skF_5')) | ~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4279, c_32])).
% 5.67/2.07  tff(c_4288, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2466, c_2530, c_4279, c_4284])).
% 5.67/2.07  tff(c_4290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2401, c_4288])).
% 5.67/2.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.67/2.07  
% 5.67/2.07  Inference rules
% 5.67/2.07  ----------------------
% 5.67/2.07  #Ref     : 0
% 5.67/2.07  #Sup     : 1051
% 5.67/2.07  #Fact    : 0
% 5.67/2.07  #Define  : 0
% 5.67/2.07  #Split   : 12
% 5.67/2.07  #Chain   : 0
% 5.67/2.07  #Close   : 0
% 5.67/2.07  
% 5.67/2.07  Ordering : KBO
% 5.67/2.07  
% 5.67/2.07  Simplification rules
% 5.67/2.07  ----------------------
% 5.67/2.07  #Subsume      : 110
% 5.67/2.07  #Demod        : 886
% 5.67/2.07  #Tautology    : 522
% 5.67/2.07  #SimpNegUnit  : 4
% 5.67/2.07  #BackRed      : 54
% 5.67/2.07  
% 5.67/2.07  #Partial instantiations: 0
% 5.67/2.07  #Strategies tried      : 1
% 5.67/2.07  
% 5.67/2.07  Timing (in seconds)
% 5.67/2.07  ----------------------
% 5.76/2.07  Preprocessing        : 0.37
% 5.76/2.07  Parsing              : 0.19
% 5.76/2.07  CNF conversion       : 0.03
% 5.76/2.07  Main loop            : 0.93
% 5.76/2.07  Inferencing          : 0.30
% 5.76/2.07  Reduction            : 0.32
% 5.76/2.07  Demodulation         : 0.23
% 5.76/2.07  BG Simplification    : 0.04
% 5.76/2.07  Subsumption          : 0.19
% 5.76/2.07  Abstraction          : 0.04
% 5.76/2.07  MUC search           : 0.00
% 5.76/2.07  Cooper               : 0.00
% 5.76/2.07  Total                : 1.33
% 5.76/2.07  Index Insertion      : 0.00
% 5.76/2.07  Index Deletion       : 0.00
% 5.76/2.07  Index Matching       : 0.00
% 5.76/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
