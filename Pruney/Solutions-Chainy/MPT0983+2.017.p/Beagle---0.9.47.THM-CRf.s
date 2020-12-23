%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:03 EST 2020

% Result     : Theorem 5.84s
% Output     : CNFRefutation 5.84s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 277 expanded)
%              Number of leaves         :   47 ( 121 expanded)
%              Depth                    :   10
%              Number of atoms          :  200 ( 912 expanded)
%              Number of equality atoms :   26 (  71 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_174,negated_conjecture,(
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

tff(f_115,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_113,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_93,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_154,axiom,(
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

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_132,axiom,(
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

tff(f_101,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_66,plain,
    ( ~ v2_funct_2('#skF_6','#skF_3')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_110,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_80,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_78,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_76,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_74,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_72,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_70,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_58,plain,(
    ! [A_39] : k6_relat_1(A_39) = k6_partfun1(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_34,plain,(
    ! [A_16] : v2_funct_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_82,plain,(
    ! [A_16] : v2_funct_1(k6_partfun1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_34])).

tff(c_54,plain,(
    ! [D_36,F_38,E_37,A_33,B_34,C_35] :
      ( m1_subset_1(k1_partfun1(A_33,B_34,C_35,D_36,E_37,F_38),k1_zfmisc_1(k2_zfmisc_1(A_33,D_36)))
      | ~ m1_subset_1(F_38,k1_zfmisc_1(k2_zfmisc_1(C_35,D_36)))
      | ~ v1_funct_1(F_38)
      | ~ m1_subset_1(E_37,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34)))
      | ~ v1_funct_1(E_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_48,plain,(
    ! [A_30] : m1_subset_1(k6_relat_1(A_30),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_81,plain,(
    ! [A_30] : m1_subset_1(k6_partfun1(A_30),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_48])).

tff(c_68,plain,(
    r2_relset_1('#skF_3','#skF_3',k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k6_partfun1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_1617,plain,(
    ! [D_282,C_283,A_284,B_285] :
      ( D_282 = C_283
      | ~ r2_relset_1(A_284,B_285,C_283,D_282)
      | ~ m1_subset_1(D_282,k1_zfmisc_1(k2_zfmisc_1(A_284,B_285)))
      | ~ m1_subset_1(C_283,k1_zfmisc_1(k2_zfmisc_1(A_284,B_285))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1625,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_68,c_1617])).

tff(c_1640,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_1625])).

tff(c_1652,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1640])).

tff(c_2048,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_1652])).

tff(c_2055,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_2048])).

tff(c_2056,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1640])).

tff(c_2794,plain,(
    ! [B_449,D_452,C_453,A_450,E_451] :
      ( k1_xboole_0 = C_453
      | v2_funct_1(D_452)
      | ~ v2_funct_1(k1_partfun1(A_450,B_449,B_449,C_453,D_452,E_451))
      | ~ m1_subset_1(E_451,k1_zfmisc_1(k2_zfmisc_1(B_449,C_453)))
      | ~ v1_funct_2(E_451,B_449,C_453)
      | ~ v1_funct_1(E_451)
      | ~ m1_subset_1(D_452,k1_zfmisc_1(k2_zfmisc_1(A_450,B_449)))
      | ~ v1_funct_2(D_452,A_450,B_449)
      | ~ v1_funct_1(D_452) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_2796,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_funct_1('#skF_5')
    | ~ v2_funct_1(k6_partfun1('#skF_3'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2056,c_2794])).

tff(c_2801,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_72,c_70,c_82,c_2796])).

tff(c_2802,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_2801])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2841,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2802,c_12])).

tff(c_18,plain,(
    ! [B_11] : k2_zfmisc_1(k1_xboole_0,B_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2839,plain,(
    ! [B_11] : k2_zfmisc_1('#skF_3',B_11) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2802,c_2802,c_18])).

tff(c_174,plain,(
    ! [A_67] :
      ( v2_funct_1(A_67)
      | ~ v1_funct_1(A_67)
      | ~ v1_relat_1(A_67)
      | ~ v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_177,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_174,c_110])).

tff(c_180,plain,
    ( ~ v1_relat_1('#skF_5')
    | ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_177])).

tff(c_181,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_180])).

tff(c_131,plain,(
    ! [A_61,B_62] :
      ( r1_tarski(A_61,B_62)
      | ~ m1_subset_1(A_61,k1_zfmisc_1(B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_139,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_76,c_131])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_281,plain,(
    ! [C_86,B_87,A_88] :
      ( r2_hidden(C_86,B_87)
      | ~ r2_hidden(C_86,A_88)
      | ~ r1_tarski(A_88,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2093,plain,(
    ! [A_354,B_355] :
      ( r2_hidden('#skF_1'(A_354),B_355)
      | ~ r1_tarski(A_354,B_355)
      | v1_xboole_0(A_354) ) ),
    inference(resolution,[status(thm)],[c_4,c_281])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2123,plain,(
    ! [B_362,A_363] :
      ( ~ v1_xboole_0(B_362)
      | ~ r1_tarski(A_363,B_362)
      | v1_xboole_0(A_363) ) ),
    inference(resolution,[status(thm)],[c_2093,c_2])).

tff(c_2138,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_139,c_2123])).

tff(c_2150,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_181,c_2138])).

tff(c_2909,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2839,c_2150])).

tff(c_2914,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2841,c_2909])).

tff(c_2915,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_2934,plain,(
    ! [C_466,A_467,B_468] :
      ( v1_relat_1(C_466)
      | ~ m1_subset_1(C_466,k1_zfmisc_1(k2_zfmisc_1(A_467,B_468))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2947,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_2934])).

tff(c_2959,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2915,c_2947])).

tff(c_2960,plain,(
    ~ v2_funct_2('#skF_6','#skF_3') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_3042,plain,(
    ! [C_486,A_487,B_488] :
      ( v1_relat_1(C_486)
      | ~ m1_subset_1(C_486,k1_zfmisc_1(k2_zfmisc_1(A_487,B_488))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3064,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_3042])).

tff(c_3183,plain,(
    ! [C_510,B_511,A_512] :
      ( v5_relat_1(C_510,B_511)
      | ~ m1_subset_1(C_510,k1_zfmisc_1(k2_zfmisc_1(A_512,B_511))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3206,plain,(
    v5_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_3183])).

tff(c_3298,plain,(
    ! [A_531,B_532,C_533] :
      ( k2_relset_1(A_531,B_532,C_533) = k2_relat_1(C_533)
      | ~ m1_subset_1(C_533,k1_zfmisc_1(k2_zfmisc_1(A_531,B_532))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_3321,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_3298])).

tff(c_3780,plain,(
    ! [A_605,B_606,C_607,D_608] :
      ( k2_relset_1(A_605,B_606,C_607) = B_606
      | ~ r2_relset_1(B_606,B_606,k1_partfun1(B_606,A_605,A_605,B_606,D_608,C_607),k6_partfun1(B_606))
      | ~ m1_subset_1(D_608,k1_zfmisc_1(k2_zfmisc_1(B_606,A_605)))
      | ~ v1_funct_2(D_608,B_606,A_605)
      | ~ v1_funct_1(D_608)
      | ~ m1_subset_1(C_607,k1_zfmisc_1(k2_zfmisc_1(A_605,B_606)))
      | ~ v1_funct_2(C_607,A_605,B_606)
      | ~ v1_funct_1(C_607) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_3783,plain,
    ( k2_relset_1('#skF_4','#skF_3','#skF_6') = '#skF_3'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_3780])).

tff(c_3786,plain,(
    k2_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_80,c_78,c_76,c_3321,c_3783])).

tff(c_50,plain,(
    ! [B_32] :
      ( v2_funct_2(B_32,k2_relat_1(B_32))
      | ~ v5_relat_1(B_32,k2_relat_1(B_32))
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_3797,plain,
    ( v2_funct_2('#skF_6',k2_relat_1('#skF_6'))
    | ~ v5_relat_1('#skF_6','#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3786,c_50])).

tff(c_3807,plain,(
    v2_funct_2('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3064,c_3206,c_3786,c_3797])).

tff(c_3809,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2960,c_3807])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:16:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.84/2.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.84/2.18  
% 5.84/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.84/2.18  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 5.84/2.18  
% 5.84/2.18  %Foreground sorts:
% 5.84/2.18  
% 5.84/2.18  
% 5.84/2.18  %Background operators:
% 5.84/2.18  
% 5.84/2.18  
% 5.84/2.18  %Foreground operators:
% 5.84/2.18  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.84/2.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.84/2.18  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.84/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.84/2.18  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.84/2.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.84/2.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.84/2.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.84/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.84/2.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.84/2.18  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.84/2.18  tff('#skF_5', type, '#skF_5': $i).
% 5.84/2.18  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.84/2.18  tff('#skF_6', type, '#skF_6': $i).
% 5.84/2.18  tff('#skF_3', type, '#skF_3': $i).
% 5.84/2.18  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.84/2.18  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.84/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.84/2.18  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.84/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.84/2.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.84/2.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.84/2.18  tff('#skF_4', type, '#skF_4': $i).
% 5.84/2.18  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.84/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.84/2.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.84/2.18  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.84/2.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.84/2.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.84/2.18  
% 5.84/2.20  tff(f_174, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 5.84/2.20  tff(f_115, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.84/2.20  tff(f_69, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.84/2.20  tff(f_113, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.84/2.20  tff(f_93, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 5.84/2.20  tff(f_91, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.84/2.20  tff(f_154, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 5.84/2.20  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.84/2.20  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.84/2.20  tff(f_65, axiom, (![A]: (((v1_xboole_0(A) & v1_relat_1(A)) & v1_funct_1(A)) => ((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_1)).
% 5.84/2.20  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.84/2.20  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.84/2.20  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.84/2.20  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.84/2.20  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.84/2.20  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.84/2.20  tff(f_132, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 5.84/2.20  tff(f_101, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 5.84/2.20  tff(c_66, plain, (~v2_funct_2('#skF_6', '#skF_3') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.84/2.20  tff(c_110, plain, (~v2_funct_1('#skF_5')), inference(splitLeft, [status(thm)], [c_66])).
% 5.84/2.20  tff(c_80, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.84/2.20  tff(c_78, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.84/2.20  tff(c_76, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.84/2.20  tff(c_74, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.84/2.20  tff(c_72, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.84/2.20  tff(c_70, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.84/2.20  tff(c_58, plain, (![A_39]: (k6_relat_1(A_39)=k6_partfun1(A_39))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.84/2.20  tff(c_34, plain, (![A_16]: (v2_funct_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.84/2.20  tff(c_82, plain, (![A_16]: (v2_funct_1(k6_partfun1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_34])).
% 5.84/2.20  tff(c_54, plain, (![D_36, F_38, E_37, A_33, B_34, C_35]: (m1_subset_1(k1_partfun1(A_33, B_34, C_35, D_36, E_37, F_38), k1_zfmisc_1(k2_zfmisc_1(A_33, D_36))) | ~m1_subset_1(F_38, k1_zfmisc_1(k2_zfmisc_1(C_35, D_36))) | ~v1_funct_1(F_38) | ~m1_subset_1(E_37, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))) | ~v1_funct_1(E_37))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.84/2.20  tff(c_48, plain, (![A_30]: (m1_subset_1(k6_relat_1(A_30), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.84/2.20  tff(c_81, plain, (![A_30]: (m1_subset_1(k6_partfun1(A_30), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_48])).
% 5.84/2.20  tff(c_68, plain, (r2_relset_1('#skF_3', '#skF_3', k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k6_partfun1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.84/2.20  tff(c_1617, plain, (![D_282, C_283, A_284, B_285]: (D_282=C_283 | ~r2_relset_1(A_284, B_285, C_283, D_282) | ~m1_subset_1(D_282, k1_zfmisc_1(k2_zfmisc_1(A_284, B_285))) | ~m1_subset_1(C_283, k1_zfmisc_1(k2_zfmisc_1(A_284, B_285))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.84/2.20  tff(c_1625, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_68, c_1617])).
% 5.84/2.20  tff(c_1640, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_1625])).
% 5.84/2.20  tff(c_1652, plain, (~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(splitLeft, [status(thm)], [c_1640])).
% 5.84/2.20  tff(c_2048, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_1652])).
% 5.84/2.20  tff(c_2055, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_2048])).
% 5.84/2.20  tff(c_2056, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3')), inference(splitRight, [status(thm)], [c_1640])).
% 5.84/2.20  tff(c_2794, plain, (![B_449, D_452, C_453, A_450, E_451]: (k1_xboole_0=C_453 | v2_funct_1(D_452) | ~v2_funct_1(k1_partfun1(A_450, B_449, B_449, C_453, D_452, E_451)) | ~m1_subset_1(E_451, k1_zfmisc_1(k2_zfmisc_1(B_449, C_453))) | ~v1_funct_2(E_451, B_449, C_453) | ~v1_funct_1(E_451) | ~m1_subset_1(D_452, k1_zfmisc_1(k2_zfmisc_1(A_450, B_449))) | ~v1_funct_2(D_452, A_450, B_449) | ~v1_funct_1(D_452))), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.84/2.20  tff(c_2796, plain, (k1_xboole_0='#skF_3' | v2_funct_1('#skF_5') | ~v2_funct_1(k6_partfun1('#skF_3')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2056, c_2794])).
% 5.84/2.20  tff(c_2801, plain, (k1_xboole_0='#skF_3' | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_72, c_70, c_82, c_2796])).
% 5.84/2.20  tff(c_2802, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_110, c_2801])).
% 5.84/2.20  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.84/2.20  tff(c_2841, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2802, c_12])).
% 5.84/2.20  tff(c_18, plain, (![B_11]: (k2_zfmisc_1(k1_xboole_0, B_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.84/2.20  tff(c_2839, plain, (![B_11]: (k2_zfmisc_1('#skF_3', B_11)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2802, c_2802, c_18])).
% 5.84/2.20  tff(c_174, plain, (![A_67]: (v2_funct_1(A_67) | ~v1_funct_1(A_67) | ~v1_relat_1(A_67) | ~v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.84/2.20  tff(c_177, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_174, c_110])).
% 5.84/2.20  tff(c_180, plain, (~v1_relat_1('#skF_5') | ~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_177])).
% 5.84/2.20  tff(c_181, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_180])).
% 5.84/2.20  tff(c_131, plain, (![A_61, B_62]: (r1_tarski(A_61, B_62) | ~m1_subset_1(A_61, k1_zfmisc_1(B_62)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.84/2.20  tff(c_139, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_76, c_131])).
% 5.84/2.20  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.84/2.20  tff(c_281, plain, (![C_86, B_87, A_88]: (r2_hidden(C_86, B_87) | ~r2_hidden(C_86, A_88) | ~r1_tarski(A_88, B_87))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.84/2.20  tff(c_2093, plain, (![A_354, B_355]: (r2_hidden('#skF_1'(A_354), B_355) | ~r1_tarski(A_354, B_355) | v1_xboole_0(A_354))), inference(resolution, [status(thm)], [c_4, c_281])).
% 5.84/2.20  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.84/2.20  tff(c_2123, plain, (![B_362, A_363]: (~v1_xboole_0(B_362) | ~r1_tarski(A_363, B_362) | v1_xboole_0(A_363))), inference(resolution, [status(thm)], [c_2093, c_2])).
% 5.84/2.20  tff(c_2138, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_139, c_2123])).
% 5.84/2.20  tff(c_2150, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_181, c_2138])).
% 5.84/2.20  tff(c_2909, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2839, c_2150])).
% 5.84/2.20  tff(c_2914, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2841, c_2909])).
% 5.84/2.20  tff(c_2915, plain, (~v1_relat_1('#skF_5')), inference(splitRight, [status(thm)], [c_180])).
% 5.84/2.20  tff(c_2934, plain, (![C_466, A_467, B_468]: (v1_relat_1(C_466) | ~m1_subset_1(C_466, k1_zfmisc_1(k2_zfmisc_1(A_467, B_468))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.84/2.20  tff(c_2947, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_76, c_2934])).
% 5.84/2.20  tff(c_2959, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2915, c_2947])).
% 5.84/2.20  tff(c_2960, plain, (~v2_funct_2('#skF_6', '#skF_3')), inference(splitRight, [status(thm)], [c_66])).
% 5.84/2.20  tff(c_3042, plain, (![C_486, A_487, B_488]: (v1_relat_1(C_486) | ~m1_subset_1(C_486, k1_zfmisc_1(k2_zfmisc_1(A_487, B_488))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.84/2.20  tff(c_3064, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_70, c_3042])).
% 5.84/2.20  tff(c_3183, plain, (![C_510, B_511, A_512]: (v5_relat_1(C_510, B_511) | ~m1_subset_1(C_510, k1_zfmisc_1(k2_zfmisc_1(A_512, B_511))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.84/2.20  tff(c_3206, plain, (v5_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_3183])).
% 5.84/2.20  tff(c_3298, plain, (![A_531, B_532, C_533]: (k2_relset_1(A_531, B_532, C_533)=k2_relat_1(C_533) | ~m1_subset_1(C_533, k1_zfmisc_1(k2_zfmisc_1(A_531, B_532))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.84/2.20  tff(c_3321, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_70, c_3298])).
% 5.84/2.20  tff(c_3780, plain, (![A_605, B_606, C_607, D_608]: (k2_relset_1(A_605, B_606, C_607)=B_606 | ~r2_relset_1(B_606, B_606, k1_partfun1(B_606, A_605, A_605, B_606, D_608, C_607), k6_partfun1(B_606)) | ~m1_subset_1(D_608, k1_zfmisc_1(k2_zfmisc_1(B_606, A_605))) | ~v1_funct_2(D_608, B_606, A_605) | ~v1_funct_1(D_608) | ~m1_subset_1(C_607, k1_zfmisc_1(k2_zfmisc_1(A_605, B_606))) | ~v1_funct_2(C_607, A_605, B_606) | ~v1_funct_1(C_607))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.84/2.20  tff(c_3783, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_6')='#skF_3' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_68, c_3780])).
% 5.84/2.20  tff(c_3786, plain, (k2_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_80, c_78, c_76, c_3321, c_3783])).
% 5.84/2.20  tff(c_50, plain, (![B_32]: (v2_funct_2(B_32, k2_relat_1(B_32)) | ~v5_relat_1(B_32, k2_relat_1(B_32)) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.84/2.20  tff(c_3797, plain, (v2_funct_2('#skF_6', k2_relat_1('#skF_6')) | ~v5_relat_1('#skF_6', '#skF_3') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3786, c_50])).
% 5.84/2.20  tff(c_3807, plain, (v2_funct_2('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3064, c_3206, c_3786, c_3797])).
% 5.84/2.20  tff(c_3809, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2960, c_3807])).
% 5.84/2.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.84/2.20  
% 5.84/2.20  Inference rules
% 5.84/2.20  ----------------------
% 5.84/2.20  #Ref     : 0
% 5.84/2.20  #Sup     : 760
% 5.84/2.20  #Fact    : 0
% 5.84/2.20  #Define  : 0
% 5.84/2.20  #Split   : 14
% 5.84/2.20  #Chain   : 0
% 5.84/2.20  #Close   : 0
% 5.84/2.20  
% 5.84/2.20  Ordering : KBO
% 5.84/2.20  
% 5.84/2.20  Simplification rules
% 5.84/2.20  ----------------------
% 5.84/2.20  #Subsume      : 32
% 5.84/2.20  #Demod        : 631
% 5.84/2.20  #Tautology    : 293
% 5.84/2.20  #SimpNegUnit  : 13
% 5.84/2.20  #BackRed      : 127
% 5.84/2.20  
% 5.84/2.20  #Partial instantiations: 0
% 5.84/2.20  #Strategies tried      : 1
% 5.84/2.20  
% 5.84/2.20  Timing (in seconds)
% 5.84/2.20  ----------------------
% 5.84/2.20  Preprocessing        : 0.36
% 5.84/2.20  Parsing              : 0.19
% 5.84/2.20  CNF conversion       : 0.03
% 5.84/2.20  Main loop            : 1.03
% 5.84/2.20  Inferencing          : 0.36
% 5.84/2.20  Reduction            : 0.38
% 5.84/2.20  Demodulation         : 0.28
% 5.84/2.20  BG Simplification    : 0.04
% 5.84/2.20  Subsumption          : 0.16
% 5.84/2.20  Abstraction          : 0.04
% 5.84/2.20  MUC search           : 0.00
% 5.84/2.20  Cooper               : 0.00
% 5.84/2.20  Total                : 1.43
% 5.84/2.20  Index Insertion      : 0.00
% 5.84/2.20  Index Deletion       : 0.00
% 5.84/2.20  Index Matching       : 0.00
% 5.84/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
