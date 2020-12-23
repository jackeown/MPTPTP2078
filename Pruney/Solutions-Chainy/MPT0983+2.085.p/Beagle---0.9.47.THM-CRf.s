%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:13 EST 2020

% Result     : Theorem 5.99s
% Output     : CNFRefutation 6.34s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 280 expanded)
%              Number of leaves         :   50 ( 123 expanded)
%              Depth                    :   11
%              Number of atoms          :  210 ( 763 expanded)
%              Number of equality atoms :   31 (  76 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_185,negated_conjecture,(
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

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_126,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_124,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_104,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_165,axiom,(
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

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_143,axiom,(
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

tff(f_112,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_62,plain,
    ( ~ v2_funct_2('#skF_7','#skF_4')
    | ~ v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_92,plain,(
    ~ v2_funct_1('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( v1_xboole_0(k2_zfmisc_1(A_7,B_8))
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_72,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_192,plain,(
    ! [C_84,B_85,A_86] :
      ( ~ v1_xboole_0(C_84)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(C_84))
      | ~ r2_hidden(A_86,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_201,plain,(
    ! [A_86] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(A_86,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_72,c_192])).

tff(c_274,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_201])).

tff(c_282,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_274])).

tff(c_76,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_74,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_70,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_68,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_66,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_54,plain,(
    ! [A_49] : k6_relat_1(A_49) = k6_partfun1(A_49) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_22,plain,(
    ! [A_13] : v2_funct_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_78,plain,(
    ! [A_13] : v2_funct_1(k6_partfun1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_22])).

tff(c_50,plain,(
    ! [E_47,F_48,D_46,C_45,A_43,B_44] :
      ( m1_subset_1(k1_partfun1(A_43,B_44,C_45,D_46,E_47,F_48),k1_zfmisc_1(k2_zfmisc_1(A_43,D_46)))
      | ~ m1_subset_1(F_48,k1_zfmisc_1(k2_zfmisc_1(C_45,D_46)))
      | ~ v1_funct_1(F_48)
      | ~ m1_subset_1(E_47,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44)))
      | ~ v1_funct_1(E_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_44,plain,(
    ! [A_40] : m1_subset_1(k6_relat_1(A_40),k1_zfmisc_1(k2_zfmisc_1(A_40,A_40))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_77,plain,(
    ! [A_40] : m1_subset_1(k6_partfun1(A_40),k1_zfmisc_1(k2_zfmisc_1(A_40,A_40))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_44])).

tff(c_64,plain,(
    r2_relset_1('#skF_4','#skF_4',k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7'),k6_partfun1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_490,plain,(
    ! [D_125,C_126,A_127,B_128] :
      ( D_125 = C_126
      | ~ r2_relset_1(A_127,B_128,C_126,D_125)
      | ~ m1_subset_1(D_125,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128)))
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_500,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7') = k6_partfun1('#skF_4')
    | ~ m1_subset_1(k6_partfun1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
    | ~ m1_subset_1(k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_64,c_490])).

tff(c_519,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7') = k6_partfun1('#skF_4')
    | ~ m1_subset_1(k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_500])).

tff(c_607,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_519])).

tff(c_1659,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_607])).

tff(c_1663,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_70,c_66,c_1659])).

tff(c_1664,plain,(
    k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7') = k6_partfun1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_519])).

tff(c_3050,plain,(
    ! [B_249,E_252,C_253,D_250,A_251] :
      ( k1_xboole_0 = C_253
      | v2_funct_1(D_250)
      | ~ v2_funct_1(k1_partfun1(A_251,B_249,B_249,C_253,D_250,E_252))
      | ~ m1_subset_1(E_252,k1_zfmisc_1(k2_zfmisc_1(B_249,C_253)))
      | ~ v1_funct_2(E_252,B_249,C_253)
      | ~ v1_funct_1(E_252)
      | ~ m1_subset_1(D_250,k1_zfmisc_1(k2_zfmisc_1(A_251,B_249)))
      | ~ v1_funct_2(D_250,A_251,B_249)
      | ~ v1_funct_1(D_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_3052,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_funct_1('#skF_6')
    | ~ v2_funct_1(k6_partfun1('#skF_4'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1664,c_3050])).

tff(c_3054,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_68,c_66,c_78,c_3052])).

tff(c_3055,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_3054])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3102,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3055,c_6])).

tff(c_3104,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_282,c_3102])).

tff(c_3107,plain,(
    ! [A_254] : ~ r2_hidden(A_254,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_3112,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_3107])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3119,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3112,c_8])).

tff(c_100,plain,(
    ! [A_69,B_70] :
      ( v1_xboole_0(k2_zfmisc_1(A_69,B_70))
      | ~ v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_115,plain,(
    ! [A_74,B_75] :
      ( k2_zfmisc_1(A_74,B_75) = k1_xboole_0
      | ~ v1_xboole_0(A_74) ) ),
    inference(resolution,[status(thm)],[c_100,c_8])).

tff(c_121,plain,(
    ! [B_75] : k2_zfmisc_1(k1_xboole_0,B_75) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_115])).

tff(c_151,plain,(
    ! [A_80] : m1_subset_1(k6_partfun1(A_80),k1_zfmisc_1(k2_zfmisc_1(A_80,A_80))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_44])).

tff(c_155,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_151])).

tff(c_14,plain,(
    ! [C_11,B_10,A_9] :
      ( ~ v1_xboole_0(C_11)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(C_11))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_203,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_9,k6_partfun1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_155,c_14])).

tff(c_207,plain,(
    ! [A_87] : ~ r2_hidden(A_87,k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_203])).

tff(c_212,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_4,c_207])).

tff(c_220,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_212,c_8])).

tff(c_232,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_78])).

tff(c_3128,plain,(
    v2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3119,c_232])).

tff(c_3143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_3128])).

tff(c_3144,plain,(
    ~ v2_funct_2('#skF_7','#skF_4') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_3210,plain,(
    ! [C_271,A_272,B_273] :
      ( v1_relat_1(C_271)
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1(A_272,B_273))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3225,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_3210])).

tff(c_3244,plain,(
    ! [C_274,B_275,A_276] :
      ( v5_relat_1(C_274,B_275)
      | ~ m1_subset_1(C_274,k1_zfmisc_1(k2_zfmisc_1(A_276,B_275))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3259,plain,(
    v5_relat_1('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_3244])).

tff(c_3423,plain,(
    ! [A_297,B_298,D_299] :
      ( r2_relset_1(A_297,B_298,D_299,D_299)
      | ~ m1_subset_1(D_299,k1_zfmisc_1(k2_zfmisc_1(A_297,B_298))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_3432,plain,(
    ! [A_40] : r2_relset_1(A_40,A_40,k6_partfun1(A_40),k6_partfun1(A_40)) ),
    inference(resolution,[status(thm)],[c_77,c_3423])).

tff(c_3550,plain,(
    ! [A_307,B_308,C_309] :
      ( k2_relset_1(A_307,B_308,C_309) = k2_relat_1(C_309)
      | ~ m1_subset_1(C_309,k1_zfmisc_1(k2_zfmisc_1(A_307,B_308))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3565,plain,(
    k2_relset_1('#skF_5','#skF_4','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_3550])).

tff(c_3777,plain,(
    ! [D_324,C_325,A_326,B_327] :
      ( D_324 = C_325
      | ~ r2_relset_1(A_326,B_327,C_325,D_324)
      | ~ m1_subset_1(D_324,k1_zfmisc_1(k2_zfmisc_1(A_326,B_327)))
      | ~ m1_subset_1(C_325,k1_zfmisc_1(k2_zfmisc_1(A_326,B_327))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_3787,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7') = k6_partfun1('#skF_4')
    | ~ m1_subset_1(k6_partfun1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
    | ~ m1_subset_1(k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_64,c_3777])).

tff(c_3806,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7') = k6_partfun1('#skF_4')
    | ~ m1_subset_1(k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_3787])).

tff(c_4990,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_3806])).

tff(c_5314,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_4990])).

tff(c_5318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_70,c_66,c_5314])).

tff(c_5319,plain,(
    k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7') = k6_partfun1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_3806])).

tff(c_5854,plain,(
    ! [A_430,B_431,C_432,D_433] :
      ( k2_relset_1(A_430,B_431,C_432) = B_431
      | ~ r2_relset_1(B_431,B_431,k1_partfun1(B_431,A_430,A_430,B_431,D_433,C_432),k6_partfun1(B_431))
      | ~ m1_subset_1(D_433,k1_zfmisc_1(k2_zfmisc_1(B_431,A_430)))
      | ~ v1_funct_2(D_433,B_431,A_430)
      | ~ v1_funct_1(D_433)
      | ~ m1_subset_1(C_432,k1_zfmisc_1(k2_zfmisc_1(A_430,B_431)))
      | ~ v1_funct_2(C_432,A_430,B_431)
      | ~ v1_funct_1(C_432) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_5857,plain,
    ( k2_relset_1('#skF_5','#skF_4','#skF_7') = '#skF_4'
    | ~ r2_relset_1('#skF_4','#skF_4',k6_partfun1('#skF_4'),k6_partfun1('#skF_4'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
    | ~ v1_funct_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_5319,c_5854])).

tff(c_5877,plain,(
    k2_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_76,c_74,c_72,c_3432,c_3565,c_5857])).

tff(c_46,plain,(
    ! [B_42] :
      ( v2_funct_2(B_42,k2_relat_1(B_42))
      | ~ v5_relat_1(B_42,k2_relat_1(B_42))
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_5893,plain,
    ( v2_funct_2('#skF_7',k2_relat_1('#skF_7'))
    | ~ v5_relat_1('#skF_7','#skF_4')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_5877,c_46])).

tff(c_5903,plain,(
    v2_funct_2('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3225,c_3259,c_5877,c_5893])).

tff(c_5905,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3144,c_5903])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:32:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.99/2.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.99/2.28  
% 5.99/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.99/2.29  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4
% 5.99/2.29  
% 5.99/2.29  %Foreground sorts:
% 5.99/2.29  
% 5.99/2.29  
% 5.99/2.29  %Background operators:
% 5.99/2.29  
% 5.99/2.29  
% 5.99/2.29  %Foreground operators:
% 5.99/2.29  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.99/2.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.99/2.29  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.99/2.29  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.99/2.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.99/2.29  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.99/2.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.99/2.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.99/2.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.99/2.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.99/2.29  tff('#skF_7', type, '#skF_7': $i).
% 5.99/2.29  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.99/2.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.99/2.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.99/2.29  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.99/2.29  tff('#skF_5', type, '#skF_5': $i).
% 5.99/2.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.99/2.29  tff('#skF_6', type, '#skF_6': $i).
% 5.99/2.29  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.99/2.29  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.99/2.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.99/2.29  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.99/2.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.99/2.29  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.99/2.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.99/2.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.99/2.29  tff('#skF_4', type, '#skF_4': $i).
% 5.99/2.29  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.99/2.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.99/2.29  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.99/2.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.99/2.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.99/2.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.99/2.29  
% 6.34/2.31  tff(f_185, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 6.34/2.31  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.34/2.31  tff(f_42, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 6.34/2.31  tff(f_49, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 6.34/2.31  tff(f_126, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.34/2.31  tff(f_61, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 6.34/2.31  tff(f_124, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.34/2.31  tff(f_104, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 6.34/2.31  tff(f_102, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.34/2.31  tff(f_165, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 6.34/2.31  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.34/2.31  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 6.34/2.31  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.34/2.31  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.34/2.31  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.34/2.31  tff(f_143, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 6.34/2.31  tff(f_112, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 6.34/2.31  tff(c_62, plain, (~v2_funct_2('#skF_7', '#skF_4') | ~v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_185])).
% 6.34/2.31  tff(c_92, plain, (~v2_funct_1('#skF_6')), inference(splitLeft, [status(thm)], [c_62])).
% 6.34/2.31  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.34/2.31  tff(c_12, plain, (![A_7, B_8]: (v1_xboole_0(k2_zfmisc_1(A_7, B_8)) | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.34/2.31  tff(c_72, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_185])).
% 6.34/2.31  tff(c_192, plain, (![C_84, B_85, A_86]: (~v1_xboole_0(C_84) | ~m1_subset_1(B_85, k1_zfmisc_1(C_84)) | ~r2_hidden(A_86, B_85))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.34/2.31  tff(c_201, plain, (![A_86]: (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(A_86, '#skF_6'))), inference(resolution, [status(thm)], [c_72, c_192])).
% 6.34/2.31  tff(c_274, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_201])).
% 6.34/2.31  tff(c_282, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_12, c_274])).
% 6.34/2.31  tff(c_76, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_185])).
% 6.34/2.31  tff(c_74, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_185])).
% 6.34/2.31  tff(c_70, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_185])).
% 6.34/2.31  tff(c_68, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_185])).
% 6.34/2.31  tff(c_66, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_185])).
% 6.34/2.31  tff(c_54, plain, (![A_49]: (k6_relat_1(A_49)=k6_partfun1(A_49))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.34/2.31  tff(c_22, plain, (![A_13]: (v2_funct_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.34/2.31  tff(c_78, plain, (![A_13]: (v2_funct_1(k6_partfun1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_22])).
% 6.34/2.31  tff(c_50, plain, (![E_47, F_48, D_46, C_45, A_43, B_44]: (m1_subset_1(k1_partfun1(A_43, B_44, C_45, D_46, E_47, F_48), k1_zfmisc_1(k2_zfmisc_1(A_43, D_46))) | ~m1_subset_1(F_48, k1_zfmisc_1(k2_zfmisc_1(C_45, D_46))) | ~v1_funct_1(F_48) | ~m1_subset_1(E_47, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))) | ~v1_funct_1(E_47))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.34/2.31  tff(c_44, plain, (![A_40]: (m1_subset_1(k6_relat_1(A_40), k1_zfmisc_1(k2_zfmisc_1(A_40, A_40))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.34/2.31  tff(c_77, plain, (![A_40]: (m1_subset_1(k6_partfun1(A_40), k1_zfmisc_1(k2_zfmisc_1(A_40, A_40))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_44])).
% 6.34/2.31  tff(c_64, plain, (r2_relset_1('#skF_4', '#skF_4', k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7'), k6_partfun1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_185])).
% 6.34/2.31  tff(c_490, plain, (![D_125, C_126, A_127, B_128]: (D_125=C_126 | ~r2_relset_1(A_127, B_128, C_126, D_125) | ~m1_subset_1(D_125, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.34/2.31  tff(c_500, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7')=k6_partfun1('#skF_4') | ~m1_subset_1(k6_partfun1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~m1_subset_1(k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(resolution, [status(thm)], [c_64, c_490])).
% 6.34/2.31  tff(c_519, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7')=k6_partfun1('#skF_4') | ~m1_subset_1(k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_500])).
% 6.34/2.31  tff(c_607, plain, (~m1_subset_1(k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(splitLeft, [status(thm)], [c_519])).
% 6.34/2.31  tff(c_1659, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_607])).
% 6.34/2.31  tff(c_1663, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_70, c_66, c_1659])).
% 6.34/2.31  tff(c_1664, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7')=k6_partfun1('#skF_4')), inference(splitRight, [status(thm)], [c_519])).
% 6.34/2.31  tff(c_3050, plain, (![B_249, E_252, C_253, D_250, A_251]: (k1_xboole_0=C_253 | v2_funct_1(D_250) | ~v2_funct_1(k1_partfun1(A_251, B_249, B_249, C_253, D_250, E_252)) | ~m1_subset_1(E_252, k1_zfmisc_1(k2_zfmisc_1(B_249, C_253))) | ~v1_funct_2(E_252, B_249, C_253) | ~v1_funct_1(E_252) | ~m1_subset_1(D_250, k1_zfmisc_1(k2_zfmisc_1(A_251, B_249))) | ~v1_funct_2(D_250, A_251, B_249) | ~v1_funct_1(D_250))), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.34/2.31  tff(c_3052, plain, (k1_xboole_0='#skF_4' | v2_funct_1('#skF_6') | ~v2_funct_1(k6_partfun1('#skF_4')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1664, c_3050])).
% 6.34/2.31  tff(c_3054, plain, (k1_xboole_0='#skF_4' | v2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_68, c_66, c_78, c_3052])).
% 6.34/2.31  tff(c_3055, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_92, c_3054])).
% 6.34/2.31  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.34/2.31  tff(c_3102, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3055, c_6])).
% 6.34/2.31  tff(c_3104, plain, $false, inference(negUnitSimplification, [status(thm)], [c_282, c_3102])).
% 6.34/2.31  tff(c_3107, plain, (![A_254]: (~r2_hidden(A_254, '#skF_6'))), inference(splitRight, [status(thm)], [c_201])).
% 6.34/2.31  tff(c_3112, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_4, c_3107])).
% 6.34/2.31  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.34/2.31  tff(c_3119, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_3112, c_8])).
% 6.34/2.31  tff(c_100, plain, (![A_69, B_70]: (v1_xboole_0(k2_zfmisc_1(A_69, B_70)) | ~v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.34/2.31  tff(c_115, plain, (![A_74, B_75]: (k2_zfmisc_1(A_74, B_75)=k1_xboole_0 | ~v1_xboole_0(A_74))), inference(resolution, [status(thm)], [c_100, c_8])).
% 6.34/2.31  tff(c_121, plain, (![B_75]: (k2_zfmisc_1(k1_xboole_0, B_75)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_115])).
% 6.34/2.31  tff(c_151, plain, (![A_80]: (m1_subset_1(k6_partfun1(A_80), k1_zfmisc_1(k2_zfmisc_1(A_80, A_80))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_44])).
% 6.34/2.31  tff(c_155, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_121, c_151])).
% 6.34/2.31  tff(c_14, plain, (![C_11, B_10, A_9]: (~v1_xboole_0(C_11) | ~m1_subset_1(B_10, k1_zfmisc_1(C_11)) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.34/2.31  tff(c_203, plain, (![A_9]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_9, k6_partfun1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_155, c_14])).
% 6.34/2.31  tff(c_207, plain, (![A_87]: (~r2_hidden(A_87, k6_partfun1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_203])).
% 6.34/2.31  tff(c_212, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_207])).
% 6.34/2.31  tff(c_220, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_212, c_8])).
% 6.34/2.31  tff(c_232, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_220, c_78])).
% 6.34/2.31  tff(c_3128, plain, (v2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3119, c_232])).
% 6.34/2.31  tff(c_3143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_3128])).
% 6.34/2.31  tff(c_3144, plain, (~v2_funct_2('#skF_7', '#skF_4')), inference(splitRight, [status(thm)], [c_62])).
% 6.34/2.31  tff(c_3210, plain, (![C_271, A_272, B_273]: (v1_relat_1(C_271) | ~m1_subset_1(C_271, k1_zfmisc_1(k2_zfmisc_1(A_272, B_273))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.34/2.31  tff(c_3225, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_66, c_3210])).
% 6.34/2.31  tff(c_3244, plain, (![C_274, B_275, A_276]: (v5_relat_1(C_274, B_275) | ~m1_subset_1(C_274, k1_zfmisc_1(k2_zfmisc_1(A_276, B_275))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.34/2.31  tff(c_3259, plain, (v5_relat_1('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_66, c_3244])).
% 6.34/2.31  tff(c_3423, plain, (![A_297, B_298, D_299]: (r2_relset_1(A_297, B_298, D_299, D_299) | ~m1_subset_1(D_299, k1_zfmisc_1(k2_zfmisc_1(A_297, B_298))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.34/2.31  tff(c_3432, plain, (![A_40]: (r2_relset_1(A_40, A_40, k6_partfun1(A_40), k6_partfun1(A_40)))), inference(resolution, [status(thm)], [c_77, c_3423])).
% 6.34/2.31  tff(c_3550, plain, (![A_307, B_308, C_309]: (k2_relset_1(A_307, B_308, C_309)=k2_relat_1(C_309) | ~m1_subset_1(C_309, k1_zfmisc_1(k2_zfmisc_1(A_307, B_308))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.34/2.31  tff(c_3565, plain, (k2_relset_1('#skF_5', '#skF_4', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_66, c_3550])).
% 6.34/2.31  tff(c_3777, plain, (![D_324, C_325, A_326, B_327]: (D_324=C_325 | ~r2_relset_1(A_326, B_327, C_325, D_324) | ~m1_subset_1(D_324, k1_zfmisc_1(k2_zfmisc_1(A_326, B_327))) | ~m1_subset_1(C_325, k1_zfmisc_1(k2_zfmisc_1(A_326, B_327))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.34/2.31  tff(c_3787, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7')=k6_partfun1('#skF_4') | ~m1_subset_1(k6_partfun1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~m1_subset_1(k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(resolution, [status(thm)], [c_64, c_3777])).
% 6.34/2.31  tff(c_3806, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7')=k6_partfun1('#skF_4') | ~m1_subset_1(k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_3787])).
% 6.34/2.31  tff(c_4990, plain, (~m1_subset_1(k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(splitLeft, [status(thm)], [c_3806])).
% 6.34/2.31  tff(c_5314, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_4990])).
% 6.34/2.31  tff(c_5318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_70, c_66, c_5314])).
% 6.34/2.31  tff(c_5319, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7')=k6_partfun1('#skF_4')), inference(splitRight, [status(thm)], [c_3806])).
% 6.34/2.31  tff(c_5854, plain, (![A_430, B_431, C_432, D_433]: (k2_relset_1(A_430, B_431, C_432)=B_431 | ~r2_relset_1(B_431, B_431, k1_partfun1(B_431, A_430, A_430, B_431, D_433, C_432), k6_partfun1(B_431)) | ~m1_subset_1(D_433, k1_zfmisc_1(k2_zfmisc_1(B_431, A_430))) | ~v1_funct_2(D_433, B_431, A_430) | ~v1_funct_1(D_433) | ~m1_subset_1(C_432, k1_zfmisc_1(k2_zfmisc_1(A_430, B_431))) | ~v1_funct_2(C_432, A_430, B_431) | ~v1_funct_1(C_432))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.34/2.31  tff(c_5857, plain, (k2_relset_1('#skF_5', '#skF_4', '#skF_7')='#skF_4' | ~r2_relset_1('#skF_4', '#skF_4', k6_partfun1('#skF_4'), k6_partfun1('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_5319, c_5854])).
% 6.34/2.31  tff(c_5877, plain, (k2_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_76, c_74, c_72, c_3432, c_3565, c_5857])).
% 6.34/2.31  tff(c_46, plain, (![B_42]: (v2_funct_2(B_42, k2_relat_1(B_42)) | ~v5_relat_1(B_42, k2_relat_1(B_42)) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.34/2.31  tff(c_5893, plain, (v2_funct_2('#skF_7', k2_relat_1('#skF_7')) | ~v5_relat_1('#skF_7', '#skF_4') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_5877, c_46])).
% 6.34/2.31  tff(c_5903, plain, (v2_funct_2('#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3225, c_3259, c_5877, c_5893])).
% 6.34/2.31  tff(c_5905, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3144, c_5903])).
% 6.34/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.34/2.31  
% 6.34/2.31  Inference rules
% 6.34/2.31  ----------------------
% 6.34/2.31  #Ref     : 0
% 6.34/2.31  #Sup     : 1420
% 6.34/2.31  #Fact    : 0
% 6.34/2.31  #Define  : 0
% 6.34/2.31  #Split   : 19
% 6.34/2.31  #Chain   : 0
% 6.34/2.31  #Close   : 0
% 6.34/2.31  
% 6.34/2.31  Ordering : KBO
% 6.34/2.31  
% 6.34/2.31  Simplification rules
% 6.34/2.31  ----------------------
% 6.34/2.31  #Subsume      : 188
% 6.34/2.31  #Demod        : 1474
% 6.34/2.31  #Tautology    : 793
% 6.34/2.31  #SimpNegUnit  : 4
% 6.34/2.31  #BackRed      : 74
% 6.34/2.31  
% 6.34/2.31  #Partial instantiations: 0
% 6.34/2.31  #Strategies tried      : 1
% 6.34/2.31  
% 6.34/2.31  Timing (in seconds)
% 6.34/2.31  ----------------------
% 6.34/2.31  Preprocessing        : 0.41
% 6.34/2.31  Parsing              : 0.21
% 6.34/2.31  CNF conversion       : 0.03
% 6.34/2.31  Main loop            : 1.03
% 6.34/2.31  Inferencing          : 0.34
% 6.34/2.31  Reduction            : 0.36
% 6.34/2.31  Demodulation         : 0.27
% 6.34/2.31  BG Simplification    : 0.04
% 6.34/2.31  Subsumption          : 0.20
% 6.34/2.31  Abstraction          : 0.04
% 6.34/2.31  MUC search           : 0.00
% 6.34/2.31  Cooper               : 0.00
% 6.34/2.31  Total                : 1.48
% 6.34/2.31  Index Insertion      : 0.00
% 6.34/2.31  Index Deletion       : 0.00
% 6.34/2.31  Index Matching       : 0.00
% 6.34/2.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
