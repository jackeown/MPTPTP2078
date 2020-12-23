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
% DateTime   : Thu Dec  3 10:12:06 EST 2020

% Result     : Theorem 7.51s
% Output     : CNFRefutation 7.78s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 307 expanded)
%              Number of leaves         :   50 ( 124 expanded)
%              Depth                    :   12
%              Number of atoms          :  220 ( 700 expanded)
%              Number of equality atoms :   34 (  89 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_180,negated_conjecture,(
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

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_121,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_119,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_99,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_160,axiom,(
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
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_57,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_138,axiom,(
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

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_66,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_127,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_76,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_489,plain,(
    ! [C_133,A_134,B_135] :
      ( v1_xboole_0(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135)))
      | ~ v1_xboole_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_511,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_489])).

tff(c_514,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_511])).

tff(c_80,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_78,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_74,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_72,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_70,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_58,plain,(
    ! [A_46] : k6_relat_1(A_46) = k6_partfun1(A_46) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_30,plain,(
    ! [A_15] : v2_funct_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_82,plain,(
    ! [A_15] : v2_funct_1(k6_partfun1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_30])).

tff(c_54,plain,(
    ! [E_44,C_42,F_45,A_40,D_43,B_41] :
      ( m1_subset_1(k1_partfun1(A_40,B_41,C_42,D_43,E_44,F_45),k1_zfmisc_1(k2_zfmisc_1(A_40,D_43)))
      | ~ m1_subset_1(F_45,k1_zfmisc_1(k2_zfmisc_1(C_42,D_43)))
      | ~ v1_funct_1(F_45)
      | ~ m1_subset_1(E_44,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41)))
      | ~ v1_funct_1(E_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_48,plain,(
    ! [A_37] : m1_subset_1(k6_relat_1(A_37),k1_zfmisc_1(k2_zfmisc_1(A_37,A_37))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_81,plain,(
    ! [A_37] : m1_subset_1(k6_partfun1(A_37),k1_zfmisc_1(k2_zfmisc_1(A_37,A_37))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_48])).

tff(c_68,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_4092,plain,(
    ! [D_439,C_440,A_441,B_442] :
      ( D_439 = C_440
      | ~ r2_relset_1(A_441,B_442,C_440,D_439)
      | ~ m1_subset_1(D_439,k1_zfmisc_1(k2_zfmisc_1(A_441,B_442)))
      | ~ m1_subset_1(C_440,k1_zfmisc_1(k2_zfmisc_1(A_441,B_442))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4098,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_68,c_4092])).

tff(c_4109,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_4098])).

tff(c_4110,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_4109])).

tff(c_5543,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_4110])).

tff(c_5547,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_5543])).

tff(c_5548,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_4109])).

tff(c_64,plain,(
    ! [D_55,B_53,E_57,A_52,C_54] :
      ( k1_xboole_0 = C_54
      | v2_funct_1(D_55)
      | ~ v2_funct_1(k1_partfun1(A_52,B_53,B_53,C_54,D_55,E_57))
      | ~ m1_subset_1(E_57,k1_zfmisc_1(k2_zfmisc_1(B_53,C_54)))
      | ~ v1_funct_2(E_57,B_53,C_54)
      | ~ v1_funct_1(E_57)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | ~ v1_funct_2(D_55,A_52,B_53)
      | ~ v1_funct_1(D_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_6988,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5548,c_64])).

tff(c_6997,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_72,c_70,c_82,c_6988])).

tff(c_6998,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_6997])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_7038,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6998,c_8])).

tff(c_7040,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_514,c_7038])).

tff(c_7041,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_511])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_84,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_235,plain,(
    ! [C_92,B_93,A_94] :
      ( ~ v1_xboole_0(C_92)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(C_92))
      | ~ r2_hidden(A_94,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_259,plain,(
    ! [A_97,A_98] :
      ( ~ v1_xboole_0(A_97)
      | ~ r2_hidden(A_98,A_97) ) ),
    inference(resolution,[status(thm)],[c_84,c_235])).

tff(c_263,plain,(
    ! [A_1,B_2] :
      ( ~ v1_xboole_0(A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_259])).

tff(c_312,plain,(
    ! [C_115,B_116,A_117] :
      ( v1_xboole_0(C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(B_116,A_117)))
      | ~ v1_xboole_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_421,plain,(
    ! [B_125,A_126] :
      ( v1_xboole_0(k2_zfmisc_1(B_125,A_126))
      | ~ v1_xboole_0(A_126) ) ),
    inference(resolution,[status(thm)],[c_84,c_312])).

tff(c_102,plain,(
    ! [A_63] : k6_relat_1(A_63) = k6_partfun1(A_63) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_26,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_108,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_26])).

tff(c_128,plain,(
    ! [A_65] : m1_subset_1(k6_partfun1(A_65),k1_zfmisc_1(k2_zfmisc_1(A_65,A_65))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_48])).

tff(c_131,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_128])).

tff(c_246,plain,(
    ! [A_94] :
      ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
      | ~ r2_hidden(A_94,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_131,c_235])).

tff(c_275,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_246])).

tff(c_435,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_421,c_275])).

tff(c_449,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_435])).

tff(c_452,plain,(
    ! [A_127] : ~ r2_hidden(A_127,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_462,plain,(
    ! [B_131] : r1_tarski(k1_xboole_0,B_131) ),
    inference(resolution,[status(thm)],[c_6,c_452])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_466,plain,(
    ! [B_132] :
      ( k1_xboole_0 = B_132
      | ~ r1_tarski(B_132,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_462,c_10])).

tff(c_7043,plain,(
    ! [A_625] :
      ( k1_xboole_0 = A_625
      | ~ v1_xboole_0(A_625) ) ),
    inference(resolution,[status(thm)],[c_263,c_466])).

tff(c_7057,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_7041,c_7043])).

tff(c_7042,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_511])).

tff(c_7056,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_7042,c_7043])).

tff(c_7100,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7057,c_7056])).

tff(c_121,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_82])).

tff(c_7069,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7056,c_121])).

tff(c_7105,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7100,c_7069])).

tff(c_7117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_7105])).

tff(c_7118,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_7125,plain,(
    ! [C_632,A_633,B_634] :
      ( v1_relat_1(C_632)
      | ~ m1_subset_1(C_632,k1_zfmisc_1(k2_zfmisc_1(A_633,B_634))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_7147,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_7125])).

tff(c_7882,plain,(
    ! [A_730,B_731,C_732] :
      ( k2_relset_1(A_730,B_731,C_732) = k2_relat_1(C_732)
      | ~ m1_subset_1(C_732,k1_zfmisc_1(k2_zfmisc_1(A_730,B_731))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_7904,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_7882])).

tff(c_8714,plain,(
    ! [A_803,B_804,C_805,D_806] :
      ( k2_relset_1(A_803,B_804,C_805) = B_804
      | ~ r2_relset_1(B_804,B_804,k1_partfun1(B_804,A_803,A_803,B_804,D_806,C_805),k6_partfun1(B_804))
      | ~ m1_subset_1(D_806,k1_zfmisc_1(k2_zfmisc_1(B_804,A_803)))
      | ~ v1_funct_2(D_806,B_804,A_803)
      | ~ v1_funct_1(D_806)
      | ~ m1_subset_1(C_805,k1_zfmisc_1(k2_zfmisc_1(A_803,B_804)))
      | ~ v1_funct_2(C_805,A_803,B_804)
      | ~ v1_funct_1(C_805) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_8726,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_8714])).

tff(c_8732,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_80,c_78,c_76,c_7904,c_8726])).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_7430,plain,(
    ! [B_692,A_693] :
      ( v5_relat_1(B_692,A_693)
      | ~ r1_tarski(k2_relat_1(B_692),A_693)
      | ~ v1_relat_1(B_692) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_7444,plain,(
    ! [B_692] :
      ( v5_relat_1(B_692,k2_relat_1(B_692))
      | ~ v1_relat_1(B_692) ) ),
    inference(resolution,[status(thm)],[c_14,c_7430])).

tff(c_7693,plain,(
    ! [B_718] :
      ( v2_funct_2(B_718,k2_relat_1(B_718))
      | ~ v5_relat_1(B_718,k2_relat_1(B_718))
      | ~ v1_relat_1(B_718) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_7704,plain,(
    ! [B_692] :
      ( v2_funct_2(B_692,k2_relat_1(B_692))
      | ~ v1_relat_1(B_692) ) ),
    inference(resolution,[status(thm)],[c_7444,c_7693])).

tff(c_8740,plain,
    ( v2_funct_2('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_8732,c_7704])).

tff(c_8755,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7147,c_8740])).

tff(c_8757,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7118,c_8755])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:21:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.51/2.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.51/2.86  
% 7.51/2.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.51/2.87  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 7.51/2.87  
% 7.51/2.87  %Foreground sorts:
% 7.51/2.87  
% 7.51/2.87  
% 7.51/2.87  %Background operators:
% 7.51/2.87  
% 7.51/2.87  
% 7.51/2.87  %Foreground operators:
% 7.51/2.87  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.51/2.87  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.51/2.87  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.51/2.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.51/2.87  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.51/2.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.51/2.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.51/2.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.51/2.87  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.51/2.87  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.51/2.87  tff('#skF_5', type, '#skF_5': $i).
% 7.51/2.87  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.51/2.87  tff('#skF_2', type, '#skF_2': $i).
% 7.51/2.87  tff('#skF_3', type, '#skF_3': $i).
% 7.51/2.87  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 7.51/2.87  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.51/2.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.51/2.87  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.51/2.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.51/2.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.51/2.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.51/2.87  tff('#skF_4', type, '#skF_4': $i).
% 7.51/2.87  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.51/2.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.51/2.87  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.51/2.87  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.51/2.87  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 7.51/2.87  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.51/2.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.51/2.87  
% 7.78/2.89  tff(f_180, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 7.78/2.89  tff(f_78, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 7.78/2.89  tff(f_121, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.78/2.89  tff(f_61, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.78/2.89  tff(f_119, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.78/2.89  tff(f_99, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 7.78/2.89  tff(f_97, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.78/2.89  tff(f_160, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 7.78/2.89  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.78/2.89  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.78/2.89  tff(f_41, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 7.78/2.89  tff(f_43, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 7.78/2.89  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 7.78/2.89  tff(f_85, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 7.78/2.89  tff(f_57, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 7.78/2.89  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.78/2.89  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.78/2.89  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.78/2.89  tff(f_138, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 7.78/2.89  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 7.78/2.89  tff(f_107, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 7.78/2.89  tff(c_66, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_180])).
% 7.78/2.89  tff(c_127, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_66])).
% 7.78/2.89  tff(c_76, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_180])).
% 7.78/2.89  tff(c_489, plain, (![C_133, A_134, B_135]: (v1_xboole_0(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))) | ~v1_xboole_0(A_134))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.78/2.89  tff(c_511, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_76, c_489])).
% 7.78/2.89  tff(c_514, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_511])).
% 7.78/2.89  tff(c_80, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_180])).
% 7.78/2.89  tff(c_78, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 7.78/2.89  tff(c_74, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_180])).
% 7.78/2.89  tff(c_72, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_180])).
% 7.78/2.89  tff(c_70, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_180])).
% 7.78/2.89  tff(c_58, plain, (![A_46]: (k6_relat_1(A_46)=k6_partfun1(A_46))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.78/2.89  tff(c_30, plain, (![A_15]: (v2_funct_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.78/2.89  tff(c_82, plain, (![A_15]: (v2_funct_1(k6_partfun1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_30])).
% 7.78/2.89  tff(c_54, plain, (![E_44, C_42, F_45, A_40, D_43, B_41]: (m1_subset_1(k1_partfun1(A_40, B_41, C_42, D_43, E_44, F_45), k1_zfmisc_1(k2_zfmisc_1(A_40, D_43))) | ~m1_subset_1(F_45, k1_zfmisc_1(k2_zfmisc_1(C_42, D_43))) | ~v1_funct_1(F_45) | ~m1_subset_1(E_44, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))) | ~v1_funct_1(E_44))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.78/2.89  tff(c_48, plain, (![A_37]: (m1_subset_1(k6_relat_1(A_37), k1_zfmisc_1(k2_zfmisc_1(A_37, A_37))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.78/2.89  tff(c_81, plain, (![A_37]: (m1_subset_1(k6_partfun1(A_37), k1_zfmisc_1(k2_zfmisc_1(A_37, A_37))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_48])).
% 7.78/2.89  tff(c_68, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_180])).
% 7.78/2.89  tff(c_4092, plain, (![D_439, C_440, A_441, B_442]: (D_439=C_440 | ~r2_relset_1(A_441, B_442, C_440, D_439) | ~m1_subset_1(D_439, k1_zfmisc_1(k2_zfmisc_1(A_441, B_442))) | ~m1_subset_1(C_440, k1_zfmisc_1(k2_zfmisc_1(A_441, B_442))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.78/2.89  tff(c_4098, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_68, c_4092])).
% 7.78/2.89  tff(c_4109, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_4098])).
% 7.78/2.89  tff(c_4110, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_4109])).
% 7.78/2.89  tff(c_5543, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_4110])).
% 7.78/2.89  tff(c_5547, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_5543])).
% 7.78/2.89  tff(c_5548, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_4109])).
% 7.78/2.89  tff(c_64, plain, (![D_55, B_53, E_57, A_52, C_54]: (k1_xboole_0=C_54 | v2_funct_1(D_55) | ~v2_funct_1(k1_partfun1(A_52, B_53, B_53, C_54, D_55, E_57)) | ~m1_subset_1(E_57, k1_zfmisc_1(k2_zfmisc_1(B_53, C_54))) | ~v1_funct_2(E_57, B_53, C_54) | ~v1_funct_1(E_57) | ~m1_subset_1(D_55, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))) | ~v1_funct_2(D_55, A_52, B_53) | ~v1_funct_1(D_55))), inference(cnfTransformation, [status(thm)], [f_160])).
% 7.78/2.89  tff(c_6988, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5548, c_64])).
% 7.78/2.89  tff(c_6997, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_72, c_70, c_82, c_6988])).
% 7.78/2.89  tff(c_6998, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_127, c_6997])).
% 7.78/2.89  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.78/2.89  tff(c_7038, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6998, c_8])).
% 7.78/2.89  tff(c_7040, plain, $false, inference(negUnitSimplification, [status(thm)], [c_514, c_7038])).
% 7.78/2.89  tff(c_7041, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_511])).
% 7.78/2.89  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.78/2.89  tff(c_16, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.78/2.89  tff(c_18, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.78/2.89  tff(c_84, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18])).
% 7.78/2.89  tff(c_235, plain, (![C_92, B_93, A_94]: (~v1_xboole_0(C_92) | ~m1_subset_1(B_93, k1_zfmisc_1(C_92)) | ~r2_hidden(A_94, B_93))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.78/2.89  tff(c_259, plain, (![A_97, A_98]: (~v1_xboole_0(A_97) | ~r2_hidden(A_98, A_97))), inference(resolution, [status(thm)], [c_84, c_235])).
% 7.78/2.89  tff(c_263, plain, (![A_1, B_2]: (~v1_xboole_0(A_1) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_259])).
% 7.78/2.89  tff(c_312, plain, (![C_115, B_116, A_117]: (v1_xboole_0(C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(B_116, A_117))) | ~v1_xboole_0(A_117))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.78/2.89  tff(c_421, plain, (![B_125, A_126]: (v1_xboole_0(k2_zfmisc_1(B_125, A_126)) | ~v1_xboole_0(A_126))), inference(resolution, [status(thm)], [c_84, c_312])).
% 7.78/2.89  tff(c_102, plain, (![A_63]: (k6_relat_1(A_63)=k6_partfun1(A_63))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.78/2.89  tff(c_26, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.78/2.89  tff(c_108, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_102, c_26])).
% 7.78/2.89  tff(c_128, plain, (![A_65]: (m1_subset_1(k6_partfun1(A_65), k1_zfmisc_1(k2_zfmisc_1(A_65, A_65))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_48])).
% 7.78/2.89  tff(c_131, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_128])).
% 7.78/2.89  tff(c_246, plain, (![A_94]: (~v1_xboole_0(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)) | ~r2_hidden(A_94, k1_xboole_0))), inference(resolution, [status(thm)], [c_131, c_235])).
% 7.78/2.89  tff(c_275, plain, (~v1_xboole_0(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_246])).
% 7.78/2.89  tff(c_435, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_421, c_275])).
% 7.78/2.89  tff(c_449, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_435])).
% 7.78/2.89  tff(c_452, plain, (![A_127]: (~r2_hidden(A_127, k1_xboole_0))), inference(splitRight, [status(thm)], [c_246])).
% 7.78/2.89  tff(c_462, plain, (![B_131]: (r1_tarski(k1_xboole_0, B_131))), inference(resolution, [status(thm)], [c_6, c_452])).
% 7.78/2.89  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.78/2.89  tff(c_466, plain, (![B_132]: (k1_xboole_0=B_132 | ~r1_tarski(B_132, k1_xboole_0))), inference(resolution, [status(thm)], [c_462, c_10])).
% 7.78/2.89  tff(c_7043, plain, (![A_625]: (k1_xboole_0=A_625 | ~v1_xboole_0(A_625))), inference(resolution, [status(thm)], [c_263, c_466])).
% 7.78/2.89  tff(c_7057, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_7041, c_7043])).
% 7.78/2.89  tff(c_7042, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_511])).
% 7.78/2.89  tff(c_7056, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_7042, c_7043])).
% 7.78/2.89  tff(c_7100, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7057, c_7056])).
% 7.78/2.89  tff(c_121, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_108, c_82])).
% 7.78/2.89  tff(c_7069, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7056, c_121])).
% 7.78/2.89  tff(c_7105, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7100, c_7069])).
% 7.78/2.89  tff(c_7117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_127, c_7105])).
% 7.78/2.89  tff(c_7118, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_66])).
% 7.78/2.89  tff(c_7125, plain, (![C_632, A_633, B_634]: (v1_relat_1(C_632) | ~m1_subset_1(C_632, k1_zfmisc_1(k2_zfmisc_1(A_633, B_634))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.78/2.89  tff(c_7147, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_70, c_7125])).
% 7.78/2.89  tff(c_7882, plain, (![A_730, B_731, C_732]: (k2_relset_1(A_730, B_731, C_732)=k2_relat_1(C_732) | ~m1_subset_1(C_732, k1_zfmisc_1(k2_zfmisc_1(A_730, B_731))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.78/2.89  tff(c_7904, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_70, c_7882])).
% 7.78/2.89  tff(c_8714, plain, (![A_803, B_804, C_805, D_806]: (k2_relset_1(A_803, B_804, C_805)=B_804 | ~r2_relset_1(B_804, B_804, k1_partfun1(B_804, A_803, A_803, B_804, D_806, C_805), k6_partfun1(B_804)) | ~m1_subset_1(D_806, k1_zfmisc_1(k2_zfmisc_1(B_804, A_803))) | ~v1_funct_2(D_806, B_804, A_803) | ~v1_funct_1(D_806) | ~m1_subset_1(C_805, k1_zfmisc_1(k2_zfmisc_1(A_803, B_804))) | ~v1_funct_2(C_805, A_803, B_804) | ~v1_funct_1(C_805))), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.78/2.89  tff(c_8726, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_68, c_8714])).
% 7.78/2.89  tff(c_8732, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_80, c_78, c_76, c_7904, c_8726])).
% 7.78/2.89  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.78/2.89  tff(c_7430, plain, (![B_692, A_693]: (v5_relat_1(B_692, A_693) | ~r1_tarski(k2_relat_1(B_692), A_693) | ~v1_relat_1(B_692))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.78/2.89  tff(c_7444, plain, (![B_692]: (v5_relat_1(B_692, k2_relat_1(B_692)) | ~v1_relat_1(B_692))), inference(resolution, [status(thm)], [c_14, c_7430])).
% 7.78/2.89  tff(c_7693, plain, (![B_718]: (v2_funct_2(B_718, k2_relat_1(B_718)) | ~v5_relat_1(B_718, k2_relat_1(B_718)) | ~v1_relat_1(B_718))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.78/2.89  tff(c_7704, plain, (![B_692]: (v2_funct_2(B_692, k2_relat_1(B_692)) | ~v1_relat_1(B_692))), inference(resolution, [status(thm)], [c_7444, c_7693])).
% 7.78/2.89  tff(c_8740, plain, (v2_funct_2('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_8732, c_7704])).
% 7.78/2.89  tff(c_8755, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7147, c_8740])).
% 7.78/2.89  tff(c_8757, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7118, c_8755])).
% 7.78/2.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.78/2.89  
% 7.78/2.89  Inference rules
% 7.78/2.89  ----------------------
% 7.78/2.89  #Ref     : 0
% 7.78/2.89  #Sup     : 2135
% 7.78/2.89  #Fact    : 0
% 7.78/2.89  #Define  : 0
% 7.78/2.89  #Split   : 23
% 7.78/2.89  #Chain   : 0
% 7.78/2.89  #Close   : 0
% 7.78/2.89  
% 7.78/2.89  Ordering : KBO
% 7.78/2.89  
% 7.78/2.89  Simplification rules
% 7.78/2.89  ----------------------
% 7.78/2.89  #Subsume      : 306
% 7.78/2.89  #Demod        : 1258
% 7.78/2.89  #Tautology    : 956
% 7.78/2.89  #SimpNegUnit  : 7
% 7.78/2.89  #BackRed      : 77
% 7.78/2.89  
% 7.78/2.89  #Partial instantiations: 0
% 7.78/2.89  #Strategies tried      : 1
% 7.78/2.89  
% 7.78/2.89  Timing (in seconds)
% 7.78/2.89  ----------------------
% 7.78/2.89  Preprocessing        : 0.60
% 7.78/2.89  Parsing              : 0.32
% 7.78/2.89  CNF conversion       : 0.05
% 7.78/2.89  Main loop            : 1.45
% 7.78/2.89  Inferencing          : 0.46
% 7.78/2.89  Reduction            : 0.50
% 7.78/2.89  Demodulation         : 0.37
% 7.78/2.89  BG Simplification    : 0.06
% 7.78/2.89  Subsumption          : 0.31
% 7.78/2.89  Abstraction          : 0.06
% 7.78/2.89  MUC search           : 0.00
% 7.78/2.89  Cooper               : 0.00
% 7.78/2.89  Total                : 2.10
% 7.78/2.89  Index Insertion      : 0.00
% 7.78/2.89  Index Deletion       : 0.00
% 7.78/2.89  Index Matching       : 0.00
% 7.78/2.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
