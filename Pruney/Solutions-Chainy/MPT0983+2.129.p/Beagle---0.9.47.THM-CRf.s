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
% DateTime   : Thu Dec  3 10:12:20 EST 2020

% Result     : Theorem 6.75s
% Output     : CNFRefutation 6.93s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 733 expanded)
%              Number of leaves         :   46 ( 265 expanded)
%              Depth                    :   10
%              Number of atoms          :  238 (2102 expanded)
%              Number of equality atoms :   57 ( 286 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(f_183,negated_conjecture,(
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

tff(f_124,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_118,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_122,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_163,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_76,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_75,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_141,axiom,(
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

tff(f_106,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_64,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_146,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_78,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_76,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_74,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_72,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_70,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_68,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_56,plain,(
    ! [A_40] : k6_relat_1(A_40) = k6_partfun1(A_40) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_32,plain,(
    ! [A_20] : v2_funct_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_79,plain,(
    ! [A_20] : v2_funct_1(k6_partfun1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_32])).

tff(c_48,plain,(
    ! [D_36,F_38,E_37,A_33,B_34,C_35] :
      ( m1_subset_1(k1_partfun1(A_33,B_34,C_35,D_36,E_37,F_38),k1_zfmisc_1(k2_zfmisc_1(A_33,D_36)))
      | ~ m1_subset_1(F_38,k1_zfmisc_1(k2_zfmisc_1(C_35,D_36)))
      | ~ v1_funct_1(F_38)
      | ~ m1_subset_1(E_37,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34)))
      | ~ v1_funct_1(E_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_54,plain,(
    ! [A_39] : m1_subset_1(k6_partfun1(A_39),k1_zfmisc_1(k2_zfmisc_1(A_39,A_39))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_66,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_2791,plain,(
    ! [D_357,C_358,A_359,B_360] :
      ( D_357 = C_358
      | ~ r2_relset_1(A_359,B_360,C_358,D_357)
      | ~ m1_subset_1(D_357,k1_zfmisc_1(k2_zfmisc_1(A_359,B_360)))
      | ~ m1_subset_1(C_358,k1_zfmisc_1(k2_zfmisc_1(A_359,B_360))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2801,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_66,c_2791])).

tff(c_2820,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2801])).

tff(c_2847,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2820])).

tff(c_3208,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_2847])).

tff(c_3215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_3208])).

tff(c_3216,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2820])).

tff(c_3626,plain,(
    ! [B_482,C_484,A_485,D_483,E_481] :
      ( k1_xboole_0 = C_484
      | v2_funct_1(D_483)
      | ~ v2_funct_1(k1_partfun1(A_485,B_482,B_482,C_484,D_483,E_481))
      | ~ m1_subset_1(E_481,k1_zfmisc_1(k2_zfmisc_1(B_482,C_484)))
      | ~ v1_funct_2(E_481,B_482,C_484)
      | ~ v1_funct_1(E_481)
      | ~ m1_subset_1(D_483,k1_zfmisc_1(k2_zfmisc_1(A_485,B_482)))
      | ~ v1_funct_2(D_483,A_485,B_482)
      | ~ v1_funct_1(D_483) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_3628,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3216,c_3626])).

tff(c_3630,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_72,c_70,c_68,c_79,c_3628])).

tff(c_3631,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_3630])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_3667,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3631,c_2])).

tff(c_10,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3665,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3631,c_3631,c_10])).

tff(c_218,plain,(
    ! [B_73,A_74] :
      ( v1_xboole_0(B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_74))
      | ~ v1_xboole_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_244,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_218])).

tff(c_246,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_244])).

tff(c_3842,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3665,c_246])).

tff(c_3847,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3667,c_3842])).

tff(c_3849,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_244])).

tff(c_3848,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_244])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( ~ v1_xboole_0(B_5)
      | B_5 = A_4
      | ~ v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3952,plain,(
    ! [A_499] :
      ( A_499 = '#skF_5'
      | ~ v1_xboole_0(A_499) ) ),
    inference(resolution,[status(thm)],[c_3848,c_6])).

tff(c_3959,plain,(
    k2_zfmisc_1('#skF_3','#skF_2') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3849,c_3952])).

tff(c_148,plain,(
    ! [B_62,A_63] :
      ( ~ v1_xboole_0(B_62)
      | B_62 = A_63
      | ~ v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_151,plain,(
    ! [A_63] :
      ( k1_xboole_0 = A_63
      | ~ v1_xboole_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_2,c_148])).

tff(c_3855,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3848,c_151])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( k1_xboole_0 = B_7
      | k1_xboole_0 = A_6
      | k2_zfmisc_1(A_6,B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4025,plain,(
    ! [B_502,A_503] :
      ( B_502 = '#skF_5'
      | A_503 = '#skF_5'
      | k2_zfmisc_1(A_503,B_502) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3855,c_3855,c_3855,c_8])).

tff(c_4035,plain,
    ( '#skF_5' = '#skF_2'
    | '#skF_5' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_3959,c_4025])).

tff(c_4040,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4035])).

tff(c_4054,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4040,c_3848])).

tff(c_3865,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3855,c_3855,c_10])).

tff(c_4043,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4040,c_4040,c_3865])).

tff(c_243,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_74,c_218])).

tff(c_245,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_243])).

tff(c_4114,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4043,c_245])).

tff(c_4119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4054,c_4114])).

tff(c_4120,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4035])).

tff(c_4135,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4120,c_3848])).

tff(c_12,plain,(
    ! [B_7] : k2_zfmisc_1(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3864,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_5',B_7) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3855,c_3855,c_12])).

tff(c_4125,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_2',B_7) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4120,c_4120,c_3864])).

tff(c_4247,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4125,c_245])).

tff(c_4252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4135,c_4247])).

tff(c_4253,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_243])).

tff(c_4271,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4253,c_151])).

tff(c_112,plain,(
    ! [A_58] : k6_relat_1(A_58) = k6_partfun1(A_58) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_28,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_118,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_28])).

tff(c_134,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_79])).

tff(c_4278,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4271,c_134])).

tff(c_4286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_4278])).

tff(c_4287,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_26,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4436,plain,(
    ! [B_535,A_536] :
      ( v1_relat_1(B_535)
      | ~ m1_subset_1(B_535,k1_zfmisc_1(A_536))
      | ~ v1_relat_1(A_536) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4451,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_4436])).

tff(c_4465,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_4451])).

tff(c_6653,plain,(
    ! [C_781,B_782,A_783] :
      ( v5_relat_1(C_781,B_782)
      | ~ m1_subset_1(C_781,k1_zfmisc_1(k2_zfmisc_1(A_783,B_782))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6674,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_6653])).

tff(c_6856,plain,(
    ! [A_791,B_792,D_793] :
      ( r2_relset_1(A_791,B_792,D_793,D_793)
      | ~ m1_subset_1(D_793,k1_zfmisc_1(k2_zfmisc_1(A_791,B_792))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_6875,plain,(
    ! [A_39] : r2_relset_1(A_39,A_39,k6_partfun1(A_39),k6_partfun1(A_39)) ),
    inference(resolution,[status(thm)],[c_54,c_6856])).

tff(c_6962,plain,(
    ! [A_805,B_806,C_807] :
      ( k2_relset_1(A_805,B_806,C_807) = k2_relat_1(C_807)
      | ~ m1_subset_1(C_807,k1_zfmisc_1(k2_zfmisc_1(A_805,B_806))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6989,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_6962])).

tff(c_7023,plain,(
    ! [D_810,C_811,A_812,B_813] :
      ( D_810 = C_811
      | ~ r2_relset_1(A_812,B_813,C_811,D_810)
      | ~ m1_subset_1(D_810,k1_zfmisc_1(k2_zfmisc_1(A_812,B_813)))
      | ~ m1_subset_1(C_811,k1_zfmisc_1(k2_zfmisc_1(A_812,B_813))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_7033,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_66,c_7023])).

tff(c_7052,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_7033])).

tff(c_7066,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_7052])).

tff(c_7442,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_7066])).

tff(c_7449,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_7442])).

tff(c_7450,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_7052])).

tff(c_7952,plain,(
    ! [A_940,B_941,C_942,D_943] :
      ( k2_relset_1(A_940,B_941,C_942) = B_941
      | ~ r2_relset_1(B_941,B_941,k1_partfun1(B_941,A_940,A_940,B_941,D_943,C_942),k6_partfun1(B_941))
      | ~ m1_subset_1(D_943,k1_zfmisc_1(k2_zfmisc_1(B_941,A_940)))
      | ~ v1_funct_2(D_943,B_941,A_940)
      | ~ v1_funct_1(D_943)
      | ~ m1_subset_1(C_942,k1_zfmisc_1(k2_zfmisc_1(A_940,B_941)))
      | ~ v1_funct_2(C_942,A_940,B_941)
      | ~ v1_funct_1(C_942) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_7955,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7450,c_7952])).

tff(c_7960,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_78,c_76,c_74,c_6875,c_6989,c_7955])).

tff(c_44,plain,(
    ! [B_32] :
      ( v2_funct_2(B_32,k2_relat_1(B_32))
      | ~ v5_relat_1(B_32,k2_relat_1(B_32))
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_7969,plain,
    ( v2_funct_2('#skF_5',k2_relat_1('#skF_5'))
    | ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7960,c_44])).

tff(c_7976,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4465,c_6674,c_7960,c_7969])).

tff(c_7978,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4287,c_7976])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:07:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.75/2.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.75/2.60  
% 6.75/2.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.93/2.60  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 6.93/2.60  
% 6.93/2.60  %Foreground sorts:
% 6.93/2.60  
% 6.93/2.60  
% 6.93/2.60  %Background operators:
% 6.93/2.60  
% 6.93/2.60  
% 6.93/2.60  %Foreground operators:
% 6.93/2.60  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.93/2.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.93/2.60  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.93/2.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.93/2.60  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.93/2.60  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.93/2.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.93/2.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.93/2.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.93/2.60  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.93/2.60  tff('#skF_5', type, '#skF_5': $i).
% 6.93/2.60  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.93/2.60  tff('#skF_2', type, '#skF_2': $i).
% 6.93/2.60  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.93/2.60  tff('#skF_3', type, '#skF_3': $i).
% 6.93/2.60  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.93/2.60  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.93/2.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.93/2.60  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.93/2.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.93/2.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.93/2.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.93/2.60  tff('#skF_4', type, '#skF_4': $i).
% 6.93/2.60  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.93/2.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.93/2.60  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.93/2.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.93/2.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.93/2.60  
% 6.93/2.62  tff(f_183, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 6.93/2.62  tff(f_124, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.93/2.62  tff(f_80, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 6.93/2.62  tff(f_118, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.93/2.62  tff(f_122, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.93/2.62  tff(f_98, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.93/2.62  tff(f_163, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 6.93/2.62  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.93/2.62  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.93/2.62  tff(f_62, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 6.93/2.62  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 6.93/2.62  tff(f_76, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 6.93/2.62  tff(f_75, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.93/2.62  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.93/2.62  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.93/2.62  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.93/2.62  tff(f_141, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 6.93/2.62  tff(f_106, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 6.93/2.62  tff(c_64, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.93/2.62  tff(c_146, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_64])).
% 6.93/2.62  tff(c_78, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.93/2.62  tff(c_76, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.93/2.62  tff(c_74, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.93/2.62  tff(c_72, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.93/2.62  tff(c_70, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.93/2.62  tff(c_68, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.93/2.62  tff(c_56, plain, (![A_40]: (k6_relat_1(A_40)=k6_partfun1(A_40))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.93/2.62  tff(c_32, plain, (![A_20]: (v2_funct_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.93/2.62  tff(c_79, plain, (![A_20]: (v2_funct_1(k6_partfun1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_32])).
% 6.93/2.62  tff(c_48, plain, (![D_36, F_38, E_37, A_33, B_34, C_35]: (m1_subset_1(k1_partfun1(A_33, B_34, C_35, D_36, E_37, F_38), k1_zfmisc_1(k2_zfmisc_1(A_33, D_36))) | ~m1_subset_1(F_38, k1_zfmisc_1(k2_zfmisc_1(C_35, D_36))) | ~v1_funct_1(F_38) | ~m1_subset_1(E_37, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))) | ~v1_funct_1(E_37))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.93/2.62  tff(c_54, plain, (![A_39]: (m1_subset_1(k6_partfun1(A_39), k1_zfmisc_1(k2_zfmisc_1(A_39, A_39))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.93/2.62  tff(c_66, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.93/2.62  tff(c_2791, plain, (![D_357, C_358, A_359, B_360]: (D_357=C_358 | ~r2_relset_1(A_359, B_360, C_358, D_357) | ~m1_subset_1(D_357, k1_zfmisc_1(k2_zfmisc_1(A_359, B_360))) | ~m1_subset_1(C_358, k1_zfmisc_1(k2_zfmisc_1(A_359, B_360))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.93/2.62  tff(c_2801, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_66, c_2791])).
% 6.93/2.62  tff(c_2820, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2801])).
% 6.93/2.62  tff(c_2847, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_2820])).
% 6.93/2.62  tff(c_3208, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_2847])).
% 6.93/2.62  tff(c_3215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_3208])).
% 6.93/2.62  tff(c_3216, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_2820])).
% 6.93/2.62  tff(c_3626, plain, (![B_482, C_484, A_485, D_483, E_481]: (k1_xboole_0=C_484 | v2_funct_1(D_483) | ~v2_funct_1(k1_partfun1(A_485, B_482, B_482, C_484, D_483, E_481)) | ~m1_subset_1(E_481, k1_zfmisc_1(k2_zfmisc_1(B_482, C_484))) | ~v1_funct_2(E_481, B_482, C_484) | ~v1_funct_1(E_481) | ~m1_subset_1(D_483, k1_zfmisc_1(k2_zfmisc_1(A_485, B_482))) | ~v1_funct_2(D_483, A_485, B_482) | ~v1_funct_1(D_483))), inference(cnfTransformation, [status(thm)], [f_163])).
% 6.93/2.62  tff(c_3628, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3216, c_3626])).
% 6.93/2.62  tff(c_3630, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_72, c_70, c_68, c_79, c_3628])).
% 6.93/2.62  tff(c_3631, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_146, c_3630])).
% 6.93/2.62  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.93/2.62  tff(c_3667, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3631, c_2])).
% 6.93/2.62  tff(c_10, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.93/2.62  tff(c_3665, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3631, c_3631, c_10])).
% 6.93/2.62  tff(c_218, plain, (![B_73, A_74]: (v1_xboole_0(B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_74)) | ~v1_xboole_0(A_74))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.93/2.62  tff(c_244, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_218])).
% 6.93/2.62  tff(c_246, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_244])).
% 6.93/2.62  tff(c_3842, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3665, c_246])).
% 6.93/2.62  tff(c_3847, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3667, c_3842])).
% 6.93/2.62  tff(c_3849, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_244])).
% 6.93/2.62  tff(c_3848, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_244])).
% 6.93/2.62  tff(c_6, plain, (![B_5, A_4]: (~v1_xboole_0(B_5) | B_5=A_4 | ~v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.93/2.62  tff(c_3952, plain, (![A_499]: (A_499='#skF_5' | ~v1_xboole_0(A_499))), inference(resolution, [status(thm)], [c_3848, c_6])).
% 6.93/2.62  tff(c_3959, plain, (k2_zfmisc_1('#skF_3', '#skF_2')='#skF_5'), inference(resolution, [status(thm)], [c_3849, c_3952])).
% 6.93/2.62  tff(c_148, plain, (![B_62, A_63]: (~v1_xboole_0(B_62) | B_62=A_63 | ~v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.93/2.62  tff(c_151, plain, (![A_63]: (k1_xboole_0=A_63 | ~v1_xboole_0(A_63))), inference(resolution, [status(thm)], [c_2, c_148])).
% 6.93/2.62  tff(c_3855, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_3848, c_151])).
% 6.93/2.62  tff(c_8, plain, (![B_7, A_6]: (k1_xboole_0=B_7 | k1_xboole_0=A_6 | k2_zfmisc_1(A_6, B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.93/2.62  tff(c_4025, plain, (![B_502, A_503]: (B_502='#skF_5' | A_503='#skF_5' | k2_zfmisc_1(A_503, B_502)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3855, c_3855, c_3855, c_8])).
% 6.93/2.62  tff(c_4035, plain, ('#skF_5'='#skF_2' | '#skF_5'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_3959, c_4025])).
% 6.93/2.62  tff(c_4040, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_4035])).
% 6.93/2.62  tff(c_4054, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4040, c_3848])).
% 6.93/2.62  tff(c_3865, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3855, c_3855, c_10])).
% 6.93/2.62  tff(c_4043, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4040, c_4040, c_3865])).
% 6.93/2.62  tff(c_243, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_74, c_218])).
% 6.93/2.62  tff(c_245, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_243])).
% 6.93/2.62  tff(c_4114, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4043, c_245])).
% 6.93/2.62  tff(c_4119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4054, c_4114])).
% 6.93/2.62  tff(c_4120, plain, ('#skF_5'='#skF_2'), inference(splitRight, [status(thm)], [c_4035])).
% 6.93/2.62  tff(c_4135, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4120, c_3848])).
% 6.93/2.62  tff(c_12, plain, (![B_7]: (k2_zfmisc_1(k1_xboole_0, B_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.93/2.62  tff(c_3864, plain, (![B_7]: (k2_zfmisc_1('#skF_5', B_7)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3855, c_3855, c_12])).
% 6.93/2.62  tff(c_4125, plain, (![B_7]: (k2_zfmisc_1('#skF_2', B_7)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4120, c_4120, c_3864])).
% 6.93/2.62  tff(c_4247, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4125, c_245])).
% 6.93/2.62  tff(c_4252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4135, c_4247])).
% 6.93/2.62  tff(c_4253, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_243])).
% 6.93/2.62  tff(c_4271, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4253, c_151])).
% 6.93/2.62  tff(c_112, plain, (![A_58]: (k6_relat_1(A_58)=k6_partfun1(A_58))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.93/2.62  tff(c_28, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.93/2.62  tff(c_118, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_112, c_28])).
% 6.93/2.62  tff(c_134, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_118, c_79])).
% 6.93/2.62  tff(c_4278, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4271, c_134])).
% 6.93/2.62  tff(c_4286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_4278])).
% 6.93/2.62  tff(c_4287, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_64])).
% 6.93/2.62  tff(c_26, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.93/2.62  tff(c_4436, plain, (![B_535, A_536]: (v1_relat_1(B_535) | ~m1_subset_1(B_535, k1_zfmisc_1(A_536)) | ~v1_relat_1(A_536))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.93/2.62  tff(c_4451, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_4436])).
% 6.93/2.62  tff(c_4465, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_4451])).
% 6.93/2.62  tff(c_6653, plain, (![C_781, B_782, A_783]: (v5_relat_1(C_781, B_782) | ~m1_subset_1(C_781, k1_zfmisc_1(k2_zfmisc_1(A_783, B_782))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.93/2.62  tff(c_6674, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_6653])).
% 6.93/2.62  tff(c_6856, plain, (![A_791, B_792, D_793]: (r2_relset_1(A_791, B_792, D_793, D_793) | ~m1_subset_1(D_793, k1_zfmisc_1(k2_zfmisc_1(A_791, B_792))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.93/2.62  tff(c_6875, plain, (![A_39]: (r2_relset_1(A_39, A_39, k6_partfun1(A_39), k6_partfun1(A_39)))), inference(resolution, [status(thm)], [c_54, c_6856])).
% 6.93/2.62  tff(c_6962, plain, (![A_805, B_806, C_807]: (k2_relset_1(A_805, B_806, C_807)=k2_relat_1(C_807) | ~m1_subset_1(C_807, k1_zfmisc_1(k2_zfmisc_1(A_805, B_806))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.93/2.62  tff(c_6989, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_68, c_6962])).
% 6.93/2.62  tff(c_7023, plain, (![D_810, C_811, A_812, B_813]: (D_810=C_811 | ~r2_relset_1(A_812, B_813, C_811, D_810) | ~m1_subset_1(D_810, k1_zfmisc_1(k2_zfmisc_1(A_812, B_813))) | ~m1_subset_1(C_811, k1_zfmisc_1(k2_zfmisc_1(A_812, B_813))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.93/2.62  tff(c_7033, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_66, c_7023])).
% 6.93/2.62  tff(c_7052, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_7033])).
% 6.93/2.62  tff(c_7066, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_7052])).
% 6.93/2.62  tff(c_7442, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_7066])).
% 6.93/2.62  tff(c_7449, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_7442])).
% 6.93/2.62  tff(c_7450, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_7052])).
% 6.93/2.62  tff(c_7952, plain, (![A_940, B_941, C_942, D_943]: (k2_relset_1(A_940, B_941, C_942)=B_941 | ~r2_relset_1(B_941, B_941, k1_partfun1(B_941, A_940, A_940, B_941, D_943, C_942), k6_partfun1(B_941)) | ~m1_subset_1(D_943, k1_zfmisc_1(k2_zfmisc_1(B_941, A_940))) | ~v1_funct_2(D_943, B_941, A_940) | ~v1_funct_1(D_943) | ~m1_subset_1(C_942, k1_zfmisc_1(k2_zfmisc_1(A_940, B_941))) | ~v1_funct_2(C_942, A_940, B_941) | ~v1_funct_1(C_942))), inference(cnfTransformation, [status(thm)], [f_141])).
% 6.93/2.62  tff(c_7955, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7450, c_7952])).
% 6.93/2.62  tff(c_7960, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_78, c_76, c_74, c_6875, c_6989, c_7955])).
% 6.93/2.62  tff(c_44, plain, (![B_32]: (v2_funct_2(B_32, k2_relat_1(B_32)) | ~v5_relat_1(B_32, k2_relat_1(B_32)) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.93/2.62  tff(c_7969, plain, (v2_funct_2('#skF_5', k2_relat_1('#skF_5')) | ~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7960, c_44])).
% 6.93/2.62  tff(c_7976, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4465, c_6674, c_7960, c_7969])).
% 6.93/2.62  tff(c_7978, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4287, c_7976])).
% 6.93/2.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.93/2.62  
% 6.93/2.62  Inference rules
% 6.93/2.62  ----------------------
% 6.93/2.62  #Ref     : 0
% 6.93/2.62  #Sup     : 1736
% 6.93/2.62  #Fact    : 0
% 6.93/2.62  #Define  : 0
% 6.93/2.62  #Split   : 38
% 6.93/2.62  #Chain   : 0
% 6.93/2.62  #Close   : 0
% 6.93/2.62  
% 6.93/2.62  Ordering : KBO
% 6.93/2.62  
% 6.93/2.62  Simplification rules
% 6.93/2.62  ----------------------
% 6.93/2.62  #Subsume      : 184
% 6.93/2.62  #Demod        : 1547
% 6.93/2.62  #Tautology    : 755
% 6.93/2.62  #SimpNegUnit  : 9
% 6.93/2.62  #BackRed      : 289
% 6.93/2.62  
% 6.93/2.62  #Partial instantiations: 0
% 6.93/2.62  #Strategies tried      : 1
% 6.93/2.62  
% 6.93/2.62  Timing (in seconds)
% 6.93/2.62  ----------------------
% 6.93/2.63  Preprocessing        : 0.36
% 6.93/2.63  Parsing              : 0.20
% 6.93/2.63  CNF conversion       : 0.02
% 6.93/2.63  Main loop            : 1.42
% 6.93/2.63  Inferencing          : 0.47
% 6.93/2.63  Reduction            : 0.52
% 6.93/2.63  Demodulation         : 0.38
% 6.93/2.63  BG Simplification    : 0.05
% 6.93/2.63  Subsumption          : 0.24
% 6.93/2.63  Abstraction          : 0.05
% 6.93/2.63  MUC search           : 0.00
% 6.93/2.63  Cooper               : 0.00
% 6.93/2.63  Total                : 1.83
% 6.93/2.63  Index Insertion      : 0.00
% 6.93/2.63  Index Deletion       : 0.00
% 6.93/2.63  Index Matching       : 0.00
% 6.93/2.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
