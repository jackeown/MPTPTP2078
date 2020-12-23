%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:04 EST 2020

% Result     : Theorem 4.73s
% Output     : CNFRefutation 4.73s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 589 expanded)
%              Number of leaves         :   45 ( 217 expanded)
%              Depth                    :   10
%              Number of atoms          :  262 (1578 expanded)
%              Number of equality atoms :   75 ( 256 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_168,negated_conjecture,(
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

tff(f_109,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_59,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_107,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_61,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_103,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_148,axiom,(
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

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_126,axiom,(
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

tff(f_91,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_56,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_127,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_48,plain,(
    ! [A_33] : k6_relat_1(A_33) = k6_partfun1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_18,plain,(
    ! [A_9] : k1_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_73,plain,(
    ! [A_9] : k1_relat_1(k6_partfun1(A_9)) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_18])).

tff(c_46,plain,(
    ! [A_32] : m1_subset_1(k6_partfun1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_169,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_202,plain,(
    ! [A_64] : v1_relat_1(k6_partfun1(A_64)) ),
    inference(resolution,[status(thm)],[c_46,c_169])).

tff(c_16,plain,(
    ! [A_8] :
      ( k1_relat_1(A_8) != k1_xboole_0
      | k1_xboole_0 = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_205,plain,(
    ! [A_64] :
      ( k1_relat_1(k6_partfun1(A_64)) != k1_xboole_0
      | k6_partfun1(A_64) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_202,c_16])).

tff(c_284,plain,(
    ! [A_67] :
      ( k1_xboole_0 != A_67
      | k6_partfun1(A_67) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_205])).

tff(c_58,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_295,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_xboole_0)
    | k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_58])).

tff(c_336,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_295])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_68,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_22,plain,(
    ! [A_10] : v2_funct_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_71,plain,(
    ! [A_10] : v2_funct_1(k6_partfun1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_22])).

tff(c_40,plain,(
    ! [B_27,D_29,A_26,E_30,F_31,C_28] :
      ( m1_subset_1(k1_partfun1(A_26,B_27,C_28,D_29,E_30,F_31),k1_zfmisc_1(k2_zfmisc_1(A_26,D_29)))
      | ~ m1_subset_1(F_31,k1_zfmisc_1(k2_zfmisc_1(C_28,D_29)))
      | ~ v1_funct_1(F_31)
      | ~ m1_subset_1(E_30,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ v1_funct_1(E_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_508,plain,(
    ! [D_95,C_96,A_97,B_98] :
      ( D_95 = C_96
      | ~ r2_relset_1(A_97,B_98,C_96,D_95)
      | ~ m1_subset_1(D_95,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98)))
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_516,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_508])).

tff(c_531,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_516])).

tff(c_851,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_531])).

tff(c_893,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_851])).

tff(c_897,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_893])).

tff(c_898,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_531])).

tff(c_954,plain,(
    ! [B_150,E_149,C_151,D_152,A_148] :
      ( k1_xboole_0 = C_151
      | v2_funct_1(D_152)
      | ~ v2_funct_1(k1_partfun1(A_148,B_150,B_150,C_151,D_152,E_149))
      | ~ m1_subset_1(E_149,k1_zfmisc_1(k2_zfmisc_1(B_150,C_151)))
      | ~ v1_funct_2(E_149,B_150,C_151)
      | ~ v1_funct_1(E_149)
      | ~ m1_subset_1(D_152,k1_zfmisc_1(k2_zfmisc_1(A_148,B_150)))
      | ~ v1_funct_2(D_152,A_148,B_150)
      | ~ v1_funct_1(D_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_956,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_898,c_954])).

tff(c_958,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_62,c_60,c_71,c_956])).

tff(c_960,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_336,c_958])).

tff(c_962,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_295])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_977,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_962,c_2])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_976,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_962,c_962,c_8])).

tff(c_150,plain,(
    ! [B_59,A_60] :
      ( v1_xboole_0(B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60))
      | ~ v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_167,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_150])).

tff(c_213,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_1018,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_976,c_213])).

tff(c_1022,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_977,c_1018])).

tff(c_1023,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_128,plain,(
    ! [B_53,A_54] :
      ( ~ v1_xboole_0(B_53)
      | B_53 = A_54
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_131,plain,(
    ! [A_54] :
      ( k1_xboole_0 = A_54
      | ~ v1_xboole_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_2,c_128])).

tff(c_1041,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1023,c_131])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1048,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1041,c_1041,c_10])).

tff(c_1049,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1041,c_1041,c_8])).

tff(c_210,plain,(
    ! [A_64] :
      ( k1_xboole_0 != A_64
      | k6_partfun1(A_64) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_205])).

tff(c_1240,plain,(
    ! [A_174] :
      ( A_174 != '#skF_4'
      | k6_partfun1(A_174) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1041,c_1041,c_210])).

tff(c_1260,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_4')
    | '#skF_1' != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1240,c_58])).

tff(c_1311,plain,(
    '#skF_1' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1260])).

tff(c_1024,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_1077,plain,(
    ! [A_162] :
      ( A_162 = '#skF_4'
      | ~ v1_xboole_0(A_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1041,c_131])).

tff(c_1087,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1024,c_1077])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1535,plain,(
    ! [B_212,A_213] :
      ( B_212 = '#skF_4'
      | A_213 = '#skF_4'
      | k2_zfmisc_1(A_213,B_212) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1041,c_1041,c_1041,c_6])).

tff(c_1538,plain,
    ( '#skF_1' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1087,c_1535])).

tff(c_1547,plain,(
    '#skF_2' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_1311,c_1538])).

tff(c_168,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_150])).

tff(c_1060,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_168])).

tff(c_1557,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1547,c_1060])).

tff(c_1565,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1023,c_1049,c_1557])).

tff(c_1567,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1260])).

tff(c_1571,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1567,c_1060])).

tff(c_1580,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1023,c_1048,c_1571])).

tff(c_1581,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1592,plain,(
    ! [A_214] :
      ( A_214 = '#skF_3'
      | ~ v1_xboole_0(A_214) ) ),
    inference(resolution,[status(thm)],[c_1581,c_4])).

tff(c_1613,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1023,c_1592])).

tff(c_1619,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1613,c_127])).

tff(c_139,plain,(
    ! [A_57] : m1_subset_1(k6_partfun1(A_57),k1_zfmisc_1(k2_zfmisc_1(A_57,A_57))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_143,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_139])).

tff(c_153,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_143,c_150])).

tff(c_165,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_153])).

tff(c_1056,plain,(
    v1_xboole_0(k6_partfun1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1041,c_165])).

tff(c_1612,plain,(
    k6_partfun1('#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1056,c_1592])).

tff(c_1638,plain,(
    k6_partfun1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1613,c_1612])).

tff(c_1657,plain,(
    v2_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1638,c_71])).

tff(c_1662,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1619,c_1657])).

tff(c_1663,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1687,plain,(
    ! [C_224,A_225,B_226] :
      ( v1_relat_1(C_224)
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1(A_225,B_226))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1702,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_1687])).

tff(c_1826,plain,(
    ! [C_233,B_234,A_235] :
      ( v5_relat_1(C_233,B_234)
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(A_235,B_234))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1843,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_1826])).

tff(c_1969,plain,(
    ! [A_255,B_256,D_257] :
      ( r2_relset_1(A_255,B_256,D_257,D_257)
      | ~ m1_subset_1(D_257,k1_zfmisc_1(k2_zfmisc_1(A_255,B_256))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1980,plain,(
    ! [A_32] : r2_relset_1(A_32,A_32,k6_partfun1(A_32),k6_partfun1(A_32)) ),
    inference(resolution,[status(thm)],[c_46,c_1969])).

tff(c_1987,plain,(
    ! [A_260,B_261,C_262] :
      ( k2_relset_1(A_260,B_261,C_262) = k2_relat_1(C_262)
      | ~ m1_subset_1(C_262,k1_zfmisc_1(k2_zfmisc_1(A_260,B_261))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2005,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_1987])).

tff(c_2033,plain,(
    ! [D_267,C_268,A_269,B_270] :
      ( D_267 = C_268
      | ~ r2_relset_1(A_269,B_270,C_268,D_267)
      | ~ m1_subset_1(D_267,k1_zfmisc_1(k2_zfmisc_1(A_269,B_270)))
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_zfmisc_1(A_269,B_270))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2039,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_2033])).

tff(c_2050,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2039])).

tff(c_2084,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2050])).

tff(c_2401,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_2084])).

tff(c_2405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_2401])).

tff(c_2406,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2050])).

tff(c_2797,plain,(
    ! [A_372,B_373,C_374,D_375] :
      ( k2_relset_1(A_372,B_373,C_374) = B_373
      | ~ r2_relset_1(B_373,B_373,k1_partfun1(B_373,A_372,A_372,B_373,D_375,C_374),k6_partfun1(B_373))
      | ~ m1_subset_1(D_375,k1_zfmisc_1(k2_zfmisc_1(B_373,A_372)))
      | ~ v1_funct_2(D_375,B_373,A_372)
      | ~ v1_funct_1(D_375)
      | ~ m1_subset_1(C_374,k1_zfmisc_1(k2_zfmisc_1(A_372,B_373)))
      | ~ v1_funct_2(C_374,A_372,B_373)
      | ~ v1_funct_1(C_374) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2800,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2406,c_2797])).

tff(c_2805,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_70,c_68,c_66,c_1980,c_2005,c_2800])).

tff(c_36,plain,(
    ! [B_25] :
      ( v2_funct_2(B_25,k2_relat_1(B_25))
      | ~ v5_relat_1(B_25,k2_relat_1(B_25))
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2811,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2805,c_36])).

tff(c_2815,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1702,c_1843,c_2805,c_2811])).

tff(c_2817,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1663,c_2815])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:25:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.73/1.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.73/1.83  
% 4.73/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.73/1.83  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.73/1.83  
% 4.73/1.83  %Foreground sorts:
% 4.73/1.83  
% 4.73/1.83  
% 4.73/1.83  %Background operators:
% 4.73/1.83  
% 4.73/1.83  
% 4.73/1.83  %Foreground operators:
% 4.73/1.83  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.73/1.83  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.73/1.83  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.73/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.73/1.83  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.73/1.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.73/1.83  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.73/1.83  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.73/1.83  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.73/1.83  tff('#skF_2', type, '#skF_2': $i).
% 4.73/1.83  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.73/1.83  tff('#skF_3', type, '#skF_3': $i).
% 4.73/1.83  tff('#skF_1', type, '#skF_1': $i).
% 4.73/1.83  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.73/1.83  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.73/1.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.73/1.83  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.73/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.73/1.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.73/1.83  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.73/1.83  tff('#skF_4', type, '#skF_4': $i).
% 4.73/1.83  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.73/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.73/1.83  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.73/1.83  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.73/1.83  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.73/1.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.73/1.83  
% 4.73/1.86  tff(f_168, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 4.73/1.86  tff(f_109, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.73/1.86  tff(f_59, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 4.73/1.86  tff(f_107, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.73/1.86  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.73/1.86  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 4.73/1.86  tff(f_61, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 4.73/1.86  tff(f_103, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.73/1.86  tff(f_83, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.73/1.86  tff(f_148, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 4.73/1.86  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.73/1.86  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.73/1.86  tff(f_47, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 4.73/1.86  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 4.73/1.86  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.73/1.86  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.73/1.86  tff(f_126, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 4.73/1.86  tff(f_91, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 4.73/1.86  tff(c_56, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.73/1.86  tff(c_127, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_56])).
% 4.73/1.86  tff(c_48, plain, (![A_33]: (k6_relat_1(A_33)=k6_partfun1(A_33))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.73/1.86  tff(c_18, plain, (![A_9]: (k1_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.73/1.86  tff(c_73, plain, (![A_9]: (k1_relat_1(k6_partfun1(A_9))=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_18])).
% 4.73/1.86  tff(c_46, plain, (![A_32]: (m1_subset_1(k6_partfun1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.73/1.86  tff(c_169, plain, (![C_61, A_62, B_63]: (v1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.73/1.86  tff(c_202, plain, (![A_64]: (v1_relat_1(k6_partfun1(A_64)))), inference(resolution, [status(thm)], [c_46, c_169])).
% 4.73/1.86  tff(c_16, plain, (![A_8]: (k1_relat_1(A_8)!=k1_xboole_0 | k1_xboole_0=A_8 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.73/1.86  tff(c_205, plain, (![A_64]: (k1_relat_1(k6_partfun1(A_64))!=k1_xboole_0 | k6_partfun1(A_64)=k1_xboole_0)), inference(resolution, [status(thm)], [c_202, c_16])).
% 4.73/1.86  tff(c_284, plain, (![A_67]: (k1_xboole_0!=A_67 | k6_partfun1(A_67)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_73, c_205])).
% 4.73/1.86  tff(c_58, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.73/1.86  tff(c_295, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_xboole_0) | k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_284, c_58])).
% 4.73/1.86  tff(c_336, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_295])).
% 4.73/1.86  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.73/1.86  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.73/1.86  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.73/1.86  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.73/1.86  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.73/1.86  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.73/1.86  tff(c_22, plain, (![A_10]: (v2_funct_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.73/1.86  tff(c_71, plain, (![A_10]: (v2_funct_1(k6_partfun1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_22])).
% 4.73/1.86  tff(c_40, plain, (![B_27, D_29, A_26, E_30, F_31, C_28]: (m1_subset_1(k1_partfun1(A_26, B_27, C_28, D_29, E_30, F_31), k1_zfmisc_1(k2_zfmisc_1(A_26, D_29))) | ~m1_subset_1(F_31, k1_zfmisc_1(k2_zfmisc_1(C_28, D_29))) | ~v1_funct_1(F_31) | ~m1_subset_1(E_30, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~v1_funct_1(E_30))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.73/1.86  tff(c_508, plain, (![D_95, C_96, A_97, B_98]: (D_95=C_96 | ~r2_relset_1(A_97, B_98, C_96, D_95) | ~m1_subset_1(D_95, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.73/1.86  tff(c_516, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_508])).
% 4.73/1.86  tff(c_531, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_516])).
% 4.73/1.86  tff(c_851, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_531])).
% 4.73/1.86  tff(c_893, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_851])).
% 4.73/1.86  tff(c_897, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_893])).
% 4.73/1.86  tff(c_898, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_531])).
% 4.73/1.86  tff(c_954, plain, (![B_150, E_149, C_151, D_152, A_148]: (k1_xboole_0=C_151 | v2_funct_1(D_152) | ~v2_funct_1(k1_partfun1(A_148, B_150, B_150, C_151, D_152, E_149)) | ~m1_subset_1(E_149, k1_zfmisc_1(k2_zfmisc_1(B_150, C_151))) | ~v1_funct_2(E_149, B_150, C_151) | ~v1_funct_1(E_149) | ~m1_subset_1(D_152, k1_zfmisc_1(k2_zfmisc_1(A_148, B_150))) | ~v1_funct_2(D_152, A_148, B_150) | ~v1_funct_1(D_152))), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.73/1.86  tff(c_956, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_898, c_954])).
% 4.73/1.86  tff(c_958, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_62, c_60, c_71, c_956])).
% 4.73/1.86  tff(c_960, plain, $false, inference(negUnitSimplification, [status(thm)], [c_127, c_336, c_958])).
% 4.73/1.86  tff(c_962, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_295])).
% 4.73/1.86  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.73/1.86  tff(c_977, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_962, c_2])).
% 4.73/1.86  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.73/1.86  tff(c_976, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_962, c_962, c_8])).
% 4.73/1.86  tff(c_150, plain, (![B_59, A_60]: (v1_xboole_0(B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)) | ~v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.73/1.86  tff(c_167, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_60, c_150])).
% 4.73/1.86  tff(c_213, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_167])).
% 4.73/1.86  tff(c_1018, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_976, c_213])).
% 4.73/1.86  tff(c_1022, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_977, c_1018])).
% 4.73/1.86  tff(c_1023, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_167])).
% 4.73/1.86  tff(c_128, plain, (![B_53, A_54]: (~v1_xboole_0(B_53) | B_53=A_54 | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.73/1.86  tff(c_131, plain, (![A_54]: (k1_xboole_0=A_54 | ~v1_xboole_0(A_54))), inference(resolution, [status(thm)], [c_2, c_128])).
% 4.73/1.86  tff(c_1041, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1023, c_131])).
% 4.73/1.86  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.73/1.86  tff(c_1048, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1041, c_1041, c_10])).
% 4.73/1.86  tff(c_1049, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1041, c_1041, c_8])).
% 4.73/1.86  tff(c_210, plain, (![A_64]: (k1_xboole_0!=A_64 | k6_partfun1(A_64)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_73, c_205])).
% 4.73/1.86  tff(c_1240, plain, (![A_174]: (A_174!='#skF_4' | k6_partfun1(A_174)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1041, c_1041, c_210])).
% 4.73/1.86  tff(c_1260, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_4') | '#skF_1'!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1240, c_58])).
% 4.73/1.86  tff(c_1311, plain, ('#skF_1'!='#skF_4'), inference(splitLeft, [status(thm)], [c_1260])).
% 4.73/1.86  tff(c_1024, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_167])).
% 4.73/1.86  tff(c_1077, plain, (![A_162]: (A_162='#skF_4' | ~v1_xboole_0(A_162))), inference(demodulation, [status(thm), theory('equality')], [c_1041, c_131])).
% 4.73/1.86  tff(c_1087, plain, (k2_zfmisc_1('#skF_2', '#skF_1')='#skF_4'), inference(resolution, [status(thm)], [c_1024, c_1077])).
% 4.73/1.86  tff(c_6, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.73/1.86  tff(c_1535, plain, (![B_212, A_213]: (B_212='#skF_4' | A_213='#skF_4' | k2_zfmisc_1(A_213, B_212)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1041, c_1041, c_1041, c_6])).
% 4.73/1.86  tff(c_1538, plain, ('#skF_1'='#skF_4' | '#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1087, c_1535])).
% 4.73/1.86  tff(c_1547, plain, ('#skF_2'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_1311, c_1538])).
% 4.73/1.86  tff(c_168, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_150])).
% 4.73/1.86  tff(c_1060, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_168])).
% 4.73/1.86  tff(c_1557, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1547, c_1060])).
% 4.73/1.86  tff(c_1565, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1023, c_1049, c_1557])).
% 4.73/1.86  tff(c_1567, plain, ('#skF_1'='#skF_4'), inference(splitRight, [status(thm)], [c_1260])).
% 4.73/1.86  tff(c_1571, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1567, c_1060])).
% 4.73/1.86  tff(c_1580, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1023, c_1048, c_1571])).
% 4.73/1.86  tff(c_1581, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_168])).
% 4.73/1.86  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.73/1.86  tff(c_1592, plain, (![A_214]: (A_214='#skF_3' | ~v1_xboole_0(A_214))), inference(resolution, [status(thm)], [c_1581, c_4])).
% 4.73/1.86  tff(c_1613, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_1023, c_1592])).
% 4.73/1.86  tff(c_1619, plain, (~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1613, c_127])).
% 4.73/1.86  tff(c_139, plain, (![A_57]: (m1_subset_1(k6_partfun1(A_57), k1_zfmisc_1(k2_zfmisc_1(A_57, A_57))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.73/1.86  tff(c_143, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_139])).
% 4.73/1.86  tff(c_153, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_143, c_150])).
% 4.73/1.86  tff(c_165, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_153])).
% 4.73/1.86  tff(c_1056, plain, (v1_xboole_0(k6_partfun1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1041, c_165])).
% 4.73/1.86  tff(c_1612, plain, (k6_partfun1('#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_1056, c_1592])).
% 4.73/1.86  tff(c_1638, plain, (k6_partfun1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1613, c_1612])).
% 4.73/1.86  tff(c_1657, plain, (v2_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1638, c_71])).
% 4.73/1.86  tff(c_1662, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1619, c_1657])).
% 4.73/1.86  tff(c_1663, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_56])).
% 4.73/1.86  tff(c_1687, plain, (![C_224, A_225, B_226]: (v1_relat_1(C_224) | ~m1_subset_1(C_224, k1_zfmisc_1(k2_zfmisc_1(A_225, B_226))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.73/1.86  tff(c_1702, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_1687])).
% 4.73/1.86  tff(c_1826, plain, (![C_233, B_234, A_235]: (v5_relat_1(C_233, B_234) | ~m1_subset_1(C_233, k1_zfmisc_1(k2_zfmisc_1(A_235, B_234))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.73/1.86  tff(c_1843, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_1826])).
% 4.73/1.86  tff(c_1969, plain, (![A_255, B_256, D_257]: (r2_relset_1(A_255, B_256, D_257, D_257) | ~m1_subset_1(D_257, k1_zfmisc_1(k2_zfmisc_1(A_255, B_256))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.73/1.86  tff(c_1980, plain, (![A_32]: (r2_relset_1(A_32, A_32, k6_partfun1(A_32), k6_partfun1(A_32)))), inference(resolution, [status(thm)], [c_46, c_1969])).
% 4.73/1.86  tff(c_1987, plain, (![A_260, B_261, C_262]: (k2_relset_1(A_260, B_261, C_262)=k2_relat_1(C_262) | ~m1_subset_1(C_262, k1_zfmisc_1(k2_zfmisc_1(A_260, B_261))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.73/1.86  tff(c_2005, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_1987])).
% 4.73/1.86  tff(c_2033, plain, (![D_267, C_268, A_269, B_270]: (D_267=C_268 | ~r2_relset_1(A_269, B_270, C_268, D_267) | ~m1_subset_1(D_267, k1_zfmisc_1(k2_zfmisc_1(A_269, B_270))) | ~m1_subset_1(C_268, k1_zfmisc_1(k2_zfmisc_1(A_269, B_270))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.73/1.86  tff(c_2039, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_2033])).
% 4.73/1.86  tff(c_2050, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2039])).
% 4.73/1.86  tff(c_2084, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2050])).
% 4.73/1.86  tff(c_2401, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_2084])).
% 4.73/1.86  tff(c_2405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_2401])).
% 4.73/1.86  tff(c_2406, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2050])).
% 4.73/1.86  tff(c_2797, plain, (![A_372, B_373, C_374, D_375]: (k2_relset_1(A_372, B_373, C_374)=B_373 | ~r2_relset_1(B_373, B_373, k1_partfun1(B_373, A_372, A_372, B_373, D_375, C_374), k6_partfun1(B_373)) | ~m1_subset_1(D_375, k1_zfmisc_1(k2_zfmisc_1(B_373, A_372))) | ~v1_funct_2(D_375, B_373, A_372) | ~v1_funct_1(D_375) | ~m1_subset_1(C_374, k1_zfmisc_1(k2_zfmisc_1(A_372, B_373))) | ~v1_funct_2(C_374, A_372, B_373) | ~v1_funct_1(C_374))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.73/1.86  tff(c_2800, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2406, c_2797])).
% 4.73/1.86  tff(c_2805, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_70, c_68, c_66, c_1980, c_2005, c_2800])).
% 4.73/1.86  tff(c_36, plain, (![B_25]: (v2_funct_2(B_25, k2_relat_1(B_25)) | ~v5_relat_1(B_25, k2_relat_1(B_25)) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.73/1.86  tff(c_2811, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2805, c_36])).
% 4.73/1.86  tff(c_2815, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1702, c_1843, c_2805, c_2811])).
% 4.73/1.86  tff(c_2817, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1663, c_2815])).
% 4.73/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.73/1.86  
% 4.73/1.86  Inference rules
% 4.73/1.86  ----------------------
% 4.73/1.86  #Ref     : 2
% 4.73/1.86  #Sup     : 588
% 4.73/1.86  #Fact    : 0
% 4.73/1.86  #Define  : 0
% 4.73/1.86  #Split   : 31
% 4.73/1.86  #Chain   : 0
% 4.73/1.86  #Close   : 0
% 4.73/1.86  
% 4.73/1.86  Ordering : KBO
% 4.73/1.86  
% 4.73/1.86  Simplification rules
% 4.73/1.86  ----------------------
% 4.73/1.86  #Subsume      : 64
% 4.73/1.86  #Demod        : 415
% 4.73/1.86  #Tautology    : 282
% 4.73/1.86  #SimpNegUnit  : 20
% 4.73/1.86  #BackRed      : 69
% 4.73/1.86  
% 4.73/1.86  #Partial instantiations: 0
% 4.73/1.86  #Strategies tried      : 1
% 4.73/1.86  
% 4.73/1.86  Timing (in seconds)
% 4.73/1.86  ----------------------
% 4.73/1.86  Preprocessing        : 0.35
% 4.73/1.86  Parsing              : 0.19
% 4.73/1.86  CNF conversion       : 0.02
% 4.73/1.86  Main loop            : 0.73
% 4.73/1.86  Inferencing          : 0.26
% 4.73/1.86  Reduction            : 0.26
% 4.73/1.86  Demodulation         : 0.18
% 4.73/1.86  BG Simplification    : 0.03
% 4.73/1.86  Subsumption          : 0.11
% 4.73/1.86  Abstraction          : 0.03
% 4.73/1.86  MUC search           : 0.00
% 4.73/1.86  Cooper               : 0.00
% 4.73/1.86  Total                : 1.13
% 4.73/1.86  Index Insertion      : 0.00
% 4.73/1.86  Index Deletion       : 0.00
% 4.73/1.86  Index Matching       : 0.00
% 4.73/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
