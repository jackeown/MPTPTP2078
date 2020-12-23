%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:18 EST 2020

% Result     : Theorem 9.07s
% Output     : CNFRefutation 9.23s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 362 expanded)
%              Number of leaves         :   48 ( 145 expanded)
%              Depth                    :   15
%              Number of atoms          :  270 (1162 expanded)
%              Number of equality atoms :   47 ( 109 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_143,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_141,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_131,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_111,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_109,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_91,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_72,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_119,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_66,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_119,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( v1_xboole_0(k2_zfmisc_1(A_8,B_9))
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_76,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_315,plain,(
    ! [B_84,A_85] :
      ( v1_xboole_0(B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_85))
      | ~ v1_xboole_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_327,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_315])).

tff(c_341,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_327])).

tff(c_348,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_341])).

tff(c_60,plain,(
    ! [A_48] : k6_relat_1(A_48) = k6_partfun1(A_48) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_38,plain,(
    ! [A_25] : v2_funct_1(k6_relat_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_82,plain,(
    ! [A_25] : v2_funct_1(k6_partfun1(A_25)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_38])).

tff(c_80,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_5765,plain,(
    ! [B_345,F_347,D_344,A_346,C_348,E_343] :
      ( k1_partfun1(A_346,B_345,C_348,D_344,E_343,F_347) = k5_relat_1(E_343,F_347)
      | ~ m1_subset_1(F_347,k1_zfmisc_1(k2_zfmisc_1(C_348,D_344)))
      | ~ v1_funct_1(F_347)
      | ~ m1_subset_1(E_343,k1_zfmisc_1(k2_zfmisc_1(A_346,B_345)))
      | ~ v1_funct_1(E_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_5777,plain,(
    ! [A_346,B_345,E_343] :
      ( k1_partfun1(A_346,B_345,'#skF_2','#skF_1',E_343,'#skF_4') = k5_relat_1(E_343,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_343,k1_zfmisc_1(k2_zfmisc_1(A_346,B_345)))
      | ~ v1_funct_1(E_343) ) ),
    inference(resolution,[status(thm)],[c_70,c_5765])).

tff(c_7926,plain,(
    ! [A_434,B_435,E_436] :
      ( k1_partfun1(A_434,B_435,'#skF_2','#skF_1',E_436,'#skF_4') = k5_relat_1(E_436,'#skF_4')
      | ~ m1_subset_1(E_436,k1_zfmisc_1(k2_zfmisc_1(A_434,B_435)))
      | ~ v1_funct_1(E_436) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_5777])).

tff(c_7971,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_7926])).

tff(c_7985,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_7971])).

tff(c_54,plain,(
    ! [F_41,D_39,A_36,E_40,C_38,B_37] :
      ( m1_subset_1(k1_partfun1(A_36,B_37,C_38,D_39,E_40,F_41),k1_zfmisc_1(k2_zfmisc_1(A_36,D_39)))
      | ~ m1_subset_1(F_41,k1_zfmisc_1(k2_zfmisc_1(C_38,D_39)))
      | ~ v1_funct_1(F_41)
      | ~ m1_subset_1(E_40,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_1(E_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_9293,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7985,c_54])).

tff(c_9300,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_9293])).

tff(c_48,plain,(
    ! [A_33] : m1_subset_1(k6_relat_1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_81,plain,(
    ! [A_33] : m1_subset_1(k6_partfun1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_48])).

tff(c_68,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_1152,plain,(
    ! [D_136,C_137,A_138,B_139] :
      ( D_136 = C_137
      | ~ r2_relset_1(A_138,B_139,C_137,D_136)
      | ~ m1_subset_1(D_136,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139)))
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1162,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_1152])).

tff(c_1181,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_1162])).

tff(c_9369,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9300,c_7985,c_7985,c_1181])).

tff(c_78,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_72,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_64,plain,(
    ! [D_52,C_51,E_54,B_50,A_49] :
      ( k1_xboole_0 = C_51
      | v2_funct_1(D_52)
      | ~ v2_funct_1(k1_partfun1(A_49,B_50,B_50,C_51,D_52,E_54))
      | ~ m1_subset_1(E_54,k1_zfmisc_1(k2_zfmisc_1(B_50,C_51)))
      | ~ v1_funct_2(E_54,B_50,C_51)
      | ~ v1_funct_1(E_54)
      | ~ m1_subset_1(D_52,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50)))
      | ~ v1_funct_2(D_52,A_49,B_50)
      | ~ v1_funct_1(D_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_9290,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7985,c_64])).

tff(c_9297,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_72,c_70,c_9290])).

tff(c_9298,plain,
    ( k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_9297])).

tff(c_9302,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_9298])).

tff(c_9372,plain,(
    ~ v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9369,c_9302])).

tff(c_9379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_9372])).

tff(c_9380,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_9298])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_9431,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9380,c_2])).

tff(c_9433,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_348,c_9431])).

tff(c_9434,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_327])).

tff(c_120,plain,(
    ! [B_65,A_66] :
      ( ~ v1_xboole_0(B_65)
      | B_65 = A_66
      | ~ v1_xboole_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_123,plain,(
    ! [A_66] :
      ( k1_xboole_0 = A_66
      | ~ v1_xboole_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_2,c_120])).

tff(c_9451,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_9434,c_123])).

tff(c_36,plain,(
    ! [A_25] : v1_relat_1(k6_relat_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_83,plain,(
    ! [A_25] : v1_relat_1(k6_partfun1(A_25)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_36])).

tff(c_32,plain,(
    ! [A_24] : k1_relat_1(k6_relat_1(A_24)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_85,plain,(
    ! [A_24] : k1_relat_1(k6_partfun1(A_24)) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_32])).

tff(c_221,plain,(
    ! [A_79] :
      ( ~ v1_xboole_0(k1_relat_1(A_79))
      | ~ v1_relat_1(A_79)
      | v1_xboole_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_224,plain,(
    ! [A_24] :
      ( ~ v1_xboole_0(A_24)
      | ~ v1_relat_1(k6_partfun1(A_24))
      | v1_xboole_0(k6_partfun1(A_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_221])).

tff(c_227,plain,(
    ! [A_80] :
      ( ~ v1_xboole_0(A_80)
      | v1_xboole_0(k6_partfun1(A_80)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_224])).

tff(c_241,plain,(
    ! [A_81] :
      ( k6_partfun1(A_81) = k1_xboole_0
      | ~ v1_xboole_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_227,c_123])).

tff(c_257,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_241])).

tff(c_275,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_82])).

tff(c_9456,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9451,c_275])).

tff(c_9468,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_9456])).

tff(c_9469,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_26,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_9773,plain,(
    ! [B_489,A_490] :
      ( v1_relat_1(B_489)
      | ~ m1_subset_1(B_489,k1_zfmisc_1(A_490))
      | ~ v1_relat_1(A_490) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_9785,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_70,c_9773])).

tff(c_9797,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_9785])).

tff(c_10157,plain,(
    ! [C_514,B_515,A_516] :
      ( v5_relat_1(C_514,B_515)
      | ~ m1_subset_1(C_514,k1_zfmisc_1(k2_zfmisc_1(A_516,B_515))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_10179,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_10157])).

tff(c_9782,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_9773])).

tff(c_9794,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_9782])).

tff(c_34,plain,(
    ! [A_24] : k2_relat_1(k6_relat_1(A_24)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_84,plain,(
    ! [A_24] : k2_relat_1(k6_partfun1(A_24)) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_34])).

tff(c_10839,plain,(
    ! [B_568,D_567,E_566,A_569,C_571,F_570] :
      ( k1_partfun1(A_569,B_568,C_571,D_567,E_566,F_570) = k5_relat_1(E_566,F_570)
      | ~ m1_subset_1(F_570,k1_zfmisc_1(k2_zfmisc_1(C_571,D_567)))
      | ~ v1_funct_1(F_570)
      | ~ m1_subset_1(E_566,k1_zfmisc_1(k2_zfmisc_1(A_569,B_568)))
      | ~ v1_funct_1(E_566) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_10853,plain,(
    ! [A_569,B_568,E_566] :
      ( k1_partfun1(A_569,B_568,'#skF_2','#skF_1',E_566,'#skF_4') = k5_relat_1(E_566,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_566,k1_zfmisc_1(k2_zfmisc_1(A_569,B_568)))
      | ~ v1_funct_1(E_566) ) ),
    inference(resolution,[status(thm)],[c_70,c_10839])).

tff(c_12306,plain,(
    ! [A_626,B_627,E_628] :
      ( k1_partfun1(A_626,B_627,'#skF_2','#skF_1',E_628,'#skF_4') = k5_relat_1(E_628,'#skF_4')
      | ~ m1_subset_1(E_628,k1_zfmisc_1(k2_zfmisc_1(A_626,B_627)))
      | ~ v1_funct_1(E_628) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_10853])).

tff(c_12348,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_12306])).

tff(c_12362,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_12348])).

tff(c_13711,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12362,c_54])).

tff(c_13717,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_13711])).

tff(c_10475,plain,(
    ! [D_536,C_537,A_538,B_539] :
      ( D_536 = C_537
      | ~ r2_relset_1(A_538,B_539,C_537,D_536)
      | ~ m1_subset_1(D_536,k1_zfmisc_1(k2_zfmisc_1(A_538,B_539)))
      | ~ m1_subset_1(C_537,k1_zfmisc_1(k2_zfmisc_1(A_538,B_539))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_10485,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_10475])).

tff(c_10504,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_10485])).

tff(c_13821,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13717,c_12362,c_12362,c_10504])).

tff(c_30,plain,(
    ! [A_21,B_23] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_21,B_23)),k2_relat_1(B_23))
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_13843,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13821,c_30])).

tff(c_13851,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9794,c_9797,c_84,c_13843])).

tff(c_9811,plain,(
    ! [B_493,A_494] :
      ( r1_tarski(k2_relat_1(B_493),A_494)
      | ~ v5_relat_1(B_493,A_494)
      | ~ v1_relat_1(B_493) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_9825,plain,(
    ! [B_493,A_494] :
      ( k2_relat_1(B_493) = A_494
      | ~ r1_tarski(A_494,k2_relat_1(B_493))
      | ~ v5_relat_1(B_493,A_494)
      | ~ v1_relat_1(B_493) ) ),
    inference(resolution,[status(thm)],[c_9811,c_4])).

tff(c_13855,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_13851,c_9825])).

tff(c_13860,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9797,c_10179,c_13855])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10043,plain,(
    ! [B_504,A_505] :
      ( v5_relat_1(B_504,A_505)
      | ~ r1_tarski(k2_relat_1(B_504),A_505)
      | ~ v1_relat_1(B_504) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10062,plain,(
    ! [B_504] :
      ( v5_relat_1(B_504,k2_relat_1(B_504))
      | ~ v1_relat_1(B_504) ) ),
    inference(resolution,[status(thm)],[c_8,c_10043])).

tff(c_10202,plain,(
    ! [B_519] :
      ( v2_funct_2(B_519,k2_relat_1(B_519))
      | ~ v5_relat_1(B_519,k2_relat_1(B_519))
      | ~ v1_relat_1(B_519) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_10223,plain,(
    ! [B_504] :
      ( v2_funct_2(B_504,k2_relat_1(B_504))
      | ~ v1_relat_1(B_504) ) ),
    inference(resolution,[status(thm)],[c_10062,c_10202])).

tff(c_13879,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_13860,c_10223])).

tff(c_13900,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9797,c_13879])).

tff(c_13902,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9469,c_13900])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:16:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.07/2.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.07/3.00  
% 9.07/3.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.07/3.00  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.07/3.00  
% 9.07/3.00  %Foreground sorts:
% 9.07/3.00  
% 9.07/3.00  
% 9.07/3.00  %Background operators:
% 9.07/3.00  
% 9.07/3.00  
% 9.07/3.00  %Foreground operators:
% 9.07/3.00  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.07/3.00  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.07/3.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.07/3.00  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.07/3.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.07/3.00  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.07/3.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.07/3.00  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.07/3.00  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.07/3.00  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.07/3.00  tff('#skF_2', type, '#skF_2': $i).
% 9.07/3.00  tff('#skF_3', type, '#skF_3': $i).
% 9.07/3.00  tff('#skF_1', type, '#skF_1': $i).
% 9.07/3.00  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 9.07/3.00  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.07/3.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.07/3.00  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.07/3.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.07/3.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.07/3.00  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.07/3.00  tff('#skF_4', type, '#skF_4': $i).
% 9.07/3.00  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.07/3.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.07/3.00  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.07/3.00  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.07/3.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.07/3.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.07/3.00  
% 9.23/3.02  tff(f_185, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 9.23/3.02  tff(f_50, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 9.23/3.02  tff(f_57, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 9.23/3.02  tff(f_143, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.23/3.02  tff(f_95, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 9.23/3.02  tff(f_141, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.23/3.02  tff(f_131, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 9.23/3.02  tff(f_111, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 9.23/3.02  tff(f_109, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.23/3.02  tff(f_165, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 9.23/3.02  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.23/3.02  tff(f_42, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 9.23/3.02  tff(f_91, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 9.23/3.02  tff(f_80, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 9.23/3.02  tff(f_72, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.23/3.02  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.23/3.02  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.23/3.02  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 9.23/3.02  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 9.23/3.02  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.23/3.02  tff(f_119, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 9.23/3.02  tff(c_66, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_185])).
% 9.23/3.02  tff(c_119, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_66])).
% 9.23/3.02  tff(c_16, plain, (![A_8, B_9]: (v1_xboole_0(k2_zfmisc_1(A_8, B_9)) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.23/3.02  tff(c_76, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_185])).
% 9.23/3.02  tff(c_315, plain, (![B_84, A_85]: (v1_xboole_0(B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(A_85)) | ~v1_xboole_0(A_85))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.23/3.02  tff(c_327, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_76, c_315])).
% 9.23/3.02  tff(c_341, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_327])).
% 9.23/3.02  tff(c_348, plain, (~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_341])).
% 9.23/3.02  tff(c_60, plain, (![A_48]: (k6_relat_1(A_48)=k6_partfun1(A_48))), inference(cnfTransformation, [status(thm)], [f_143])).
% 9.23/3.02  tff(c_38, plain, (![A_25]: (v2_funct_1(k6_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.23/3.02  tff(c_82, plain, (![A_25]: (v2_funct_1(k6_partfun1(A_25)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_38])).
% 9.23/3.02  tff(c_80, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_185])).
% 9.23/3.02  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_185])).
% 9.23/3.02  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_185])).
% 9.23/3.02  tff(c_5765, plain, (![B_345, F_347, D_344, A_346, C_348, E_343]: (k1_partfun1(A_346, B_345, C_348, D_344, E_343, F_347)=k5_relat_1(E_343, F_347) | ~m1_subset_1(F_347, k1_zfmisc_1(k2_zfmisc_1(C_348, D_344))) | ~v1_funct_1(F_347) | ~m1_subset_1(E_343, k1_zfmisc_1(k2_zfmisc_1(A_346, B_345))) | ~v1_funct_1(E_343))), inference(cnfTransformation, [status(thm)], [f_141])).
% 9.23/3.02  tff(c_5777, plain, (![A_346, B_345, E_343]: (k1_partfun1(A_346, B_345, '#skF_2', '#skF_1', E_343, '#skF_4')=k5_relat_1(E_343, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_343, k1_zfmisc_1(k2_zfmisc_1(A_346, B_345))) | ~v1_funct_1(E_343))), inference(resolution, [status(thm)], [c_70, c_5765])).
% 9.23/3.02  tff(c_7926, plain, (![A_434, B_435, E_436]: (k1_partfun1(A_434, B_435, '#skF_2', '#skF_1', E_436, '#skF_4')=k5_relat_1(E_436, '#skF_4') | ~m1_subset_1(E_436, k1_zfmisc_1(k2_zfmisc_1(A_434, B_435))) | ~v1_funct_1(E_436))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_5777])).
% 9.23/3.02  tff(c_7971, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_7926])).
% 9.23/3.02  tff(c_7985, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_7971])).
% 9.23/3.02  tff(c_54, plain, (![F_41, D_39, A_36, E_40, C_38, B_37]: (m1_subset_1(k1_partfun1(A_36, B_37, C_38, D_39, E_40, F_41), k1_zfmisc_1(k2_zfmisc_1(A_36, D_39))) | ~m1_subset_1(F_41, k1_zfmisc_1(k2_zfmisc_1(C_38, D_39))) | ~v1_funct_1(F_41) | ~m1_subset_1(E_40, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_1(E_40))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.23/3.02  tff(c_9293, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7985, c_54])).
% 9.23/3.02  tff(c_9300, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_9293])).
% 9.23/3.02  tff(c_48, plain, (![A_33]: (m1_subset_1(k6_relat_1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.23/3.02  tff(c_81, plain, (![A_33]: (m1_subset_1(k6_partfun1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_48])).
% 9.23/3.02  tff(c_68, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_185])).
% 9.23/3.02  tff(c_1152, plain, (![D_136, C_137, A_138, B_139]: (D_136=C_137 | ~r2_relset_1(A_138, B_139, C_137, D_136) | ~m1_subset_1(D_136, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.23/3.02  tff(c_1162, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_1152])).
% 9.23/3.02  tff(c_1181, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_1162])).
% 9.23/3.02  tff(c_9369, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9300, c_7985, c_7985, c_1181])).
% 9.23/3.02  tff(c_78, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_185])).
% 9.23/3.02  tff(c_72, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_185])).
% 9.23/3.02  tff(c_64, plain, (![D_52, C_51, E_54, B_50, A_49]: (k1_xboole_0=C_51 | v2_funct_1(D_52) | ~v2_funct_1(k1_partfun1(A_49, B_50, B_50, C_51, D_52, E_54)) | ~m1_subset_1(E_54, k1_zfmisc_1(k2_zfmisc_1(B_50, C_51))) | ~v1_funct_2(E_54, B_50, C_51) | ~v1_funct_1(E_54) | ~m1_subset_1(D_52, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))) | ~v1_funct_2(D_52, A_49, B_50) | ~v1_funct_1(D_52))), inference(cnfTransformation, [status(thm)], [f_165])).
% 9.23/3.02  tff(c_9290, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7985, c_64])).
% 9.23/3.02  tff(c_9297, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_72, c_70, c_9290])).
% 9.23/3.02  tff(c_9298, plain, (k1_xboole_0='#skF_1' | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_119, c_9297])).
% 9.23/3.02  tff(c_9302, plain, (~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_9298])).
% 9.23/3.02  tff(c_9372, plain, (~v2_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9369, c_9302])).
% 9.23/3.02  tff(c_9379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_9372])).
% 9.23/3.02  tff(c_9380, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_9298])).
% 9.23/3.02  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 9.23/3.02  tff(c_9431, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9380, c_2])).
% 9.23/3.02  tff(c_9433, plain, $false, inference(negUnitSimplification, [status(thm)], [c_348, c_9431])).
% 9.23/3.02  tff(c_9434, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_327])).
% 9.23/3.02  tff(c_120, plain, (![B_65, A_66]: (~v1_xboole_0(B_65) | B_65=A_66 | ~v1_xboole_0(A_66))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.23/3.02  tff(c_123, plain, (![A_66]: (k1_xboole_0=A_66 | ~v1_xboole_0(A_66))), inference(resolution, [status(thm)], [c_2, c_120])).
% 9.23/3.02  tff(c_9451, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_9434, c_123])).
% 9.23/3.02  tff(c_36, plain, (![A_25]: (v1_relat_1(k6_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.23/3.02  tff(c_83, plain, (![A_25]: (v1_relat_1(k6_partfun1(A_25)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_36])).
% 9.23/3.02  tff(c_32, plain, (![A_24]: (k1_relat_1(k6_relat_1(A_24))=A_24)), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.23/3.02  tff(c_85, plain, (![A_24]: (k1_relat_1(k6_partfun1(A_24))=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_32])).
% 9.23/3.02  tff(c_221, plain, (![A_79]: (~v1_xboole_0(k1_relat_1(A_79)) | ~v1_relat_1(A_79) | v1_xboole_0(A_79))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.23/3.02  tff(c_224, plain, (![A_24]: (~v1_xboole_0(A_24) | ~v1_relat_1(k6_partfun1(A_24)) | v1_xboole_0(k6_partfun1(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_85, c_221])).
% 9.23/3.02  tff(c_227, plain, (![A_80]: (~v1_xboole_0(A_80) | v1_xboole_0(k6_partfun1(A_80)))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_224])).
% 9.23/3.02  tff(c_241, plain, (![A_81]: (k6_partfun1(A_81)=k1_xboole_0 | ~v1_xboole_0(A_81))), inference(resolution, [status(thm)], [c_227, c_123])).
% 9.23/3.02  tff(c_257, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_241])).
% 9.23/3.02  tff(c_275, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_257, c_82])).
% 9.23/3.02  tff(c_9456, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9451, c_275])).
% 9.23/3.02  tff(c_9468, plain, $false, inference(negUnitSimplification, [status(thm)], [c_119, c_9456])).
% 9.23/3.02  tff(c_9469, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_66])).
% 9.23/3.02  tff(c_26, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.23/3.02  tff(c_9773, plain, (![B_489, A_490]: (v1_relat_1(B_489) | ~m1_subset_1(B_489, k1_zfmisc_1(A_490)) | ~v1_relat_1(A_490))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.23/3.02  tff(c_9785, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_70, c_9773])).
% 9.23/3.02  tff(c_9797, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_9785])).
% 9.23/3.02  tff(c_10157, plain, (![C_514, B_515, A_516]: (v5_relat_1(C_514, B_515) | ~m1_subset_1(C_514, k1_zfmisc_1(k2_zfmisc_1(A_516, B_515))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.23/3.02  tff(c_10179, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_10157])).
% 9.23/3.02  tff(c_9782, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_76, c_9773])).
% 9.23/3.02  tff(c_9794, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_9782])).
% 9.23/3.02  tff(c_34, plain, (![A_24]: (k2_relat_1(k6_relat_1(A_24))=A_24)), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.23/3.02  tff(c_84, plain, (![A_24]: (k2_relat_1(k6_partfun1(A_24))=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_34])).
% 9.23/3.02  tff(c_10839, plain, (![B_568, D_567, E_566, A_569, C_571, F_570]: (k1_partfun1(A_569, B_568, C_571, D_567, E_566, F_570)=k5_relat_1(E_566, F_570) | ~m1_subset_1(F_570, k1_zfmisc_1(k2_zfmisc_1(C_571, D_567))) | ~v1_funct_1(F_570) | ~m1_subset_1(E_566, k1_zfmisc_1(k2_zfmisc_1(A_569, B_568))) | ~v1_funct_1(E_566))), inference(cnfTransformation, [status(thm)], [f_141])).
% 9.23/3.02  tff(c_10853, plain, (![A_569, B_568, E_566]: (k1_partfun1(A_569, B_568, '#skF_2', '#skF_1', E_566, '#skF_4')=k5_relat_1(E_566, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_566, k1_zfmisc_1(k2_zfmisc_1(A_569, B_568))) | ~v1_funct_1(E_566))), inference(resolution, [status(thm)], [c_70, c_10839])).
% 9.23/3.02  tff(c_12306, plain, (![A_626, B_627, E_628]: (k1_partfun1(A_626, B_627, '#skF_2', '#skF_1', E_628, '#skF_4')=k5_relat_1(E_628, '#skF_4') | ~m1_subset_1(E_628, k1_zfmisc_1(k2_zfmisc_1(A_626, B_627))) | ~v1_funct_1(E_628))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_10853])).
% 9.23/3.02  tff(c_12348, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_12306])).
% 9.23/3.02  tff(c_12362, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_12348])).
% 9.23/3.02  tff(c_13711, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12362, c_54])).
% 9.23/3.02  tff(c_13717, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_13711])).
% 9.23/3.02  tff(c_10475, plain, (![D_536, C_537, A_538, B_539]: (D_536=C_537 | ~r2_relset_1(A_538, B_539, C_537, D_536) | ~m1_subset_1(D_536, k1_zfmisc_1(k2_zfmisc_1(A_538, B_539))) | ~m1_subset_1(C_537, k1_zfmisc_1(k2_zfmisc_1(A_538, B_539))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.23/3.02  tff(c_10485, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_10475])).
% 9.23/3.02  tff(c_10504, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_10485])).
% 9.23/3.02  tff(c_13821, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13717, c_12362, c_12362, c_10504])).
% 9.23/3.02  tff(c_30, plain, (![A_21, B_23]: (r1_tarski(k2_relat_1(k5_relat_1(A_21, B_23)), k2_relat_1(B_23)) | ~v1_relat_1(B_23) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.23/3.02  tff(c_13843, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_1')), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13821, c_30])).
% 9.23/3.02  tff(c_13851, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9794, c_9797, c_84, c_13843])).
% 9.23/3.02  tff(c_9811, plain, (![B_493, A_494]: (r1_tarski(k2_relat_1(B_493), A_494) | ~v5_relat_1(B_493, A_494) | ~v1_relat_1(B_493))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.23/3.02  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.23/3.02  tff(c_9825, plain, (![B_493, A_494]: (k2_relat_1(B_493)=A_494 | ~r1_tarski(A_494, k2_relat_1(B_493)) | ~v5_relat_1(B_493, A_494) | ~v1_relat_1(B_493))), inference(resolution, [status(thm)], [c_9811, c_4])).
% 9.23/3.02  tff(c_13855, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_13851, c_9825])).
% 9.23/3.02  tff(c_13860, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9797, c_10179, c_13855])).
% 9.23/3.02  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.23/3.02  tff(c_10043, plain, (![B_504, A_505]: (v5_relat_1(B_504, A_505) | ~r1_tarski(k2_relat_1(B_504), A_505) | ~v1_relat_1(B_504))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.23/3.02  tff(c_10062, plain, (![B_504]: (v5_relat_1(B_504, k2_relat_1(B_504)) | ~v1_relat_1(B_504))), inference(resolution, [status(thm)], [c_8, c_10043])).
% 9.23/3.02  tff(c_10202, plain, (![B_519]: (v2_funct_2(B_519, k2_relat_1(B_519)) | ~v5_relat_1(B_519, k2_relat_1(B_519)) | ~v1_relat_1(B_519))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.23/3.02  tff(c_10223, plain, (![B_504]: (v2_funct_2(B_504, k2_relat_1(B_504)) | ~v1_relat_1(B_504))), inference(resolution, [status(thm)], [c_10062, c_10202])).
% 9.23/3.02  tff(c_13879, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_13860, c_10223])).
% 9.23/3.02  tff(c_13900, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9797, c_13879])).
% 9.23/3.02  tff(c_13902, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9469, c_13900])).
% 9.23/3.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.23/3.02  
% 9.23/3.02  Inference rules
% 9.23/3.02  ----------------------
% 9.23/3.02  #Ref     : 0
% 9.23/3.02  #Sup     : 3400
% 9.23/3.02  #Fact    : 0
% 9.23/3.02  #Define  : 0
% 9.23/3.02  #Split   : 18
% 9.23/3.02  #Chain   : 0
% 9.23/3.02  #Close   : 0
% 9.23/3.02  
% 9.23/3.02  Ordering : KBO
% 9.23/3.02  
% 9.23/3.02  Simplification rules
% 9.23/3.02  ----------------------
% 9.23/3.02  #Subsume      : 235
% 9.23/3.02  #Demod        : 3193
% 9.23/3.02  #Tautology    : 2042
% 9.23/3.02  #SimpNegUnit  : 5
% 9.23/3.02  #BackRed      : 92
% 9.23/3.02  
% 9.23/3.02  #Partial instantiations: 0
% 9.23/3.02  #Strategies tried      : 1
% 9.23/3.02  
% 9.23/3.02  Timing (in seconds)
% 9.23/3.02  ----------------------
% 9.23/3.03  Preprocessing        : 0.37
% 9.23/3.03  Parsing              : 0.19
% 9.23/3.03  CNF conversion       : 0.03
% 9.23/3.03  Main loop            : 1.84
% 9.23/3.03  Inferencing          : 0.53
% 9.23/3.03  Reduction            : 0.67
% 9.23/3.03  Demodulation         : 0.50
% 9.23/3.03  BG Simplification    : 0.07
% 9.23/3.03  Subsumption          : 0.43
% 9.23/3.03  Abstraction          : 0.08
% 9.23/3.03  MUC search           : 0.00
% 9.23/3.03  Cooper               : 0.00
% 9.23/3.03  Total                : 2.25
% 9.23/3.03  Index Insertion      : 0.00
% 9.23/3.03  Index Deletion       : 0.00
% 9.23/3.03  Index Matching       : 0.00
% 9.23/3.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
