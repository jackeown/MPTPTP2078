%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:18 EST 2020

% Result     : Theorem 8.86s
% Output     : CNFRefutation 8.86s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 362 expanded)
%              Number of leaves         :   48 ( 145 expanded)
%              Depth                    :   15
%              Number of atoms          :  268 (1162 expanded)
%              Number of equality atoms :   45 ( 109 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_143,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_141,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_131,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_111,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_109,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_91,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_72,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_119,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

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

tff(c_5778,plain,(
    ! [B_345,F_347,D_344,A_346,C_348,E_343] :
      ( k1_partfun1(A_346,B_345,C_348,D_344,E_343,F_347) = k5_relat_1(E_343,F_347)
      | ~ m1_subset_1(F_347,k1_zfmisc_1(k2_zfmisc_1(C_348,D_344)))
      | ~ v1_funct_1(F_347)
      | ~ m1_subset_1(E_343,k1_zfmisc_1(k2_zfmisc_1(A_346,B_345)))
      | ~ v1_funct_1(E_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_5790,plain,(
    ! [A_346,B_345,E_343] :
      ( k1_partfun1(A_346,B_345,'#skF_2','#skF_1',E_343,'#skF_4') = k5_relat_1(E_343,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_343,k1_zfmisc_1(k2_zfmisc_1(A_346,B_345)))
      | ~ v1_funct_1(E_343) ) ),
    inference(resolution,[status(thm)],[c_70,c_5778])).

tff(c_8156,plain,(
    ! [A_436,B_437,E_438] :
      ( k1_partfun1(A_436,B_437,'#skF_2','#skF_1',E_438,'#skF_4') = k5_relat_1(E_438,'#skF_4')
      | ~ m1_subset_1(E_438,k1_zfmisc_1(k2_zfmisc_1(A_436,B_437)))
      | ~ v1_funct_1(E_438) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_5790])).

tff(c_8201,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_8156])).

tff(c_8215,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_8201])).

tff(c_54,plain,(
    ! [F_41,D_39,A_36,E_40,C_38,B_37] :
      ( m1_subset_1(k1_partfun1(A_36,B_37,C_38,D_39,E_40,F_41),k1_zfmisc_1(k2_zfmisc_1(A_36,D_39)))
      | ~ m1_subset_1(F_41,k1_zfmisc_1(k2_zfmisc_1(C_38,D_39)))
      | ~ v1_funct_1(F_41)
      | ~ m1_subset_1(E_40,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_1(E_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_9289,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8215,c_54])).

tff(c_9296,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_9289])).

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

tff(c_9365,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9296,c_8215,c_8215,c_1181])).

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

tff(c_9286,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8215,c_64])).

tff(c_9293,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_72,c_70,c_9286])).

tff(c_9294,plain,
    ( k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_9293])).

tff(c_9298,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_9294])).

tff(c_9368,plain,(
    ~ v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9365,c_9298])).

tff(c_9375,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_9368])).

tff(c_9376,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_9294])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_9427,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9376,c_2])).

tff(c_9429,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_348,c_9427])).

tff(c_9430,plain,(
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

tff(c_9447,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_9430,c_123])).

tff(c_36,plain,(
    ! [A_25] : v1_relat_1(k6_relat_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_83,plain,(
    ! [A_25] : v1_relat_1(k6_partfun1(A_25)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_36])).

tff(c_34,plain,(
    ! [A_24] : k2_relat_1(k6_relat_1(A_24)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_84,plain,(
    ! [A_24] : k2_relat_1(k6_partfun1(A_24)) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_34])).

tff(c_221,plain,(
    ! [A_79] :
      ( ~ v1_xboole_0(k2_relat_1(A_79))
      | ~ v1_relat_1(A_79)
      | v1_xboole_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_224,plain,(
    ! [A_24] :
      ( ~ v1_xboole_0(A_24)
      | ~ v1_relat_1(k6_partfun1(A_24))
      | v1_xboole_0(k6_partfun1(A_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_221])).

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

tff(c_9452,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9447,c_275])).

tff(c_9464,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_9452])).

tff(c_9465,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_26,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_9769,plain,(
    ! [B_489,A_490] :
      ( v1_relat_1(B_489)
      | ~ m1_subset_1(B_489,k1_zfmisc_1(A_490))
      | ~ v1_relat_1(A_490) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_9781,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_70,c_9769])).

tff(c_9793,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_9781])).

tff(c_10153,plain,(
    ! [C_514,B_515,A_516] :
      ( v5_relat_1(C_514,B_515)
      | ~ m1_subset_1(C_514,k1_zfmisc_1(k2_zfmisc_1(A_516,B_515))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_10175,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_10153])).

tff(c_9778,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_9769])).

tff(c_9790,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_9778])).

tff(c_10835,plain,(
    ! [B_568,D_567,E_566,A_569,C_571,F_570] :
      ( k1_partfun1(A_569,B_568,C_571,D_567,E_566,F_570) = k5_relat_1(E_566,F_570)
      | ~ m1_subset_1(F_570,k1_zfmisc_1(k2_zfmisc_1(C_571,D_567)))
      | ~ v1_funct_1(F_570)
      | ~ m1_subset_1(E_566,k1_zfmisc_1(k2_zfmisc_1(A_569,B_568)))
      | ~ v1_funct_1(E_566) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_10849,plain,(
    ! [A_569,B_568,E_566] :
      ( k1_partfun1(A_569,B_568,'#skF_2','#skF_1',E_566,'#skF_4') = k5_relat_1(E_566,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_566,k1_zfmisc_1(k2_zfmisc_1(A_569,B_568)))
      | ~ v1_funct_1(E_566) ) ),
    inference(resolution,[status(thm)],[c_70,c_10835])).

tff(c_12307,plain,(
    ! [A_626,B_627,E_628] :
      ( k1_partfun1(A_626,B_627,'#skF_2','#skF_1',E_628,'#skF_4') = k5_relat_1(E_628,'#skF_4')
      | ~ m1_subset_1(E_628,k1_zfmisc_1(k2_zfmisc_1(A_626,B_627)))
      | ~ v1_funct_1(E_628) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_10849])).

tff(c_12349,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_12307])).

tff(c_12363,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_12349])).

tff(c_13712,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12363,c_54])).

tff(c_13718,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_13712])).

tff(c_10471,plain,(
    ! [D_536,C_537,A_538,B_539] :
      ( D_536 = C_537
      | ~ r2_relset_1(A_538,B_539,C_537,D_536)
      | ~ m1_subset_1(D_536,k1_zfmisc_1(k2_zfmisc_1(A_538,B_539)))
      | ~ m1_subset_1(C_537,k1_zfmisc_1(k2_zfmisc_1(A_538,B_539))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_10481,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_10471])).

tff(c_10500,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_10481])).

tff(c_13822,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13718,c_12363,c_12363,c_10500])).

tff(c_30,plain,(
    ! [A_21,B_23] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_21,B_23)),k2_relat_1(B_23))
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_13844,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13822,c_30])).

tff(c_13852,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9790,c_9793,c_84,c_13844])).

tff(c_9807,plain,(
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

tff(c_9821,plain,(
    ! [B_493,A_494] :
      ( k2_relat_1(B_493) = A_494
      | ~ r1_tarski(A_494,k2_relat_1(B_493))
      | ~ v5_relat_1(B_493,A_494)
      | ~ v1_relat_1(B_493) ) ),
    inference(resolution,[status(thm)],[c_9807,c_4])).

tff(c_13856,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_13852,c_9821])).

tff(c_13861,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9793,c_10175,c_13856])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10039,plain,(
    ! [B_504,A_505] :
      ( v5_relat_1(B_504,A_505)
      | ~ r1_tarski(k2_relat_1(B_504),A_505)
      | ~ v1_relat_1(B_504) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10058,plain,(
    ! [B_504] :
      ( v5_relat_1(B_504,k2_relat_1(B_504))
      | ~ v1_relat_1(B_504) ) ),
    inference(resolution,[status(thm)],[c_8,c_10039])).

tff(c_10198,plain,(
    ! [B_519] :
      ( v2_funct_2(B_519,k2_relat_1(B_519))
      | ~ v5_relat_1(B_519,k2_relat_1(B_519))
      | ~ v1_relat_1(B_519) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_10219,plain,(
    ! [B_504] :
      ( v2_funct_2(B_504,k2_relat_1(B_504))
      | ~ v1_relat_1(B_504) ) ),
    inference(resolution,[status(thm)],[c_10058,c_10198])).

tff(c_13880,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_13861,c_10219])).

tff(c_13904,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9793,c_13880])).

tff(c_13906,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9465,c_13904])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:31:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.86/2.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.86/2.98  
% 8.86/2.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.86/2.98  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.86/2.98  
% 8.86/2.98  %Foreground sorts:
% 8.86/2.98  
% 8.86/2.98  
% 8.86/2.98  %Background operators:
% 8.86/2.98  
% 8.86/2.98  
% 8.86/2.98  %Foreground operators:
% 8.86/2.98  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.86/2.98  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.86/2.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.86/2.98  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 8.86/2.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.86/2.98  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.86/2.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.86/2.98  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.86/2.98  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.86/2.98  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.86/2.98  tff('#skF_2', type, '#skF_2': $i).
% 8.86/2.98  tff('#skF_3', type, '#skF_3': $i).
% 8.86/2.98  tff('#skF_1', type, '#skF_1': $i).
% 8.86/2.98  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 8.86/2.98  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.86/2.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.86/2.98  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 8.86/2.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.86/2.98  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.86/2.98  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.86/2.98  tff('#skF_4', type, '#skF_4': $i).
% 8.86/2.98  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.86/2.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.86/2.98  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.86/2.98  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.86/2.98  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.86/2.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.86/2.98  
% 8.86/3.00  tff(f_185, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 8.86/3.00  tff(f_50, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 8.86/3.00  tff(f_57, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 8.86/3.00  tff(f_143, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 8.86/3.00  tff(f_95, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 8.86/3.00  tff(f_141, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 8.86/3.00  tff(f_131, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 8.86/3.00  tff(f_111, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 8.86/3.00  tff(f_109, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 8.86/3.00  tff(f_165, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 8.86/3.00  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.86/3.00  tff(f_42, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 8.86/3.00  tff(f_91, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 8.86/3.00  tff(f_80, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 8.86/3.00  tff(f_72, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.86/3.00  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.86/3.00  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.86/3.00  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 8.86/3.00  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 8.86/3.00  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.86/3.00  tff(f_119, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 8.86/3.00  tff(c_66, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_185])).
% 8.86/3.00  tff(c_119, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_66])).
% 8.86/3.00  tff(c_16, plain, (![A_8, B_9]: (v1_xboole_0(k2_zfmisc_1(A_8, B_9)) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.86/3.00  tff(c_76, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_185])).
% 8.86/3.00  tff(c_315, plain, (![B_84, A_85]: (v1_xboole_0(B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(A_85)) | ~v1_xboole_0(A_85))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.86/3.00  tff(c_327, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_76, c_315])).
% 8.86/3.00  tff(c_341, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_327])).
% 8.86/3.00  tff(c_348, plain, (~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_341])).
% 8.86/3.00  tff(c_60, plain, (![A_48]: (k6_relat_1(A_48)=k6_partfun1(A_48))), inference(cnfTransformation, [status(thm)], [f_143])).
% 8.86/3.00  tff(c_38, plain, (![A_25]: (v2_funct_1(k6_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.86/3.00  tff(c_82, plain, (![A_25]: (v2_funct_1(k6_partfun1(A_25)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_38])).
% 8.86/3.00  tff(c_80, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_185])).
% 8.86/3.00  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_185])).
% 8.86/3.00  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_185])).
% 8.86/3.00  tff(c_5778, plain, (![B_345, F_347, D_344, A_346, C_348, E_343]: (k1_partfun1(A_346, B_345, C_348, D_344, E_343, F_347)=k5_relat_1(E_343, F_347) | ~m1_subset_1(F_347, k1_zfmisc_1(k2_zfmisc_1(C_348, D_344))) | ~v1_funct_1(F_347) | ~m1_subset_1(E_343, k1_zfmisc_1(k2_zfmisc_1(A_346, B_345))) | ~v1_funct_1(E_343))), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.86/3.00  tff(c_5790, plain, (![A_346, B_345, E_343]: (k1_partfun1(A_346, B_345, '#skF_2', '#skF_1', E_343, '#skF_4')=k5_relat_1(E_343, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_343, k1_zfmisc_1(k2_zfmisc_1(A_346, B_345))) | ~v1_funct_1(E_343))), inference(resolution, [status(thm)], [c_70, c_5778])).
% 8.86/3.00  tff(c_8156, plain, (![A_436, B_437, E_438]: (k1_partfun1(A_436, B_437, '#skF_2', '#skF_1', E_438, '#skF_4')=k5_relat_1(E_438, '#skF_4') | ~m1_subset_1(E_438, k1_zfmisc_1(k2_zfmisc_1(A_436, B_437))) | ~v1_funct_1(E_438))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_5790])).
% 8.86/3.00  tff(c_8201, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_8156])).
% 8.86/3.00  tff(c_8215, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_8201])).
% 8.86/3.00  tff(c_54, plain, (![F_41, D_39, A_36, E_40, C_38, B_37]: (m1_subset_1(k1_partfun1(A_36, B_37, C_38, D_39, E_40, F_41), k1_zfmisc_1(k2_zfmisc_1(A_36, D_39))) | ~m1_subset_1(F_41, k1_zfmisc_1(k2_zfmisc_1(C_38, D_39))) | ~v1_funct_1(F_41) | ~m1_subset_1(E_40, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_1(E_40))), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.86/3.00  tff(c_9289, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8215, c_54])).
% 8.86/3.00  tff(c_9296, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_9289])).
% 8.86/3.00  tff(c_48, plain, (![A_33]: (m1_subset_1(k6_relat_1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.86/3.00  tff(c_81, plain, (![A_33]: (m1_subset_1(k6_partfun1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_48])).
% 8.86/3.00  tff(c_68, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_185])).
% 8.86/3.00  tff(c_1152, plain, (![D_136, C_137, A_138, B_139]: (D_136=C_137 | ~r2_relset_1(A_138, B_139, C_137, D_136) | ~m1_subset_1(D_136, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.86/3.00  tff(c_1162, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_1152])).
% 8.86/3.00  tff(c_1181, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_1162])).
% 8.86/3.00  tff(c_9365, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9296, c_8215, c_8215, c_1181])).
% 8.86/3.00  tff(c_78, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_185])).
% 8.86/3.00  tff(c_72, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_185])).
% 8.86/3.00  tff(c_64, plain, (![D_52, C_51, E_54, B_50, A_49]: (k1_xboole_0=C_51 | v2_funct_1(D_52) | ~v2_funct_1(k1_partfun1(A_49, B_50, B_50, C_51, D_52, E_54)) | ~m1_subset_1(E_54, k1_zfmisc_1(k2_zfmisc_1(B_50, C_51))) | ~v1_funct_2(E_54, B_50, C_51) | ~v1_funct_1(E_54) | ~m1_subset_1(D_52, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))) | ~v1_funct_2(D_52, A_49, B_50) | ~v1_funct_1(D_52))), inference(cnfTransformation, [status(thm)], [f_165])).
% 8.86/3.00  tff(c_9286, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8215, c_64])).
% 8.86/3.00  tff(c_9293, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_72, c_70, c_9286])).
% 8.86/3.00  tff(c_9294, plain, (k1_xboole_0='#skF_1' | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_119, c_9293])).
% 8.86/3.00  tff(c_9298, plain, (~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_9294])).
% 8.86/3.00  tff(c_9368, plain, (~v2_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9365, c_9298])).
% 8.86/3.00  tff(c_9375, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_9368])).
% 8.86/3.00  tff(c_9376, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_9294])).
% 8.86/3.00  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 8.86/3.00  tff(c_9427, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9376, c_2])).
% 8.86/3.00  tff(c_9429, plain, $false, inference(negUnitSimplification, [status(thm)], [c_348, c_9427])).
% 8.86/3.00  tff(c_9430, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_327])).
% 8.86/3.00  tff(c_120, plain, (![B_65, A_66]: (~v1_xboole_0(B_65) | B_65=A_66 | ~v1_xboole_0(A_66))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.86/3.00  tff(c_123, plain, (![A_66]: (k1_xboole_0=A_66 | ~v1_xboole_0(A_66))), inference(resolution, [status(thm)], [c_2, c_120])).
% 8.86/3.00  tff(c_9447, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_9430, c_123])).
% 8.86/3.00  tff(c_36, plain, (![A_25]: (v1_relat_1(k6_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.86/3.00  tff(c_83, plain, (![A_25]: (v1_relat_1(k6_partfun1(A_25)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_36])).
% 8.86/3.00  tff(c_34, plain, (![A_24]: (k2_relat_1(k6_relat_1(A_24))=A_24)), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.86/3.00  tff(c_84, plain, (![A_24]: (k2_relat_1(k6_partfun1(A_24))=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_34])).
% 8.86/3.00  tff(c_221, plain, (![A_79]: (~v1_xboole_0(k2_relat_1(A_79)) | ~v1_relat_1(A_79) | v1_xboole_0(A_79))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.86/3.00  tff(c_224, plain, (![A_24]: (~v1_xboole_0(A_24) | ~v1_relat_1(k6_partfun1(A_24)) | v1_xboole_0(k6_partfun1(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_84, c_221])).
% 8.86/3.00  tff(c_227, plain, (![A_80]: (~v1_xboole_0(A_80) | v1_xboole_0(k6_partfun1(A_80)))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_224])).
% 8.86/3.00  tff(c_241, plain, (![A_81]: (k6_partfun1(A_81)=k1_xboole_0 | ~v1_xboole_0(A_81))), inference(resolution, [status(thm)], [c_227, c_123])).
% 8.86/3.00  tff(c_257, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_241])).
% 8.86/3.00  tff(c_275, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_257, c_82])).
% 8.86/3.00  tff(c_9452, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9447, c_275])).
% 8.86/3.00  tff(c_9464, plain, $false, inference(negUnitSimplification, [status(thm)], [c_119, c_9452])).
% 8.86/3.00  tff(c_9465, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_66])).
% 8.86/3.00  tff(c_26, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.86/3.00  tff(c_9769, plain, (![B_489, A_490]: (v1_relat_1(B_489) | ~m1_subset_1(B_489, k1_zfmisc_1(A_490)) | ~v1_relat_1(A_490))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.86/3.00  tff(c_9781, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_70, c_9769])).
% 8.86/3.00  tff(c_9793, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_9781])).
% 8.86/3.00  tff(c_10153, plain, (![C_514, B_515, A_516]: (v5_relat_1(C_514, B_515) | ~m1_subset_1(C_514, k1_zfmisc_1(k2_zfmisc_1(A_516, B_515))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.86/3.00  tff(c_10175, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_10153])).
% 8.86/3.00  tff(c_9778, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_76, c_9769])).
% 8.86/3.00  tff(c_9790, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_9778])).
% 8.86/3.00  tff(c_10835, plain, (![B_568, D_567, E_566, A_569, C_571, F_570]: (k1_partfun1(A_569, B_568, C_571, D_567, E_566, F_570)=k5_relat_1(E_566, F_570) | ~m1_subset_1(F_570, k1_zfmisc_1(k2_zfmisc_1(C_571, D_567))) | ~v1_funct_1(F_570) | ~m1_subset_1(E_566, k1_zfmisc_1(k2_zfmisc_1(A_569, B_568))) | ~v1_funct_1(E_566))), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.86/3.00  tff(c_10849, plain, (![A_569, B_568, E_566]: (k1_partfun1(A_569, B_568, '#skF_2', '#skF_1', E_566, '#skF_4')=k5_relat_1(E_566, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_566, k1_zfmisc_1(k2_zfmisc_1(A_569, B_568))) | ~v1_funct_1(E_566))), inference(resolution, [status(thm)], [c_70, c_10835])).
% 8.86/3.00  tff(c_12307, plain, (![A_626, B_627, E_628]: (k1_partfun1(A_626, B_627, '#skF_2', '#skF_1', E_628, '#skF_4')=k5_relat_1(E_628, '#skF_4') | ~m1_subset_1(E_628, k1_zfmisc_1(k2_zfmisc_1(A_626, B_627))) | ~v1_funct_1(E_628))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_10849])).
% 8.86/3.00  tff(c_12349, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_12307])).
% 8.86/3.00  tff(c_12363, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_12349])).
% 8.86/3.00  tff(c_13712, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12363, c_54])).
% 8.86/3.00  tff(c_13718, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_13712])).
% 8.86/3.00  tff(c_10471, plain, (![D_536, C_537, A_538, B_539]: (D_536=C_537 | ~r2_relset_1(A_538, B_539, C_537, D_536) | ~m1_subset_1(D_536, k1_zfmisc_1(k2_zfmisc_1(A_538, B_539))) | ~m1_subset_1(C_537, k1_zfmisc_1(k2_zfmisc_1(A_538, B_539))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.86/3.00  tff(c_10481, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_10471])).
% 8.86/3.00  tff(c_10500, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_10481])).
% 8.86/3.00  tff(c_13822, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13718, c_12363, c_12363, c_10500])).
% 8.86/3.00  tff(c_30, plain, (![A_21, B_23]: (r1_tarski(k2_relat_1(k5_relat_1(A_21, B_23)), k2_relat_1(B_23)) | ~v1_relat_1(B_23) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.86/3.00  tff(c_13844, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_1')), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13822, c_30])).
% 8.86/3.00  tff(c_13852, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9790, c_9793, c_84, c_13844])).
% 8.86/3.00  tff(c_9807, plain, (![B_493, A_494]: (r1_tarski(k2_relat_1(B_493), A_494) | ~v5_relat_1(B_493, A_494) | ~v1_relat_1(B_493))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.86/3.00  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.86/3.00  tff(c_9821, plain, (![B_493, A_494]: (k2_relat_1(B_493)=A_494 | ~r1_tarski(A_494, k2_relat_1(B_493)) | ~v5_relat_1(B_493, A_494) | ~v1_relat_1(B_493))), inference(resolution, [status(thm)], [c_9807, c_4])).
% 8.86/3.00  tff(c_13856, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_13852, c_9821])).
% 8.86/3.00  tff(c_13861, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9793, c_10175, c_13856])).
% 8.86/3.00  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.86/3.00  tff(c_10039, plain, (![B_504, A_505]: (v5_relat_1(B_504, A_505) | ~r1_tarski(k2_relat_1(B_504), A_505) | ~v1_relat_1(B_504))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.86/3.00  tff(c_10058, plain, (![B_504]: (v5_relat_1(B_504, k2_relat_1(B_504)) | ~v1_relat_1(B_504))), inference(resolution, [status(thm)], [c_8, c_10039])).
% 8.86/3.00  tff(c_10198, plain, (![B_519]: (v2_funct_2(B_519, k2_relat_1(B_519)) | ~v5_relat_1(B_519, k2_relat_1(B_519)) | ~v1_relat_1(B_519))), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.86/3.00  tff(c_10219, plain, (![B_504]: (v2_funct_2(B_504, k2_relat_1(B_504)) | ~v1_relat_1(B_504))), inference(resolution, [status(thm)], [c_10058, c_10198])).
% 8.86/3.00  tff(c_13880, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_13861, c_10219])).
% 8.86/3.00  tff(c_13904, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9793, c_13880])).
% 8.86/3.00  tff(c_13906, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9465, c_13904])).
% 8.86/3.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.86/3.00  
% 8.86/3.00  Inference rules
% 8.86/3.00  ----------------------
% 8.86/3.00  #Ref     : 0
% 8.86/3.00  #Sup     : 3404
% 8.86/3.00  #Fact    : 0
% 8.86/3.00  #Define  : 0
% 8.86/3.00  #Split   : 18
% 8.86/3.00  #Chain   : 0
% 8.86/3.00  #Close   : 0
% 8.86/3.00  
% 8.86/3.00  Ordering : KBO
% 8.86/3.00  
% 8.86/3.00  Simplification rules
% 8.86/3.00  ----------------------
% 8.86/3.00  #Subsume      : 235
% 8.86/3.00  #Demod        : 3190
% 8.86/3.00  #Tautology    : 2042
% 8.86/3.00  #SimpNegUnit  : 5
% 8.86/3.00  #BackRed      : 92
% 8.86/3.00  
% 8.86/3.00  #Partial instantiations: 0
% 8.86/3.00  #Strategies tried      : 1
% 8.86/3.00  
% 8.86/3.00  Timing (in seconds)
% 8.86/3.00  ----------------------
% 8.86/3.01  Preprocessing        : 0.36
% 8.86/3.01  Parsing              : 0.19
% 8.86/3.01  CNF conversion       : 0.02
% 8.86/3.01  Main loop            : 1.87
% 8.86/3.01  Inferencing          : 0.54
% 8.86/3.01  Reduction            : 0.68
% 8.86/3.01  Demodulation         : 0.51
% 8.86/3.01  BG Simplification    : 0.07
% 8.86/3.01  Subsumption          : 0.44
% 8.86/3.01  Abstraction          : 0.08
% 8.86/3.01  MUC search           : 0.00
% 8.86/3.01  Cooper               : 0.00
% 8.86/3.01  Total                : 2.27
% 8.86/3.01  Index Insertion      : 0.00
% 8.86/3.01  Index Deletion       : 0.00
% 8.86/3.01  Index Matching       : 0.00
% 8.86/3.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
