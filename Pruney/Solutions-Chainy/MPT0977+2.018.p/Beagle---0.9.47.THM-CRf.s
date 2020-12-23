%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:47 EST 2020

% Result     : Theorem 3.66s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 109 expanded)
%              Number of leaves         :   35 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :   99 ( 165 expanded)
%              Number of equality atoms :   25 (  29 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r2_relset_1(A,B,k4_relset_1(A,A,A,B,k6_partfun1(A),C),C)
          & r2_relset_1(A,B,k4_relset_1(A,B,B,B,C,k6_partfun1(B)),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_2)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_83,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_69,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_665,plain,(
    ! [A_146,B_147,D_148] :
      ( r2_relset_1(A_146,B_147,D_148,D_148)
      | ~ m1_subset_1(D_148,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_675,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_665])).

tff(c_65,plain,(
    ! [C_41,A_42,B_43] :
      ( v1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_78,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_65])).

tff(c_677,plain,(
    ! [A_150,B_151,C_152] :
      ( k2_relset_1(A_150,B_151,C_152) = k2_relat_1(C_152)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_690,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_677])).

tff(c_724,plain,(
    ! [A_160,B_161,C_162] :
      ( m1_subset_1(k2_relset_1(A_160,B_161,C_162),k1_zfmisc_1(B_161))
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_752,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_690,c_724])).

tff(c_762,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_752])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_784,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_762,c_2])).

tff(c_32,plain,(
    ! [A_32] : k6_relat_1(A_32) = k6_partfun1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( k5_relat_1(B_6,k6_relat_1(A_5)) = B_6
      | ~ r1_tarski(k2_relat_1(B_6),A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_38,plain,(
    ! [B_6,A_5] :
      ( k5_relat_1(B_6,k6_partfun1(A_5)) = B_6
      | ~ r1_tarski(k2_relat_1(B_6),A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_8])).

tff(c_787,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_784,c_38])).

tff(c_790,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_787])).

tff(c_30,plain,(
    ! [A_31] : m1_subset_1(k6_partfun1(A_31),k1_zfmisc_1(k2_zfmisc_1(A_31,A_31))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1127,plain,(
    ! [E_205,B_204,A_200,F_203,D_201,C_202] :
      ( k4_relset_1(A_200,B_204,C_202,D_201,E_205,F_203) = k5_relat_1(E_205,F_203)
      | ~ m1_subset_1(F_203,k1_zfmisc_1(k2_zfmisc_1(C_202,D_201)))
      | ~ m1_subset_1(E_205,k1_zfmisc_1(k2_zfmisc_1(A_200,B_204))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1698,plain,(
    ! [A_296,B_297,A_298,E_299] :
      ( k4_relset_1(A_296,B_297,A_298,A_298,E_299,k6_partfun1(A_298)) = k5_relat_1(E_299,k6_partfun1(A_298))
      | ~ m1_subset_1(E_299,k1_zfmisc_1(k2_zfmisc_1(A_296,B_297))) ) ),
    inference(resolution,[status(thm)],[c_30,c_1127])).

tff(c_1720,plain,(
    ! [A_298] : k4_relset_1('#skF_1','#skF_2',A_298,A_298,'#skF_3',k6_partfun1(A_298)) = k5_relat_1('#skF_3',k6_partfun1(A_298)) ),
    inference(resolution,[status(thm)],[c_36,c_1698])).

tff(c_179,plain,(
    ! [A_67,B_68,D_69] :
      ( r2_relset_1(A_67,B_68,D_69,D_69)
      | ~ m1_subset_1(D_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_189,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_179])).

tff(c_119,plain,(
    ! [C_57,A_58,B_59] :
      ( v4_relat_1(C_57,A_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_132,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_119])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k7_relat_1(B_4,A_3) = B_4
      | ~ v4_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_135,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_132,c_6])).

tff(c_138,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_135])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( k5_relat_1(k6_relat_1(A_7),B_8) = k7_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_37,plain,(
    ! [A_7,B_8] :
      ( k5_relat_1(k6_partfun1(A_7),B_8) = k7_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_10])).

tff(c_368,plain,(
    ! [A_96,D_97,B_100,E_101,C_98,F_99] :
      ( k4_relset_1(A_96,B_100,C_98,D_97,E_101,F_99) = k5_relat_1(E_101,F_99)
      | ~ m1_subset_1(F_99,k1_zfmisc_1(k2_zfmisc_1(C_98,D_97)))
      | ~ m1_subset_1(E_101,k1_zfmisc_1(k2_zfmisc_1(A_96,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_415,plain,(
    ! [A_105,B_106,E_107] :
      ( k4_relset_1(A_105,B_106,'#skF_1','#skF_2',E_107,'#skF_3') = k5_relat_1(E_107,'#skF_3')
      | ~ m1_subset_1(E_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(resolution,[status(thm)],[c_36,c_368])).

tff(c_436,plain,(
    ! [A_31] : k4_relset_1(A_31,A_31,'#skF_1','#skF_2',k6_partfun1(A_31),'#skF_3') = k5_relat_1(k6_partfun1(A_31),'#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_415])).

tff(c_34,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_79,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_547,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_79])).

tff(c_559,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_547])).

tff(c_562,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_189,c_138,c_559])).

tff(c_563,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1721,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1720,c_563])).

tff(c_1724,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_675,c_790,c_1721])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:55:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.66/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.63  
% 3.66/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.63  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.66/1.63  
% 3.66/1.63  %Foreground sorts:
% 3.66/1.63  
% 3.66/1.63  
% 3.66/1.63  %Background operators:
% 3.66/1.63  
% 3.66/1.63  
% 3.66/1.63  %Foreground operators:
% 3.66/1.63  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.66/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.66/1.63  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.66/1.63  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.66/1.63  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.66/1.63  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.66/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.66/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.66/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.66/1.63  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.66/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.66/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.66/1.63  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.66/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.66/1.63  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.66/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.66/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.66/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.66/1.63  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.66/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.66/1.63  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.66/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.66/1.63  
% 3.66/1.65  tff(f_90, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_2)).
% 3.66/1.65  tff(f_77, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.66/1.65  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.66/1.65  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.66/1.65  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.66/1.65  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.66/1.65  tff(f_83, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.66/1.65  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 3.66/1.65  tff(f_81, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 3.66/1.65  tff(f_69, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 3.66/1.65  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.66/1.65  tff(f_35, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.66/1.65  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 3.66/1.65  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.66/1.65  tff(c_665, plain, (![A_146, B_147, D_148]: (r2_relset_1(A_146, B_147, D_148, D_148) | ~m1_subset_1(D_148, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.66/1.65  tff(c_675, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_665])).
% 3.66/1.65  tff(c_65, plain, (![C_41, A_42, B_43]: (v1_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.66/1.65  tff(c_78, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_65])).
% 3.66/1.65  tff(c_677, plain, (![A_150, B_151, C_152]: (k2_relset_1(A_150, B_151, C_152)=k2_relat_1(C_152) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.66/1.65  tff(c_690, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_677])).
% 3.66/1.65  tff(c_724, plain, (![A_160, B_161, C_162]: (m1_subset_1(k2_relset_1(A_160, B_161, C_162), k1_zfmisc_1(B_161)) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.66/1.65  tff(c_752, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_690, c_724])).
% 3.66/1.65  tff(c_762, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_752])).
% 3.66/1.65  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.66/1.65  tff(c_784, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_762, c_2])).
% 3.66/1.65  tff(c_32, plain, (![A_32]: (k6_relat_1(A_32)=k6_partfun1(A_32))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.66/1.65  tff(c_8, plain, (![B_6, A_5]: (k5_relat_1(B_6, k6_relat_1(A_5))=B_6 | ~r1_tarski(k2_relat_1(B_6), A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.66/1.65  tff(c_38, plain, (![B_6, A_5]: (k5_relat_1(B_6, k6_partfun1(A_5))=B_6 | ~r1_tarski(k2_relat_1(B_6), A_5) | ~v1_relat_1(B_6))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_8])).
% 3.66/1.65  tff(c_787, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_784, c_38])).
% 3.66/1.65  tff(c_790, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_787])).
% 3.66/1.65  tff(c_30, plain, (![A_31]: (m1_subset_1(k6_partfun1(A_31), k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.66/1.65  tff(c_1127, plain, (![E_205, B_204, A_200, F_203, D_201, C_202]: (k4_relset_1(A_200, B_204, C_202, D_201, E_205, F_203)=k5_relat_1(E_205, F_203) | ~m1_subset_1(F_203, k1_zfmisc_1(k2_zfmisc_1(C_202, D_201))) | ~m1_subset_1(E_205, k1_zfmisc_1(k2_zfmisc_1(A_200, B_204))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.66/1.65  tff(c_1698, plain, (![A_296, B_297, A_298, E_299]: (k4_relset_1(A_296, B_297, A_298, A_298, E_299, k6_partfun1(A_298))=k5_relat_1(E_299, k6_partfun1(A_298)) | ~m1_subset_1(E_299, k1_zfmisc_1(k2_zfmisc_1(A_296, B_297))))), inference(resolution, [status(thm)], [c_30, c_1127])).
% 3.66/1.65  tff(c_1720, plain, (![A_298]: (k4_relset_1('#skF_1', '#skF_2', A_298, A_298, '#skF_3', k6_partfun1(A_298))=k5_relat_1('#skF_3', k6_partfun1(A_298)))), inference(resolution, [status(thm)], [c_36, c_1698])).
% 3.66/1.65  tff(c_179, plain, (![A_67, B_68, D_69]: (r2_relset_1(A_67, B_68, D_69, D_69) | ~m1_subset_1(D_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.66/1.65  tff(c_189, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_179])).
% 3.66/1.65  tff(c_119, plain, (![C_57, A_58, B_59]: (v4_relat_1(C_57, A_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.66/1.65  tff(c_132, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_36, c_119])).
% 3.66/1.65  tff(c_6, plain, (![B_4, A_3]: (k7_relat_1(B_4, A_3)=B_4 | ~v4_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.66/1.65  tff(c_135, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_132, c_6])).
% 3.66/1.65  tff(c_138, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_135])).
% 3.66/1.65  tff(c_10, plain, (![A_7, B_8]: (k5_relat_1(k6_relat_1(A_7), B_8)=k7_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.66/1.65  tff(c_37, plain, (![A_7, B_8]: (k5_relat_1(k6_partfun1(A_7), B_8)=k7_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_10])).
% 3.66/1.65  tff(c_368, plain, (![A_96, D_97, B_100, E_101, C_98, F_99]: (k4_relset_1(A_96, B_100, C_98, D_97, E_101, F_99)=k5_relat_1(E_101, F_99) | ~m1_subset_1(F_99, k1_zfmisc_1(k2_zfmisc_1(C_98, D_97))) | ~m1_subset_1(E_101, k1_zfmisc_1(k2_zfmisc_1(A_96, B_100))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.66/1.65  tff(c_415, plain, (![A_105, B_106, E_107]: (k4_relset_1(A_105, B_106, '#skF_1', '#skF_2', E_107, '#skF_3')=k5_relat_1(E_107, '#skF_3') | ~m1_subset_1(E_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(resolution, [status(thm)], [c_36, c_368])).
% 3.66/1.65  tff(c_436, plain, (![A_31]: (k4_relset_1(A_31, A_31, '#skF_1', '#skF_2', k6_partfun1(A_31), '#skF_3')=k5_relat_1(k6_partfun1(A_31), '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_415])).
% 3.66/1.65  tff(c_34, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.66/1.65  tff(c_79, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_34])).
% 3.66/1.65  tff(c_547, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_436, c_79])).
% 3.66/1.65  tff(c_559, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_37, c_547])).
% 3.66/1.65  tff(c_562, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_189, c_138, c_559])).
% 3.66/1.65  tff(c_563, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_34])).
% 3.66/1.65  tff(c_1721, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1720, c_563])).
% 3.66/1.65  tff(c_1724, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_675, c_790, c_1721])).
% 3.66/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.65  
% 3.66/1.65  Inference rules
% 3.66/1.65  ----------------------
% 3.66/1.65  #Ref     : 0
% 3.66/1.65  #Sup     : 346
% 3.66/1.65  #Fact    : 0
% 3.66/1.65  #Define  : 0
% 3.66/1.65  #Split   : 2
% 3.66/1.65  #Chain   : 0
% 3.66/1.65  #Close   : 0
% 3.66/1.65  
% 3.66/1.65  Ordering : KBO
% 3.66/1.65  
% 3.66/1.65  Simplification rules
% 3.66/1.65  ----------------------
% 3.66/1.65  #Subsume      : 3
% 3.66/1.65  #Demod        : 167
% 3.66/1.65  #Tautology    : 146
% 3.66/1.65  #SimpNegUnit  : 0
% 3.66/1.65  #BackRed      : 7
% 3.66/1.65  
% 3.66/1.65  #Partial instantiations: 0
% 3.66/1.65  #Strategies tried      : 1
% 3.66/1.65  
% 3.66/1.65  Timing (in seconds)
% 3.66/1.65  ----------------------
% 3.66/1.65  Preprocessing        : 0.33
% 3.66/1.65  Parsing              : 0.18
% 3.66/1.65  CNF conversion       : 0.02
% 3.66/1.65  Main loop            : 0.54
% 3.66/1.65  Inferencing          : 0.21
% 3.66/1.65  Reduction            : 0.17
% 3.66/1.65  Demodulation         : 0.13
% 3.66/1.65  BG Simplification    : 0.03
% 3.66/1.65  Subsumption          : 0.08
% 3.66/1.65  Abstraction          : 0.03
% 3.66/1.65  MUC search           : 0.00
% 3.66/1.65  Cooper               : 0.00
% 3.66/1.65  Total                : 0.91
% 3.66/1.65  Index Insertion      : 0.00
% 3.66/1.65  Index Deletion       : 0.00
% 3.66/1.65  Index Matching       : 0.00
% 3.66/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
