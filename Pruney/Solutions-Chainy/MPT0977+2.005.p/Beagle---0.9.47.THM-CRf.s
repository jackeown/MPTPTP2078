%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:46 EST 2020

% Result     : Theorem 3.96s
% Output     : CNFRefutation 4.27s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 103 expanded)
%              Number of leaves         :   35 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :  103 ( 160 expanded)
%              Number of equality atoms :   22 (  26 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r2_relset_1(A,B,k4_relset_1(A,A,A,B,k6_partfun1(A),C),C)
          & r2_relset_1(A,B,k4_relset_1(A,B,B,B,C,k6_partfun1(B)),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_2)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_85,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_71,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_67,plain,(
    ! [C_41,A_42,B_43] :
      ( v1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_80,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_67])).

tff(c_684,plain,(
    ! [C_160,B_161,A_162] :
      ( v5_relat_1(C_160,B_161)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_162,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_697,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_684])).

tff(c_766,plain,(
    ! [A_183,B_184,D_185] :
      ( r2_relset_1(A_183,B_184,D_185,D_185)
      | ~ m1_subset_1(D_185,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_776,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_766])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34,plain,(
    ! [A_32] : k6_relat_1(A_32) = k6_partfun1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( k5_relat_1(B_8,k6_relat_1(A_7)) = B_8
      | ~ r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_792,plain,(
    ! [B_192,A_193] :
      ( k5_relat_1(B_192,k6_partfun1(A_193)) = B_192
      | ~ r1_tarski(k2_relat_1(B_192),A_193)
      | ~ v1_relat_1(B_192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_12])).

tff(c_796,plain,(
    ! [B_4,A_3] :
      ( k5_relat_1(B_4,k6_partfun1(A_3)) = B_4
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_792])).

tff(c_32,plain,(
    ! [A_31] : m1_subset_1(k6_partfun1(A_31),k1_zfmisc_1(k2_zfmisc_1(A_31,A_31))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1311,plain,(
    ! [A_279,F_282,C_281,D_280,B_283,E_284] :
      ( k4_relset_1(A_279,B_283,C_281,D_280,E_284,F_282) = k5_relat_1(E_284,F_282)
      | ~ m1_subset_1(F_282,k1_zfmisc_1(k2_zfmisc_1(C_281,D_280)))
      | ~ m1_subset_1(E_284,k1_zfmisc_1(k2_zfmisc_1(A_279,B_283))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2062,plain,(
    ! [A_417,B_418,A_419,E_420] :
      ( k4_relset_1(A_417,B_418,A_419,A_419,E_420,k6_partfun1(A_419)) = k5_relat_1(E_420,k6_partfun1(A_419))
      | ~ m1_subset_1(E_420,k1_zfmisc_1(k2_zfmisc_1(A_417,B_418))) ) ),
    inference(resolution,[status(thm)],[c_32,c_1311])).

tff(c_2084,plain,(
    ! [A_419] : k4_relset_1('#skF_1','#skF_2',A_419,A_419,'#skF_3',k6_partfun1(A_419)) = k5_relat_1('#skF_3',k6_partfun1(A_419)) ),
    inference(resolution,[status(thm)],[c_38,c_2062])).

tff(c_175,plain,(
    ! [A_69,B_70,D_71] :
      ( r2_relset_1(A_69,B_70,D_71,D_71)
      | ~ m1_subset_1(D_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_185,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_175])).

tff(c_188,plain,(
    ! [A_75,B_76,C_77] :
      ( k1_relset_1(A_75,B_76,C_77) = k1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_201,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_188])).

tff(c_280,plain,(
    ! [A_96,B_97,C_98] :
      ( m1_subset_1(k1_relset_1(A_96,B_97,C_98),k1_zfmisc_1(A_96))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_308,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_280])).

tff(c_318,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_308])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_322,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_318,c_2])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k5_relat_1(k6_relat_1(A_5),B_6) = B_6
      | ~ r1_tarski(k1_relat_1(B_6),A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_40,plain,(
    ! [A_5,B_6] :
      ( k5_relat_1(k6_partfun1(A_5),B_6) = B_6
      | ~ r1_tarski(k1_relat_1(B_6),A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_10])).

tff(c_325,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_322,c_40])).

tff(c_328,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_325])).

tff(c_409,plain,(
    ! [F_112,A_109,C_111,B_113,D_110,E_114] :
      ( k4_relset_1(A_109,B_113,C_111,D_110,E_114,F_112) = k5_relat_1(E_114,F_112)
      | ~ m1_subset_1(F_112,k1_zfmisc_1(k2_zfmisc_1(C_111,D_110)))
      | ~ m1_subset_1(E_114,k1_zfmisc_1(k2_zfmisc_1(A_109,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_528,plain,(
    ! [A_132,B_133,E_134] :
      ( k4_relset_1(A_132,B_133,'#skF_1','#skF_2',E_134,'#skF_3') = k5_relat_1(E_134,'#skF_3')
      | ~ m1_subset_1(E_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(resolution,[status(thm)],[c_38,c_409])).

tff(c_549,plain,(
    ! [A_31] : k4_relset_1(A_31,A_31,'#skF_1','#skF_2',k6_partfun1(A_31),'#skF_3') = k5_relat_1(k6_partfun1(A_31),'#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_528])).

tff(c_36,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_81,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_666,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_81])).

tff(c_669,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_328,c_666])).

tff(c_670,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_2085,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2084,c_670])).

tff(c_2097,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_796,c_2085])).

tff(c_2100,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_697,c_776,c_2097])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:48:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.96/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.74  
% 3.96/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.75  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.96/1.75  
% 3.96/1.75  %Foreground sorts:
% 3.96/1.75  
% 3.96/1.75  
% 3.96/1.75  %Background operators:
% 3.96/1.75  
% 3.96/1.75  
% 3.96/1.75  %Foreground operators:
% 3.96/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.96/1.75  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.96/1.75  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.96/1.75  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.96/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.96/1.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.96/1.75  tff('#skF_2', type, '#skF_2': $i).
% 3.96/1.75  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.96/1.75  tff('#skF_3', type, '#skF_3': $i).
% 3.96/1.75  tff('#skF_1', type, '#skF_1': $i).
% 3.96/1.75  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.96/1.75  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.96/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.96/1.75  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.96/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.96/1.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.96/1.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.96/1.75  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.96/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.96/1.75  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.96/1.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.96/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.96/1.75  
% 4.27/1.77  tff(f_92, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_2)).
% 4.27/1.77  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.27/1.77  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.27/1.77  tff(f_79, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.27/1.77  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 4.27/1.77  tff(f_85, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.27/1.77  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 4.27/1.77  tff(f_83, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.27/1.77  tff(f_71, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 4.27/1.77  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.27/1.77  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 4.27/1.77  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.27/1.77  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 4.27/1.77  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.27/1.77  tff(c_67, plain, (![C_41, A_42, B_43]: (v1_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.27/1.77  tff(c_80, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_67])).
% 4.27/1.77  tff(c_684, plain, (![C_160, B_161, A_162]: (v5_relat_1(C_160, B_161) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_162, B_161))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.27/1.77  tff(c_697, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_684])).
% 4.27/1.77  tff(c_766, plain, (![A_183, B_184, D_185]: (r2_relset_1(A_183, B_184, D_185, D_185) | ~m1_subset_1(D_185, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.27/1.77  tff(c_776, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_766])).
% 4.27/1.77  tff(c_8, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.27/1.77  tff(c_34, plain, (![A_32]: (k6_relat_1(A_32)=k6_partfun1(A_32))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.27/1.77  tff(c_12, plain, (![B_8, A_7]: (k5_relat_1(B_8, k6_relat_1(A_7))=B_8 | ~r1_tarski(k2_relat_1(B_8), A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.27/1.77  tff(c_792, plain, (![B_192, A_193]: (k5_relat_1(B_192, k6_partfun1(A_193))=B_192 | ~r1_tarski(k2_relat_1(B_192), A_193) | ~v1_relat_1(B_192))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_12])).
% 4.27/1.77  tff(c_796, plain, (![B_4, A_3]: (k5_relat_1(B_4, k6_partfun1(A_3))=B_4 | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(resolution, [status(thm)], [c_8, c_792])).
% 4.27/1.77  tff(c_32, plain, (![A_31]: (m1_subset_1(k6_partfun1(A_31), k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.27/1.77  tff(c_1311, plain, (![A_279, F_282, C_281, D_280, B_283, E_284]: (k4_relset_1(A_279, B_283, C_281, D_280, E_284, F_282)=k5_relat_1(E_284, F_282) | ~m1_subset_1(F_282, k1_zfmisc_1(k2_zfmisc_1(C_281, D_280))) | ~m1_subset_1(E_284, k1_zfmisc_1(k2_zfmisc_1(A_279, B_283))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.27/1.77  tff(c_2062, plain, (![A_417, B_418, A_419, E_420]: (k4_relset_1(A_417, B_418, A_419, A_419, E_420, k6_partfun1(A_419))=k5_relat_1(E_420, k6_partfun1(A_419)) | ~m1_subset_1(E_420, k1_zfmisc_1(k2_zfmisc_1(A_417, B_418))))), inference(resolution, [status(thm)], [c_32, c_1311])).
% 4.27/1.77  tff(c_2084, plain, (![A_419]: (k4_relset_1('#skF_1', '#skF_2', A_419, A_419, '#skF_3', k6_partfun1(A_419))=k5_relat_1('#skF_3', k6_partfun1(A_419)))), inference(resolution, [status(thm)], [c_38, c_2062])).
% 4.27/1.77  tff(c_175, plain, (![A_69, B_70, D_71]: (r2_relset_1(A_69, B_70, D_71, D_71) | ~m1_subset_1(D_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.27/1.77  tff(c_185, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_175])).
% 4.27/1.77  tff(c_188, plain, (![A_75, B_76, C_77]: (k1_relset_1(A_75, B_76, C_77)=k1_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.27/1.77  tff(c_201, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_188])).
% 4.27/1.77  tff(c_280, plain, (![A_96, B_97, C_98]: (m1_subset_1(k1_relset_1(A_96, B_97, C_98), k1_zfmisc_1(A_96)) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.27/1.77  tff(c_308, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_201, c_280])).
% 4.27/1.77  tff(c_318, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_308])).
% 4.27/1.77  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.27/1.77  tff(c_322, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_318, c_2])).
% 4.27/1.77  tff(c_10, plain, (![A_5, B_6]: (k5_relat_1(k6_relat_1(A_5), B_6)=B_6 | ~r1_tarski(k1_relat_1(B_6), A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.27/1.77  tff(c_40, plain, (![A_5, B_6]: (k5_relat_1(k6_partfun1(A_5), B_6)=B_6 | ~r1_tarski(k1_relat_1(B_6), A_5) | ~v1_relat_1(B_6))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_10])).
% 4.27/1.77  tff(c_325, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_322, c_40])).
% 4.27/1.77  tff(c_328, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_325])).
% 4.27/1.77  tff(c_409, plain, (![F_112, A_109, C_111, B_113, D_110, E_114]: (k4_relset_1(A_109, B_113, C_111, D_110, E_114, F_112)=k5_relat_1(E_114, F_112) | ~m1_subset_1(F_112, k1_zfmisc_1(k2_zfmisc_1(C_111, D_110))) | ~m1_subset_1(E_114, k1_zfmisc_1(k2_zfmisc_1(A_109, B_113))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.27/1.77  tff(c_528, plain, (![A_132, B_133, E_134]: (k4_relset_1(A_132, B_133, '#skF_1', '#skF_2', E_134, '#skF_3')=k5_relat_1(E_134, '#skF_3') | ~m1_subset_1(E_134, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))))), inference(resolution, [status(thm)], [c_38, c_409])).
% 4.27/1.77  tff(c_549, plain, (![A_31]: (k4_relset_1(A_31, A_31, '#skF_1', '#skF_2', k6_partfun1(A_31), '#skF_3')=k5_relat_1(k6_partfun1(A_31), '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_528])).
% 4.27/1.77  tff(c_36, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.27/1.77  tff(c_81, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_36])).
% 4.27/1.77  tff(c_666, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_549, c_81])).
% 4.27/1.77  tff(c_669, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_185, c_328, c_666])).
% 4.27/1.77  tff(c_670, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_36])).
% 4.27/1.77  tff(c_2085, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2084, c_670])).
% 4.27/1.77  tff(c_2097, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3') | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_796, c_2085])).
% 4.27/1.77  tff(c_2100, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_697, c_776, c_2097])).
% 4.27/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.27/1.77  
% 4.27/1.77  Inference rules
% 4.27/1.77  ----------------------
% 4.27/1.77  #Ref     : 0
% 4.27/1.77  #Sup     : 390
% 4.27/1.77  #Fact    : 0
% 4.27/1.77  #Define  : 0
% 4.27/1.77  #Split   : 2
% 4.27/1.77  #Chain   : 0
% 4.27/1.77  #Close   : 0
% 4.27/1.77  
% 4.27/1.77  Ordering : KBO
% 4.27/1.77  
% 4.27/1.77  Simplification rules
% 4.27/1.77  ----------------------
% 4.27/1.77  #Subsume      : 1
% 4.27/1.77  #Demod        : 204
% 4.27/1.77  #Tautology    : 133
% 4.27/1.77  #SimpNegUnit  : 0
% 4.27/1.77  #BackRed      : 6
% 4.27/1.77  
% 4.27/1.77  #Partial instantiations: 0
% 4.27/1.77  #Strategies tried      : 1
% 4.27/1.77  
% 4.27/1.77  Timing (in seconds)
% 4.27/1.77  ----------------------
% 4.27/1.77  Preprocessing        : 0.33
% 4.27/1.77  Parsing              : 0.18
% 4.27/1.77  CNF conversion       : 0.02
% 4.27/1.77  Main loop            : 0.67
% 4.27/1.77  Inferencing          : 0.26
% 4.27/1.77  Reduction            : 0.21
% 4.27/1.77  Demodulation         : 0.16
% 4.27/1.77  BG Simplification    : 0.03
% 4.33/1.78  Subsumption          : 0.09
% 4.33/1.78  Abstraction          : 0.04
% 4.33/1.78  MUC search           : 0.00
% 4.33/1.78  Cooper               : 0.00
% 4.33/1.78  Total                : 1.04
% 4.33/1.78  Index Insertion      : 0.00
% 4.33/1.78  Index Deletion       : 0.00
% 4.33/1.78  Index Matching       : 0.00
% 4.33/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
