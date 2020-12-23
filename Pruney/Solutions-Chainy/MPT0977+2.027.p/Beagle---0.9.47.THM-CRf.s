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
% DateTime   : Thu Dec  3 10:11:49 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 109 expanded)
%              Number of leaves         :   36 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :  115 ( 172 expanded)
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

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r2_relset_1(A,B,k4_relset_1(A,A,A,B,k6_partfun1(A),C),C)
          & r2_relset_1(A,B,k4_relset_1(A,B,B,B,C,k6_partfun1(B)),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_2)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_90,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_76,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_12,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_629,plain,(
    ! [B_138,A_139] :
      ( v1_relat_1(B_138)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(A_139))
      | ~ v1_relat_1(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_638,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_629])).

tff(c_645,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_638])).

tff(c_660,plain,(
    ! [C_143,B_144,A_145] :
      ( v5_relat_1(C_143,B_144)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_145,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_673,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_660])).

tff(c_759,plain,(
    ! [A_168,B_169,D_170] :
      ( r2_relset_1(A_168,B_169,D_170,D_170)
      | ~ m1_subset_1(D_170,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_769,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_759])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_36,plain,(
    ! [A_34] : k6_relat_1(A_34) = k6_partfun1(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_16,plain,(
    ! [B_13,A_12] :
      ( k5_relat_1(B_13,k6_relat_1(A_12)) = B_13
      | ~ r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_732,plain,(
    ! [B_161,A_162] :
      ( k5_relat_1(B_161,k6_partfun1(A_162)) = B_161
      | ~ r1_tarski(k2_relat_1(B_161),A_162)
      | ~ v1_relat_1(B_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_16])).

tff(c_736,plain,(
    ! [B_7,A_6] :
      ( k5_relat_1(B_7,k6_partfun1(A_6)) = B_7
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_732])).

tff(c_34,plain,(
    ! [A_33] : m1_subset_1(k6_partfun1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1234,plain,(
    ! [F_236,D_239,B_238,C_235,A_240,E_237] :
      ( k4_relset_1(A_240,B_238,C_235,D_239,E_237,F_236) = k5_relat_1(E_237,F_236)
      | ~ m1_subset_1(F_236,k1_zfmisc_1(k2_zfmisc_1(C_235,D_239)))
      | ~ m1_subset_1(E_237,k1_zfmisc_1(k2_zfmisc_1(A_240,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1736,plain,(
    ! [A_303,B_304,A_305,E_306] :
      ( k4_relset_1(A_303,B_304,A_305,A_305,E_306,k6_partfun1(A_305)) = k5_relat_1(E_306,k6_partfun1(A_305))
      | ~ m1_subset_1(E_306,k1_zfmisc_1(k2_zfmisc_1(A_303,B_304))) ) ),
    inference(resolution,[status(thm)],[c_34,c_1234])).

tff(c_1758,plain,(
    ! [A_305] : k4_relset_1('#skF_1','#skF_2',A_305,A_305,'#skF_3',k6_partfun1(A_305)) = k5_relat_1('#skF_3',k6_partfun1(A_305)) ),
    inference(resolution,[status(thm)],[c_40,c_1736])).

tff(c_174,plain,(
    ! [A_68,B_69,D_70] :
      ( r2_relset_1(A_68,B_69,D_70,D_70)
      | ~ m1_subset_1(D_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_184,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_174])).

tff(c_71,plain,(
    ! [B_45,A_46] :
      ( v1_relat_1(B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_46))
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_80,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_71])).

tff(c_87,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_80])).

tff(c_199,plain,(
    ! [A_75,B_76,C_77] :
      ( k1_relset_1(A_75,B_76,C_77) = k1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_212,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_199])).

tff(c_254,plain,(
    ! [A_88,B_89,C_90] :
      ( m1_subset_1(k1_relset_1(A_88,B_89,C_90),k1_zfmisc_1(A_88))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_281,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_254])).

tff(c_291,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_281])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_299,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_291,c_2])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k5_relat_1(k6_relat_1(A_10),B_11) = B_11
      | ~ r1_tarski(k1_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_42,plain,(
    ! [A_10,B_11] :
      ( k5_relat_1(k6_partfun1(A_10),B_11) = B_11
      | ~ r1_tarski(k1_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_14])).

tff(c_302,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_299,c_42])).

tff(c_308,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_302])).

tff(c_381,plain,(
    ! [A_102,E_99,C_97,D_101,B_100,F_98] :
      ( k4_relset_1(A_102,B_100,C_97,D_101,E_99,F_98) = k5_relat_1(E_99,F_98)
      | ~ m1_subset_1(F_98,k1_zfmisc_1(k2_zfmisc_1(C_97,D_101)))
      | ~ m1_subset_1(E_99,k1_zfmisc_1(k2_zfmisc_1(A_102,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_462,plain,(
    ! [A_115,B_116,E_117] :
      ( k4_relset_1(A_115,B_116,'#skF_1','#skF_2',E_117,'#skF_3') = k5_relat_1(E_117,'#skF_3')
      | ~ m1_subset_1(E_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(resolution,[status(thm)],[c_40,c_381])).

tff(c_483,plain,(
    ! [A_33] : k4_relset_1(A_33,A_33,'#skF_1','#skF_2',k6_partfun1(A_33),'#skF_3') = k5_relat_1(k6_partfun1(A_33),'#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_462])).

tff(c_38,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_70,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_623,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_70])).

tff(c_626,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_308,c_623])).

tff(c_627,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1759,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1758,c_627])).

tff(c_1771,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_736,c_1759])).

tff(c_1774,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_645,c_673,c_769,c_1771])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:36:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.57/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.67  
% 3.57/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.67  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.57/1.67  
% 3.57/1.67  %Foreground sorts:
% 3.57/1.67  
% 3.57/1.67  
% 3.57/1.67  %Background operators:
% 3.57/1.67  
% 3.57/1.67  
% 3.57/1.67  %Foreground operators:
% 3.57/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.57/1.67  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.57/1.67  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.57/1.67  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.57/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.57/1.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.57/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.57/1.67  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.57/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.57/1.67  tff('#skF_1', type, '#skF_1': $i).
% 3.57/1.67  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.57/1.67  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.57/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.57/1.67  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.57/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.57/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.57/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.57/1.67  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.57/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.57/1.67  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.57/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.57/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.57/1.67  
% 3.79/1.69  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.79/1.69  tff(f_97, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_2)).
% 3.79/1.69  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.79/1.69  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.79/1.69  tff(f_84, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.79/1.69  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.79/1.69  tff(f_90, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.79/1.69  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 3.79/1.69  tff(f_88, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 3.79/1.69  tff(f_76, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 3.79/1.69  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.79/1.69  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.79/1.69  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.79/1.69  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 3.79/1.69  tff(c_12, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.79/1.69  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.79/1.69  tff(c_629, plain, (![B_138, A_139]: (v1_relat_1(B_138) | ~m1_subset_1(B_138, k1_zfmisc_1(A_139)) | ~v1_relat_1(A_139))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.79/1.69  tff(c_638, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_629])).
% 3.79/1.69  tff(c_645, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_638])).
% 3.79/1.69  tff(c_660, plain, (![C_143, B_144, A_145]: (v5_relat_1(C_143, B_144) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_145, B_144))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.79/1.69  tff(c_673, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_660])).
% 3.79/1.69  tff(c_759, plain, (![A_168, B_169, D_170]: (r2_relset_1(A_168, B_169, D_170, D_170) | ~m1_subset_1(D_170, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.79/1.69  tff(c_769, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_759])).
% 3.79/1.69  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.79/1.69  tff(c_36, plain, (![A_34]: (k6_relat_1(A_34)=k6_partfun1(A_34))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.79/1.69  tff(c_16, plain, (![B_13, A_12]: (k5_relat_1(B_13, k6_relat_1(A_12))=B_13 | ~r1_tarski(k2_relat_1(B_13), A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.79/1.69  tff(c_732, plain, (![B_161, A_162]: (k5_relat_1(B_161, k6_partfun1(A_162))=B_161 | ~r1_tarski(k2_relat_1(B_161), A_162) | ~v1_relat_1(B_161))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_16])).
% 3.79/1.69  tff(c_736, plain, (![B_7, A_6]: (k5_relat_1(B_7, k6_partfun1(A_6))=B_7 | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_10, c_732])).
% 3.79/1.69  tff(c_34, plain, (![A_33]: (m1_subset_1(k6_partfun1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.79/1.69  tff(c_1234, plain, (![F_236, D_239, B_238, C_235, A_240, E_237]: (k4_relset_1(A_240, B_238, C_235, D_239, E_237, F_236)=k5_relat_1(E_237, F_236) | ~m1_subset_1(F_236, k1_zfmisc_1(k2_zfmisc_1(C_235, D_239))) | ~m1_subset_1(E_237, k1_zfmisc_1(k2_zfmisc_1(A_240, B_238))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.79/1.69  tff(c_1736, plain, (![A_303, B_304, A_305, E_306]: (k4_relset_1(A_303, B_304, A_305, A_305, E_306, k6_partfun1(A_305))=k5_relat_1(E_306, k6_partfun1(A_305)) | ~m1_subset_1(E_306, k1_zfmisc_1(k2_zfmisc_1(A_303, B_304))))), inference(resolution, [status(thm)], [c_34, c_1234])).
% 3.79/1.69  tff(c_1758, plain, (![A_305]: (k4_relset_1('#skF_1', '#skF_2', A_305, A_305, '#skF_3', k6_partfun1(A_305))=k5_relat_1('#skF_3', k6_partfun1(A_305)))), inference(resolution, [status(thm)], [c_40, c_1736])).
% 3.79/1.69  tff(c_174, plain, (![A_68, B_69, D_70]: (r2_relset_1(A_68, B_69, D_70, D_70) | ~m1_subset_1(D_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.79/1.69  tff(c_184, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_174])).
% 3.79/1.69  tff(c_71, plain, (![B_45, A_46]: (v1_relat_1(B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(A_46)) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.79/1.69  tff(c_80, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_71])).
% 3.79/1.69  tff(c_87, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_80])).
% 3.79/1.69  tff(c_199, plain, (![A_75, B_76, C_77]: (k1_relset_1(A_75, B_76, C_77)=k1_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.79/1.69  tff(c_212, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_199])).
% 3.79/1.69  tff(c_254, plain, (![A_88, B_89, C_90]: (m1_subset_1(k1_relset_1(A_88, B_89, C_90), k1_zfmisc_1(A_88)) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.79/1.69  tff(c_281, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_212, c_254])).
% 3.79/1.69  tff(c_291, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_281])).
% 3.79/1.69  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.79/1.69  tff(c_299, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_291, c_2])).
% 3.79/1.69  tff(c_14, plain, (![A_10, B_11]: (k5_relat_1(k6_relat_1(A_10), B_11)=B_11 | ~r1_tarski(k1_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.79/1.69  tff(c_42, plain, (![A_10, B_11]: (k5_relat_1(k6_partfun1(A_10), B_11)=B_11 | ~r1_tarski(k1_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_14])).
% 3.79/1.69  tff(c_302, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_299, c_42])).
% 3.79/1.69  tff(c_308, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_87, c_302])).
% 3.79/1.69  tff(c_381, plain, (![A_102, E_99, C_97, D_101, B_100, F_98]: (k4_relset_1(A_102, B_100, C_97, D_101, E_99, F_98)=k5_relat_1(E_99, F_98) | ~m1_subset_1(F_98, k1_zfmisc_1(k2_zfmisc_1(C_97, D_101))) | ~m1_subset_1(E_99, k1_zfmisc_1(k2_zfmisc_1(A_102, B_100))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.79/1.69  tff(c_462, plain, (![A_115, B_116, E_117]: (k4_relset_1(A_115, B_116, '#skF_1', '#skF_2', E_117, '#skF_3')=k5_relat_1(E_117, '#skF_3') | ~m1_subset_1(E_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(resolution, [status(thm)], [c_40, c_381])).
% 3.79/1.69  tff(c_483, plain, (![A_33]: (k4_relset_1(A_33, A_33, '#skF_1', '#skF_2', k6_partfun1(A_33), '#skF_3')=k5_relat_1(k6_partfun1(A_33), '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_462])).
% 3.79/1.69  tff(c_38, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.79/1.69  tff(c_70, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_38])).
% 3.79/1.69  tff(c_623, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_483, c_70])).
% 3.79/1.69  tff(c_626, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_184, c_308, c_623])).
% 3.79/1.69  tff(c_627, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_38])).
% 3.79/1.69  tff(c_1759, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1758, c_627])).
% 3.79/1.69  tff(c_1771, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3') | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_736, c_1759])).
% 3.79/1.69  tff(c_1774, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_645, c_673, c_769, c_1771])).
% 3.79/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/1.69  
% 3.79/1.69  Inference rules
% 3.79/1.69  ----------------------
% 3.79/1.69  #Ref     : 0
% 3.79/1.69  #Sup     : 355
% 3.79/1.69  #Fact    : 0
% 3.79/1.69  #Define  : 0
% 3.79/1.69  #Split   : 6
% 3.79/1.69  #Chain   : 0
% 3.79/1.69  #Close   : 0
% 3.79/1.69  
% 3.79/1.69  Ordering : KBO
% 3.79/1.69  
% 3.79/1.69  Simplification rules
% 3.79/1.69  ----------------------
% 3.79/1.69  #Subsume      : 24
% 3.79/1.69  #Demod        : 147
% 3.79/1.69  #Tautology    : 116
% 3.79/1.69  #SimpNegUnit  : 0
% 3.79/1.69  #BackRed      : 6
% 3.79/1.69  
% 3.79/1.69  #Partial instantiations: 0
% 3.79/1.69  #Strategies tried      : 1
% 3.79/1.69  
% 3.79/1.69  Timing (in seconds)
% 3.79/1.69  ----------------------
% 3.79/1.69  Preprocessing        : 0.34
% 3.79/1.69  Parsing              : 0.19
% 3.79/1.69  CNF conversion       : 0.02
% 3.79/1.69  Main loop            : 0.54
% 3.79/1.69  Inferencing          : 0.20
% 3.79/1.69  Reduction            : 0.17
% 3.79/1.69  Demodulation         : 0.12
% 3.79/1.69  BG Simplification    : 0.03
% 3.79/1.69  Subsumption          : 0.08
% 3.79/1.69  Abstraction          : 0.03
% 3.79/1.69  MUC search           : 0.00
% 3.79/1.69  Cooper               : 0.00
% 3.79/1.69  Total                : 0.91
% 3.79/1.69  Index Insertion      : 0.00
% 3.79/1.69  Index Deletion       : 0.00
% 3.79/1.69  Index Matching       : 0.00
% 3.79/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
