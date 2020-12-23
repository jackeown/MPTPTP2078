%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:46 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 101 expanded)
%              Number of leaves         :   32 (  49 expanded)
%              Depth                    :    6
%              Number of atoms          :   94 ( 159 expanded)
%              Number of equality atoms :   21 (  25 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_84,negated_conjecture,(
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

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_77,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_63,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_46,plain,(
    ! [C_30,A_31,B_32] :
      ( v1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_54,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_46])).

tff(c_210,plain,(
    ! [C_77,B_78,A_79] :
      ( v5_relat_1(C_77,B_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_218,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_210])).

tff(c_260,plain,(
    ! [A_88,B_89,D_90] :
      ( r2_relset_1(A_88,B_89,D_90,D_90)
      | ~ m1_subset_1(D_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_266,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_260])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ! [A_26] : k6_relat_1(A_26) = k6_partfun1(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( k5_relat_1(B_6,k6_relat_1(A_5)) = B_6
      | ~ r1_tarski(k2_relat_1(B_6),A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_267,plain,(
    ! [B_91,A_92] :
      ( k5_relat_1(B_91,k6_partfun1(A_92)) = B_91
      | ~ r1_tarski(k2_relat_1(B_91),A_92)
      | ~ v1_relat_1(B_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_8])).

tff(c_271,plain,(
    ! [B_2,A_1] :
      ( k5_relat_1(B_2,k6_partfun1(A_1)) = B_2
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_267])).

tff(c_26,plain,(
    ! [A_25] : m1_subset_1(k6_partfun1(A_25),k1_zfmisc_1(k2_zfmisc_1(A_25,A_25))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_318,plain,(
    ! [B_104,C_102,D_103,F_105,A_107,E_106] :
      ( k4_relset_1(A_107,B_104,C_102,D_103,E_106,F_105) = k5_relat_1(E_106,F_105)
      | ~ m1_subset_1(F_105,k1_zfmisc_1(k2_zfmisc_1(C_102,D_103)))
      | ~ m1_subset_1(E_106,k1_zfmisc_1(k2_zfmisc_1(A_107,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_387,plain,(
    ! [A_112,B_113,A_114,E_115] :
      ( k4_relset_1(A_112,B_113,A_114,A_114,E_115,k6_partfun1(A_114)) = k5_relat_1(E_115,k6_partfun1(A_114))
      | ~ m1_subset_1(E_115,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(resolution,[status(thm)],[c_26,c_318])).

tff(c_393,plain,(
    ! [A_114] : k4_relset_1('#skF_1','#skF_2',A_114,A_114,'#skF_3',k6_partfun1(A_114)) = k5_relat_1('#skF_3',k6_partfun1(A_114)) ),
    inference(resolution,[status(thm)],[c_32,c_387])).

tff(c_150,plain,(
    ! [A_57,B_58,D_59] :
      ( r2_relset_1(A_57,B_58,D_59,D_59)
      | ~ m1_subset_1(D_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_156,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_150])).

tff(c_78,plain,(
    ! [C_44,A_45,B_46] :
      ( v4_relat_1(C_44,A_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_86,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_78])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k7_relat_1(B_4,A_3) = B_4
      | ~ v4_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_94,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_6])).

tff(c_97,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_94])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( k5_relat_1(k6_relat_1(A_7),B_8) = k7_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_33,plain,(
    ! [A_7,B_8] :
      ( k5_relat_1(k6_partfun1(A_7),B_8) = k7_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_10])).

tff(c_171,plain,(
    ! [D_66,F_68,B_67,A_70,C_65,E_69] :
      ( k4_relset_1(A_70,B_67,C_65,D_66,E_69,F_68) = k5_relat_1(E_69,F_68)
      | ~ m1_subset_1(F_68,k1_zfmisc_1(k2_zfmisc_1(C_65,D_66)))
      | ~ m1_subset_1(E_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_178,plain,(
    ! [A_71,B_72,E_73] :
      ( k4_relset_1(A_71,B_72,'#skF_1','#skF_2',E_73,'#skF_3') = k5_relat_1(E_73,'#skF_3')
      | ~ m1_subset_1(E_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(resolution,[status(thm)],[c_32,c_171])).

tff(c_185,plain,(
    ! [A_25] : k4_relset_1(A_25,A_25,'#skF_1','#skF_2',k6_partfun1(A_25),'#skF_3') = k5_relat_1(k6_partfun1(A_25),'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_178])).

tff(c_30,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_66,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_191,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_66])).

tff(c_203,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_191])).

tff(c_206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_156,c_97,c_203])).

tff(c_207,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_394,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_207])).

tff(c_406,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_394])).

tff(c_409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_218,c_266,c_406])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:09:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.33  
% 2.38/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.33  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.38/1.33  
% 2.38/1.33  %Foreground sorts:
% 2.38/1.33  
% 2.38/1.33  
% 2.38/1.33  %Background operators:
% 2.38/1.33  
% 2.38/1.33  
% 2.38/1.33  %Foreground operators:
% 2.38/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.33  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.38/1.33  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.38/1.33  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.38/1.33  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.38/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.38/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.38/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.38/1.33  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.38/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.38/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.38/1.33  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.38/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.38/1.33  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.38/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.38/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.38/1.33  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.38/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.33  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.38/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.38/1.33  
% 2.38/1.35  tff(f_84, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_2)).
% 2.38/1.35  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.38/1.35  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.38/1.35  tff(f_71, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.38/1.35  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.38/1.35  tff(f_77, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.38/1.35  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 2.38/1.35  tff(f_75, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.38/1.35  tff(f_63, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.38/1.35  tff(f_37, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.38/1.35  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.38/1.35  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.38/1.35  tff(c_46, plain, (![C_30, A_31, B_32]: (v1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.38/1.35  tff(c_54, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_46])).
% 2.38/1.35  tff(c_210, plain, (![C_77, B_78, A_79]: (v5_relat_1(C_77, B_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_78))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.38/1.35  tff(c_218, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_210])).
% 2.38/1.35  tff(c_260, plain, (![A_88, B_89, D_90]: (r2_relset_1(A_88, B_89, D_90, D_90) | ~m1_subset_1(D_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.38/1.35  tff(c_266, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_260])).
% 2.38/1.35  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.38/1.35  tff(c_28, plain, (![A_26]: (k6_relat_1(A_26)=k6_partfun1(A_26))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.38/1.35  tff(c_8, plain, (![B_6, A_5]: (k5_relat_1(B_6, k6_relat_1(A_5))=B_6 | ~r1_tarski(k2_relat_1(B_6), A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.38/1.35  tff(c_267, plain, (![B_91, A_92]: (k5_relat_1(B_91, k6_partfun1(A_92))=B_91 | ~r1_tarski(k2_relat_1(B_91), A_92) | ~v1_relat_1(B_91))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_8])).
% 2.38/1.35  tff(c_271, plain, (![B_2, A_1]: (k5_relat_1(B_2, k6_partfun1(A_1))=B_2 | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_4, c_267])).
% 2.38/1.35  tff(c_26, plain, (![A_25]: (m1_subset_1(k6_partfun1(A_25), k1_zfmisc_1(k2_zfmisc_1(A_25, A_25))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.38/1.35  tff(c_318, plain, (![B_104, C_102, D_103, F_105, A_107, E_106]: (k4_relset_1(A_107, B_104, C_102, D_103, E_106, F_105)=k5_relat_1(E_106, F_105) | ~m1_subset_1(F_105, k1_zfmisc_1(k2_zfmisc_1(C_102, D_103))) | ~m1_subset_1(E_106, k1_zfmisc_1(k2_zfmisc_1(A_107, B_104))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.38/1.35  tff(c_387, plain, (![A_112, B_113, A_114, E_115]: (k4_relset_1(A_112, B_113, A_114, A_114, E_115, k6_partfun1(A_114))=k5_relat_1(E_115, k6_partfun1(A_114)) | ~m1_subset_1(E_115, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(resolution, [status(thm)], [c_26, c_318])).
% 2.38/1.35  tff(c_393, plain, (![A_114]: (k4_relset_1('#skF_1', '#skF_2', A_114, A_114, '#skF_3', k6_partfun1(A_114))=k5_relat_1('#skF_3', k6_partfun1(A_114)))), inference(resolution, [status(thm)], [c_32, c_387])).
% 2.38/1.35  tff(c_150, plain, (![A_57, B_58, D_59]: (r2_relset_1(A_57, B_58, D_59, D_59) | ~m1_subset_1(D_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.38/1.35  tff(c_156, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_150])).
% 2.38/1.35  tff(c_78, plain, (![C_44, A_45, B_46]: (v4_relat_1(C_44, A_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.38/1.35  tff(c_86, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_78])).
% 2.38/1.35  tff(c_6, plain, (![B_4, A_3]: (k7_relat_1(B_4, A_3)=B_4 | ~v4_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.38/1.35  tff(c_94, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_6])).
% 2.38/1.35  tff(c_97, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_94])).
% 2.38/1.35  tff(c_10, plain, (![A_7, B_8]: (k5_relat_1(k6_relat_1(A_7), B_8)=k7_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.38/1.35  tff(c_33, plain, (![A_7, B_8]: (k5_relat_1(k6_partfun1(A_7), B_8)=k7_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_10])).
% 2.38/1.35  tff(c_171, plain, (![D_66, F_68, B_67, A_70, C_65, E_69]: (k4_relset_1(A_70, B_67, C_65, D_66, E_69, F_68)=k5_relat_1(E_69, F_68) | ~m1_subset_1(F_68, k1_zfmisc_1(k2_zfmisc_1(C_65, D_66))) | ~m1_subset_1(E_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_67))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.38/1.35  tff(c_178, plain, (![A_71, B_72, E_73]: (k4_relset_1(A_71, B_72, '#skF_1', '#skF_2', E_73, '#skF_3')=k5_relat_1(E_73, '#skF_3') | ~m1_subset_1(E_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(resolution, [status(thm)], [c_32, c_171])).
% 2.38/1.35  tff(c_185, plain, (![A_25]: (k4_relset_1(A_25, A_25, '#skF_1', '#skF_2', k6_partfun1(A_25), '#skF_3')=k5_relat_1(k6_partfun1(A_25), '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_178])).
% 2.38/1.35  tff(c_30, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.38/1.35  tff(c_66, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_30])).
% 2.38/1.35  tff(c_191, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_185, c_66])).
% 2.38/1.35  tff(c_203, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_33, c_191])).
% 2.38/1.35  tff(c_206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_156, c_97, c_203])).
% 2.38/1.35  tff(c_207, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 2.38/1.35  tff(c_394, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_393, c_207])).
% 2.38/1.35  tff(c_406, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3') | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_271, c_394])).
% 2.38/1.35  tff(c_409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_218, c_266, c_406])).
% 2.38/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.35  
% 2.38/1.35  Inference rules
% 2.38/1.35  ----------------------
% 2.38/1.35  #Ref     : 0
% 2.38/1.35  #Sup     : 78
% 2.38/1.35  #Fact    : 0
% 2.38/1.35  #Define  : 0
% 2.38/1.35  #Split   : 2
% 2.38/1.35  #Chain   : 0
% 2.38/1.35  #Close   : 0
% 2.38/1.35  
% 2.38/1.35  Ordering : KBO
% 2.38/1.35  
% 2.38/1.35  Simplification rules
% 2.38/1.35  ----------------------
% 2.38/1.35  #Subsume      : 2
% 2.38/1.35  #Demod        : 50
% 2.38/1.35  #Tautology    : 42
% 2.38/1.35  #SimpNegUnit  : 0
% 2.38/1.35  #BackRed      : 4
% 2.38/1.35  
% 2.38/1.35  #Partial instantiations: 0
% 2.38/1.35  #Strategies tried      : 1
% 2.38/1.35  
% 2.38/1.35  Timing (in seconds)
% 2.38/1.35  ----------------------
% 2.38/1.35  Preprocessing        : 0.30
% 2.38/1.35  Parsing              : 0.16
% 2.38/1.35  CNF conversion       : 0.02
% 2.38/1.35  Main loop            : 0.24
% 2.38/1.35  Inferencing          : 0.09
% 2.38/1.35  Reduction            : 0.07
% 2.38/1.35  Demodulation         : 0.05
% 2.38/1.35  BG Simplification    : 0.01
% 2.38/1.35  Subsumption          : 0.03
% 2.38/1.35  Abstraction          : 0.01
% 2.38/1.35  MUC search           : 0.00
% 2.38/1.35  Cooper               : 0.00
% 2.38/1.35  Total                : 0.57
% 2.38/1.35  Index Insertion      : 0.00
% 2.38/1.35  Index Deletion       : 0.00
% 2.38/1.35  Index Matching       : 0.00
% 2.38/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
