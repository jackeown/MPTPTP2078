%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:46 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 106 expanded)
%              Number of leaves         :   31 (  50 expanded)
%              Depth                    :    7
%              Number of atoms          :  103 ( 170 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r2_relset_1(A,B,k4_relset_1(A,A,A,B,k6_partfun1(A),C),C)
          & r2_relset_1(A,B,k4_relset_1(A,B,B,B,C,k6_partfun1(B)),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_2)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_75,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_73,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_44,plain,(
    ! [C_29,A_30,B_31] :
      ( v1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_52,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_44])).

tff(c_195,plain,(
    ! [C_80,B_81,A_82] :
      ( v5_relat_1(C_80,B_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_82,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_203,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_195])).

tff(c_258,plain,(
    ! [A_96,B_97,C_98,D_99] :
      ( r2_relset_1(A_96,B_97,C_98,C_98)
      | ~ m1_subset_1(D_99,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97)))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_270,plain,(
    ! [C_103] :
      ( r2_relset_1('#skF_1','#skF_2',C_103,C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_30,c_258])).

tff(c_273,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_270])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,(
    ! [A_26] : k6_relat_1(A_26) = k6_partfun1(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( k5_relat_1(B_8,k6_relat_1(A_7)) = B_8
      | ~ r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_224,plain,(
    ! [B_90,A_91] :
      ( k5_relat_1(B_90,k6_partfun1(A_91)) = B_90
      | ~ r1_tarski(k2_relat_1(B_90),A_91)
      | ~ v1_relat_1(B_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_12])).

tff(c_228,plain,(
    ! [B_4,A_3] :
      ( k5_relat_1(B_4,k6_partfun1(A_3)) = B_4
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_224])).

tff(c_24,plain,(
    ! [A_25] : m1_subset_1(k6_relat_1(A_25),k1_zfmisc_1(k2_zfmisc_1(A_25,A_25))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_31,plain,(
    ! [A_25] : m1_subset_1(k6_partfun1(A_25),k1_zfmisc_1(k2_zfmisc_1(A_25,A_25))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24])).

tff(c_274,plain,(
    ! [E_108,C_104,A_109,F_107,D_105,B_106] :
      ( k4_relset_1(A_109,B_106,C_104,D_105,E_108,F_107) = k5_relat_1(E_108,F_107)
      | ~ m1_subset_1(F_107,k1_zfmisc_1(k2_zfmisc_1(C_104,D_105)))
      | ~ m1_subset_1(E_108,k1_zfmisc_1(k2_zfmisc_1(A_109,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_309,plain,(
    ! [A_114,B_115,A_116,E_117] :
      ( k4_relset_1(A_114,B_115,A_116,A_116,E_117,k6_partfun1(A_116)) = k5_relat_1(E_117,k6_partfun1(A_116))
      | ~ m1_subset_1(E_117,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(resolution,[status(thm)],[c_31,c_274])).

tff(c_315,plain,(
    ! [A_116] : k4_relset_1('#skF_1','#skF_2',A_116,A_116,'#skF_3',k6_partfun1(A_116)) = k5_relat_1('#skF_3',k6_partfun1(A_116)) ),
    inference(resolution,[status(thm)],[c_30,c_309])).

tff(c_56,plain,(
    ! [C_37,A_38,B_39] :
      ( v4_relat_1(C_37,A_38)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_64,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_56])).

tff(c_135,plain,(
    ! [A_59,B_60,C_61,D_62] :
      ( r2_relset_1(A_59,B_60,C_61,C_61)
      | ~ m1_subset_1(D_62,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60)))
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_154,plain,(
    ! [C_72] :
      ( r2_relset_1('#skF_1','#skF_2',C_72,C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_30,c_135])).

tff(c_157,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_154])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k5_relat_1(k6_relat_1(A_5),B_6) = B_6
      | ~ r1_tarski(k1_relat_1(B_6),A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_86,plain,(
    ! [A_48,B_49] :
      ( k5_relat_1(k6_partfun1(A_48),B_49) = B_49
      | ~ r1_tarski(k1_relat_1(B_49),A_48)
      | ~ v1_relat_1(B_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_10])).

tff(c_90,plain,(
    ! [A_1,B_2] :
      ( k5_relat_1(k6_partfun1(A_1),B_2) = B_2
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_86])).

tff(c_142,plain,(
    ! [C_63,D_64,F_66,E_67,B_65,A_68] :
      ( k4_relset_1(A_68,B_65,C_63,D_64,E_67,F_66) = k5_relat_1(E_67,F_66)
      | ~ m1_subset_1(F_66,k1_zfmisc_1(k2_zfmisc_1(C_63,D_64)))
      | ~ m1_subset_1(E_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_158,plain,(
    ! [A_73,B_74,E_75] :
      ( k4_relset_1(A_73,B_74,'#skF_1','#skF_2',E_75,'#skF_3') = k5_relat_1(E_75,'#skF_3')
      | ~ m1_subset_1(E_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(resolution,[status(thm)],[c_30,c_142])).

tff(c_165,plain,(
    ! [A_25] : k4_relset_1(A_25,A_25,'#skF_1','#skF_2',k6_partfun1(A_25),'#skF_3') = k5_relat_1(k6_partfun1(A_25),'#skF_3') ),
    inference(resolution,[status(thm)],[c_31,c_158])).

tff(c_28,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_65,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_171,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_65])).

tff(c_183,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3')
    | ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_171])).

tff(c_186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_64,c_157,c_183])).

tff(c_187,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_316,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_187])).

tff(c_328,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_316])).

tff(c_331,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_203,c_273,c_328])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:53:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.29  
% 2.32/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.29  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.32/1.29  
% 2.32/1.29  %Foreground sorts:
% 2.32/1.29  
% 2.32/1.29  
% 2.32/1.29  %Background operators:
% 2.32/1.29  
% 2.32/1.29  
% 2.32/1.29  %Foreground operators:
% 2.32/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.29  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.32/1.29  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.32/1.29  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.32/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.32/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.32/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.32/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.32/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.32/1.29  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.32/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.32/1.29  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.32/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.32/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.32/1.29  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.32/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.29  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.32/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.32/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.32/1.29  
% 2.32/1.30  tff(f_82, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_2)).
% 2.32/1.30  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.32/1.30  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.32/1.30  tff(f_71, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.32/1.30  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.32/1.30  tff(f_75, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.32/1.30  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 2.32/1.30  tff(f_73, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 2.32/1.30  tff(f_65, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.32/1.30  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.32/1.30  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 2.32/1.30  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.32/1.30  tff(c_44, plain, (![C_29, A_30, B_31]: (v1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.32/1.30  tff(c_52, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_44])).
% 2.32/1.30  tff(c_195, plain, (![C_80, B_81, A_82]: (v5_relat_1(C_80, B_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_82, B_81))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.32/1.30  tff(c_203, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_195])).
% 2.32/1.30  tff(c_258, plain, (![A_96, B_97, C_98, D_99]: (r2_relset_1(A_96, B_97, C_98, C_98) | ~m1_subset_1(D_99, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.32/1.30  tff(c_270, plain, (![C_103]: (r2_relset_1('#skF_1', '#skF_2', C_103, C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_30, c_258])).
% 2.32/1.30  tff(c_273, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_270])).
% 2.32/1.30  tff(c_8, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.32/1.30  tff(c_26, plain, (![A_26]: (k6_relat_1(A_26)=k6_partfun1(A_26))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.32/1.30  tff(c_12, plain, (![B_8, A_7]: (k5_relat_1(B_8, k6_relat_1(A_7))=B_8 | ~r1_tarski(k2_relat_1(B_8), A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.32/1.30  tff(c_224, plain, (![B_90, A_91]: (k5_relat_1(B_90, k6_partfun1(A_91))=B_90 | ~r1_tarski(k2_relat_1(B_90), A_91) | ~v1_relat_1(B_90))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_12])).
% 2.32/1.30  tff(c_228, plain, (![B_4, A_3]: (k5_relat_1(B_4, k6_partfun1(A_3))=B_4 | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(resolution, [status(thm)], [c_8, c_224])).
% 2.32/1.30  tff(c_24, plain, (![A_25]: (m1_subset_1(k6_relat_1(A_25), k1_zfmisc_1(k2_zfmisc_1(A_25, A_25))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.32/1.30  tff(c_31, plain, (![A_25]: (m1_subset_1(k6_partfun1(A_25), k1_zfmisc_1(k2_zfmisc_1(A_25, A_25))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24])).
% 2.32/1.30  tff(c_274, plain, (![E_108, C_104, A_109, F_107, D_105, B_106]: (k4_relset_1(A_109, B_106, C_104, D_105, E_108, F_107)=k5_relat_1(E_108, F_107) | ~m1_subset_1(F_107, k1_zfmisc_1(k2_zfmisc_1(C_104, D_105))) | ~m1_subset_1(E_108, k1_zfmisc_1(k2_zfmisc_1(A_109, B_106))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.32/1.30  tff(c_309, plain, (![A_114, B_115, A_116, E_117]: (k4_relset_1(A_114, B_115, A_116, A_116, E_117, k6_partfun1(A_116))=k5_relat_1(E_117, k6_partfun1(A_116)) | ~m1_subset_1(E_117, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(resolution, [status(thm)], [c_31, c_274])).
% 2.32/1.30  tff(c_315, plain, (![A_116]: (k4_relset_1('#skF_1', '#skF_2', A_116, A_116, '#skF_3', k6_partfun1(A_116))=k5_relat_1('#skF_3', k6_partfun1(A_116)))), inference(resolution, [status(thm)], [c_30, c_309])).
% 2.32/1.30  tff(c_56, plain, (![C_37, A_38, B_39]: (v4_relat_1(C_37, A_38) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.32/1.30  tff(c_64, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_56])).
% 2.32/1.30  tff(c_135, plain, (![A_59, B_60, C_61, D_62]: (r2_relset_1(A_59, B_60, C_61, C_61) | ~m1_subset_1(D_62, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.32/1.30  tff(c_154, plain, (![C_72]: (r2_relset_1('#skF_1', '#skF_2', C_72, C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_30, c_135])).
% 2.32/1.30  tff(c_157, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_154])).
% 2.32/1.30  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), A_1) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.32/1.30  tff(c_10, plain, (![A_5, B_6]: (k5_relat_1(k6_relat_1(A_5), B_6)=B_6 | ~r1_tarski(k1_relat_1(B_6), A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.32/1.30  tff(c_86, plain, (![A_48, B_49]: (k5_relat_1(k6_partfun1(A_48), B_49)=B_49 | ~r1_tarski(k1_relat_1(B_49), A_48) | ~v1_relat_1(B_49))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_10])).
% 2.32/1.30  tff(c_90, plain, (![A_1, B_2]: (k5_relat_1(k6_partfun1(A_1), B_2)=B_2 | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_4, c_86])).
% 2.32/1.30  tff(c_142, plain, (![C_63, D_64, F_66, E_67, B_65, A_68]: (k4_relset_1(A_68, B_65, C_63, D_64, E_67, F_66)=k5_relat_1(E_67, F_66) | ~m1_subset_1(F_66, k1_zfmisc_1(k2_zfmisc_1(C_63, D_64))) | ~m1_subset_1(E_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_65))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.32/1.30  tff(c_158, plain, (![A_73, B_74, E_75]: (k4_relset_1(A_73, B_74, '#skF_1', '#skF_2', E_75, '#skF_3')=k5_relat_1(E_75, '#skF_3') | ~m1_subset_1(E_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(resolution, [status(thm)], [c_30, c_142])).
% 2.32/1.30  tff(c_165, plain, (![A_25]: (k4_relset_1(A_25, A_25, '#skF_1', '#skF_2', k6_partfun1(A_25), '#skF_3')=k5_relat_1(k6_partfun1(A_25), '#skF_3'))), inference(resolution, [status(thm)], [c_31, c_158])).
% 2.32/1.30  tff(c_28, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.32/1.30  tff(c_65, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_28])).
% 2.32/1.30  tff(c_171, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_165, c_65])).
% 2.32/1.30  tff(c_183, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3') | ~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_90, c_171])).
% 2.32/1.30  tff(c_186, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_64, c_157, c_183])).
% 2.32/1.30  tff(c_187, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_28])).
% 2.32/1.30  tff(c_316, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_315, c_187])).
% 2.32/1.30  tff(c_328, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3') | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_228, c_316])).
% 2.32/1.30  tff(c_331, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_203, c_273, c_328])).
% 2.32/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.30  
% 2.32/1.30  Inference rules
% 2.32/1.30  ----------------------
% 2.32/1.30  #Ref     : 0
% 2.32/1.30  #Sup     : 63
% 2.32/1.30  #Fact    : 0
% 2.32/1.30  #Define  : 0
% 2.32/1.30  #Split   : 1
% 2.32/1.30  #Chain   : 0
% 2.32/1.30  #Close   : 0
% 2.32/1.30  
% 2.32/1.30  Ordering : KBO
% 2.32/1.30  
% 2.32/1.30  Simplification rules
% 2.32/1.30  ----------------------
% 2.32/1.30  #Subsume      : 2
% 2.32/1.30  #Demod        : 25
% 2.32/1.30  #Tautology    : 27
% 2.32/1.30  #SimpNegUnit  : 0
% 2.32/1.30  #BackRed      : 3
% 2.32/1.30  
% 2.32/1.30  #Partial instantiations: 0
% 2.32/1.30  #Strategies tried      : 1
% 2.32/1.30  
% 2.32/1.30  Timing (in seconds)
% 2.32/1.30  ----------------------
% 2.32/1.31  Preprocessing        : 0.29
% 2.32/1.31  Parsing              : 0.15
% 2.32/1.31  CNF conversion       : 0.02
% 2.32/1.31  Main loop            : 0.23
% 2.32/1.31  Inferencing          : 0.09
% 2.32/1.31  Reduction            : 0.07
% 2.32/1.31  Demodulation         : 0.05
% 2.32/1.31  BG Simplification    : 0.01
% 2.32/1.31  Subsumption          : 0.03
% 2.32/1.31  Abstraction          : 0.01
% 2.32/1.31  MUC search           : 0.00
% 2.32/1.31  Cooper               : 0.00
% 2.32/1.31  Total                : 0.55
% 2.32/1.31  Index Insertion      : 0.00
% 2.32/1.31  Index Deletion       : 0.00
% 2.32/1.31  Index Matching       : 0.00
% 2.32/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
