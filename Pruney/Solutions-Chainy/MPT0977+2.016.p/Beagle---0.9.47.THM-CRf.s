%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:47 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 123 expanded)
%              Number of leaves         :   33 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :  110 ( 195 expanded)
%              Number of equality atoms :   22 (  29 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r2_relset_1(A,B,k4_relset_1(A,A,A,B,k6_partfun1(A),C),C)
          & r2_relset_1(A,B,k4_relset_1(A,B,B,B,C,k6_partfun1(B)),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_79,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_77,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_44,plain,(
    ! [C_31,A_32,B_33] :
      ( v1_relat_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_52,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_44])).

tff(c_254,plain,(
    ! [C_85,B_86,A_87] :
      ( v5_relat_1(C_85,B_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_87,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_262,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_254])).

tff(c_382,plain,(
    ! [A_104,B_105,C_106,D_107] :
      ( r2_relset_1(A_104,B_105,C_106,C_106)
      | ~ m1_subset_1(D_107,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105)))
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_389,plain,(
    ! [C_108] :
      ( r2_relset_1('#skF_1','#skF_2',C_108,C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_30,c_382])).

tff(c_392,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_389])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [A_28] : k6_relat_1(A_28) = k6_partfun1(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( k5_relat_1(B_8,k6_relat_1(A_7)) = B_8
      | ~ r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_336,plain,(
    ! [B_98,A_99] :
      ( k5_relat_1(B_98,k6_partfun1(A_99)) = B_98
      | ~ r1_tarski(k2_relat_1(B_98),A_99)
      | ~ v1_relat_1(B_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_10])).

tff(c_340,plain,(
    ! [B_2,A_1] :
      ( k5_relat_1(B_2,k6_partfun1(A_1)) = B_2
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_336])).

tff(c_24,plain,(
    ! [A_27] : m1_subset_1(k6_relat_1(A_27),k1_zfmisc_1(k2_zfmisc_1(A_27,A_27))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_31,plain,(
    ! [A_27] : m1_subset_1(k6_partfun1(A_27),k1_zfmisc_1(k2_zfmisc_1(A_27,A_27))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24])).

tff(c_398,plain,(
    ! [A_113,D_116,B_114,F_115,E_117,C_112] :
      ( k4_relset_1(A_113,B_114,C_112,D_116,E_117,F_115) = k5_relat_1(E_117,F_115)
      | ~ m1_subset_1(F_115,k1_zfmisc_1(k2_zfmisc_1(C_112,D_116)))
      | ~ m1_subset_1(E_117,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_414,plain,(
    ! [A_121,B_122,A_123,E_124] :
      ( k4_relset_1(A_121,B_122,A_123,A_123,E_124,k6_partfun1(A_123)) = k5_relat_1(E_124,k6_partfun1(A_123))
      | ~ m1_subset_1(E_124,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(resolution,[status(thm)],[c_31,c_398])).

tff(c_420,plain,(
    ! [A_123] : k4_relset_1('#skF_1','#skF_2',A_123,A_123,'#skF_3',k6_partfun1(A_123)) = k5_relat_1('#skF_3',k6_partfun1(A_123)) ),
    inference(resolution,[status(thm)],[c_30,c_414])).

tff(c_195,plain,(
    ! [A_62,B_63,C_64,D_65] :
      ( r2_relset_1(A_62,B_63,C_64,C_64)
      | ~ m1_subset_1(D_65,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_202,plain,(
    ! [C_66] :
      ( r2_relset_1('#skF_1','#skF_2',C_66,C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_30,c_195])).

tff(c_205,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_202])).

tff(c_56,plain,(
    ! [C_39,A_40,B_41] :
      ( v4_relat_1(C_39,A_40)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_64,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_56])).

tff(c_67,plain,(
    ! [B_43,A_44] :
      ( k7_relat_1(B_43,A_44) = B_43
      | ~ v4_relat_1(B_43,A_44)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_73,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_67])).

tff(c_79,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_73])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_10,A_9)),A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_83,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_12])).

tff(c_87,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_83])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k5_relat_1(k6_relat_1(A_5),B_6) = B_6
      | ~ r1_tarski(k1_relat_1(B_6),A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_133,plain,(
    ! [A_57,B_58] :
      ( k5_relat_1(k6_partfun1(A_57),B_58) = B_58
      | ~ r1_tarski(k1_relat_1(B_58),A_57)
      | ~ v1_relat_1(B_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_8])).

tff(c_139,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_87,c_133])).

tff(c_148,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_139])).

tff(c_211,plain,(
    ! [D_74,C_70,B_72,E_75,A_71,F_73] :
      ( k4_relset_1(A_71,B_72,C_70,D_74,E_75,F_73) = k5_relat_1(E_75,F_73)
      | ~ m1_subset_1(F_73,k1_zfmisc_1(k2_zfmisc_1(C_70,D_74)))
      | ~ m1_subset_1(E_75,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_218,plain,(
    ! [A_76,B_77,E_78] :
      ( k4_relset_1(A_76,B_77,'#skF_1','#skF_2',E_78,'#skF_3') = k5_relat_1(E_78,'#skF_3')
      | ~ m1_subset_1(E_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(resolution,[status(thm)],[c_30,c_211])).

tff(c_225,plain,(
    ! [A_27] : k4_relset_1(A_27,A_27,'#skF_1','#skF_2',k6_partfun1(A_27),'#skF_3') = k5_relat_1(k6_partfun1(A_27),'#skF_3') ),
    inference(resolution,[status(thm)],[c_31,c_218])).

tff(c_28,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_65,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_247,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_65])).

tff(c_250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_148,c_247])).

tff(c_251,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_425,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_251])).

tff(c_437,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_340,c_425])).

tff(c_440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_262,c_392,c_437])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:25:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.35  
% 2.36/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.35  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.36/1.35  
% 2.36/1.35  %Foreground sorts:
% 2.36/1.35  
% 2.36/1.35  
% 2.36/1.35  %Background operators:
% 2.36/1.35  
% 2.36/1.35  
% 2.36/1.35  %Foreground operators:
% 2.36/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.35  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.36/1.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.36/1.35  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.36/1.35  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.36/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.36/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.36/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.36/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.36/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.36/1.35  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.36/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.36/1.35  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.36/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.36/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.36/1.35  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.36/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.35  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.36/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.36/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.36/1.35  
% 2.36/1.37  tff(f_86, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_2)).
% 2.36/1.37  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.36/1.37  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.36/1.37  tff(f_75, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.36/1.37  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.36/1.37  tff(f_79, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.36/1.37  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 2.36/1.37  tff(f_77, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 2.36/1.37  tff(f_69, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.36/1.37  tff(f_37, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.36/1.37  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.36/1.37  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 2.36/1.37  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.36/1.37  tff(c_44, plain, (![C_31, A_32, B_33]: (v1_relat_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.36/1.37  tff(c_52, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_44])).
% 2.36/1.37  tff(c_254, plain, (![C_85, B_86, A_87]: (v5_relat_1(C_85, B_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_87, B_86))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.36/1.37  tff(c_262, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_254])).
% 2.36/1.37  tff(c_382, plain, (![A_104, B_105, C_106, D_107]: (r2_relset_1(A_104, B_105, C_106, C_106) | ~m1_subset_1(D_107, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.36/1.37  tff(c_389, plain, (![C_108]: (r2_relset_1('#skF_1', '#skF_2', C_108, C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_30, c_382])).
% 2.36/1.37  tff(c_392, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_389])).
% 2.36/1.37  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.36/1.37  tff(c_26, plain, (![A_28]: (k6_relat_1(A_28)=k6_partfun1(A_28))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.36/1.37  tff(c_10, plain, (![B_8, A_7]: (k5_relat_1(B_8, k6_relat_1(A_7))=B_8 | ~r1_tarski(k2_relat_1(B_8), A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.36/1.37  tff(c_336, plain, (![B_98, A_99]: (k5_relat_1(B_98, k6_partfun1(A_99))=B_98 | ~r1_tarski(k2_relat_1(B_98), A_99) | ~v1_relat_1(B_98))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_10])).
% 2.36/1.37  tff(c_340, plain, (![B_2, A_1]: (k5_relat_1(B_2, k6_partfun1(A_1))=B_2 | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_4, c_336])).
% 2.36/1.37  tff(c_24, plain, (![A_27]: (m1_subset_1(k6_relat_1(A_27), k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.36/1.37  tff(c_31, plain, (![A_27]: (m1_subset_1(k6_partfun1(A_27), k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24])).
% 2.36/1.37  tff(c_398, plain, (![A_113, D_116, B_114, F_115, E_117, C_112]: (k4_relset_1(A_113, B_114, C_112, D_116, E_117, F_115)=k5_relat_1(E_117, F_115) | ~m1_subset_1(F_115, k1_zfmisc_1(k2_zfmisc_1(C_112, D_116))) | ~m1_subset_1(E_117, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.36/1.37  tff(c_414, plain, (![A_121, B_122, A_123, E_124]: (k4_relset_1(A_121, B_122, A_123, A_123, E_124, k6_partfun1(A_123))=k5_relat_1(E_124, k6_partfun1(A_123)) | ~m1_subset_1(E_124, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(resolution, [status(thm)], [c_31, c_398])).
% 2.36/1.37  tff(c_420, plain, (![A_123]: (k4_relset_1('#skF_1', '#skF_2', A_123, A_123, '#skF_3', k6_partfun1(A_123))=k5_relat_1('#skF_3', k6_partfun1(A_123)))), inference(resolution, [status(thm)], [c_30, c_414])).
% 2.36/1.37  tff(c_195, plain, (![A_62, B_63, C_64, D_65]: (r2_relset_1(A_62, B_63, C_64, C_64) | ~m1_subset_1(D_65, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.36/1.37  tff(c_202, plain, (![C_66]: (r2_relset_1('#skF_1', '#skF_2', C_66, C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_30, c_195])).
% 2.36/1.37  tff(c_205, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_202])).
% 2.36/1.37  tff(c_56, plain, (![C_39, A_40, B_41]: (v4_relat_1(C_39, A_40) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.36/1.37  tff(c_64, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_56])).
% 2.36/1.37  tff(c_67, plain, (![B_43, A_44]: (k7_relat_1(B_43, A_44)=B_43 | ~v4_relat_1(B_43, A_44) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.36/1.37  tff(c_73, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_67])).
% 2.36/1.37  tff(c_79, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_73])).
% 2.36/1.37  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(k7_relat_1(B_10, A_9)), A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.36/1.37  tff(c_83, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_79, c_12])).
% 2.64/1.37  tff(c_87, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_83])).
% 2.64/1.37  tff(c_8, plain, (![A_5, B_6]: (k5_relat_1(k6_relat_1(A_5), B_6)=B_6 | ~r1_tarski(k1_relat_1(B_6), A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.64/1.37  tff(c_133, plain, (![A_57, B_58]: (k5_relat_1(k6_partfun1(A_57), B_58)=B_58 | ~r1_tarski(k1_relat_1(B_58), A_57) | ~v1_relat_1(B_58))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_8])).
% 2.64/1.37  tff(c_139, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_87, c_133])).
% 2.64/1.37  tff(c_148, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_139])).
% 2.64/1.37  tff(c_211, plain, (![D_74, C_70, B_72, E_75, A_71, F_73]: (k4_relset_1(A_71, B_72, C_70, D_74, E_75, F_73)=k5_relat_1(E_75, F_73) | ~m1_subset_1(F_73, k1_zfmisc_1(k2_zfmisc_1(C_70, D_74))) | ~m1_subset_1(E_75, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.64/1.37  tff(c_218, plain, (![A_76, B_77, E_78]: (k4_relset_1(A_76, B_77, '#skF_1', '#skF_2', E_78, '#skF_3')=k5_relat_1(E_78, '#skF_3') | ~m1_subset_1(E_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(resolution, [status(thm)], [c_30, c_211])).
% 2.64/1.37  tff(c_225, plain, (![A_27]: (k4_relset_1(A_27, A_27, '#skF_1', '#skF_2', k6_partfun1(A_27), '#skF_3')=k5_relat_1(k6_partfun1(A_27), '#skF_3'))), inference(resolution, [status(thm)], [c_31, c_218])).
% 2.64/1.37  tff(c_28, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.64/1.37  tff(c_65, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_28])).
% 2.64/1.37  tff(c_247, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_225, c_65])).
% 2.64/1.37  tff(c_250, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_205, c_148, c_247])).
% 2.64/1.37  tff(c_251, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_28])).
% 2.64/1.37  tff(c_425, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_420, c_251])).
% 2.64/1.37  tff(c_437, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3') | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_340, c_425])).
% 2.64/1.37  tff(c_440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_262, c_392, c_437])).
% 2.64/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.37  
% 2.64/1.37  Inference rules
% 2.64/1.37  ----------------------
% 2.64/1.37  #Ref     : 0
% 2.64/1.37  #Sup     : 89
% 2.64/1.37  #Fact    : 0
% 2.64/1.37  #Define  : 0
% 2.64/1.37  #Split   : 1
% 2.64/1.37  #Chain   : 0
% 2.64/1.37  #Close   : 0
% 2.64/1.37  
% 2.64/1.37  Ordering : KBO
% 2.64/1.37  
% 2.64/1.37  Simplification rules
% 2.64/1.37  ----------------------
% 2.64/1.37  #Subsume      : 0
% 2.64/1.37  #Demod        : 50
% 2.64/1.37  #Tautology    : 44
% 2.64/1.37  #SimpNegUnit  : 0
% 2.64/1.37  #BackRed      : 2
% 2.64/1.37  
% 2.64/1.37  #Partial instantiations: 0
% 2.64/1.37  #Strategies tried      : 1
% 2.64/1.37  
% 2.64/1.37  Timing (in seconds)
% 2.64/1.37  ----------------------
% 2.64/1.37  Preprocessing        : 0.32
% 2.64/1.37  Parsing              : 0.17
% 2.64/1.37  CNF conversion       : 0.02
% 2.64/1.37  Main loop            : 0.28
% 2.64/1.37  Inferencing          : 0.12
% 2.64/1.37  Reduction            : 0.08
% 2.64/1.37  Demodulation         : 0.06
% 2.64/1.37  BG Simplification    : 0.02
% 2.64/1.37  Subsumption          : 0.03
% 2.64/1.37  Abstraction          : 0.02
% 2.64/1.37  MUC search           : 0.00
% 2.64/1.37  Cooper               : 0.00
% 2.64/1.37  Total                : 0.63
% 2.64/1.37  Index Insertion      : 0.00
% 2.64/1.37  Index Deletion       : 0.00
% 2.64/1.37  Index Matching       : 0.00
% 2.64/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
