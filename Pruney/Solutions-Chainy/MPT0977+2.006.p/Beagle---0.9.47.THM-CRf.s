%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:46 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 122 expanded)
%              Number of leaves         :   36 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :  110 ( 193 expanded)
%              Number of equality atoms :   27 (  31 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r2_relset_1(A,B,k4_relset_1(A,A,A,B,k6_partfun1(A),C),C)
          & r2_relset_1(A,B,k4_relset_1(A,B,B,B,C,k6_partfun1(B)),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_87,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_73,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_50,plain,(
    ! [C_34,A_35,B_36] :
      ( v1_relat_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_58,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_50])).

tff(c_416,plain,(
    ! [A_109,B_110,D_111] :
      ( r2_relset_1(A_109,B_110,D_111,D_111)
      | ~ m1_subset_1(D_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_422,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_416])).

tff(c_272,plain,(
    ! [C_85,B_86,A_87] :
      ( v5_relat_1(C_85,B_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_87,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_280,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_272])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_343,plain,(
    ! [A_101,B_102] :
      ( k8_relat_1(A_101,B_102) = B_102
      | ~ r1_tarski(k2_relat_1(B_102),A_101)
      | ~ v1_relat_1(B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_399,plain,(
    ! [A_107,B_108] :
      ( k8_relat_1(A_107,B_108) = B_108
      | ~ v5_relat_1(B_108,A_107)
      | ~ v1_relat_1(B_108) ) ),
    inference(resolution,[status(thm)],[c_4,c_343])).

tff(c_405,plain,
    ( k8_relat_1('#skF_2','#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_280,c_399])).

tff(c_411,plain,(
    k8_relat_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_405])).

tff(c_32,plain,(
    ! [A_30] : k6_relat_1(A_30) = k6_partfun1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k5_relat_1(B_4,k6_relat_1(A_3)) = k8_relat_1(A_3,B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_38,plain,(
    ! [B_4,A_3] :
      ( k5_relat_1(B_4,k6_partfun1(A_3)) = k8_relat_1(A_3,B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_6])).

tff(c_30,plain,(
    ! [A_29] : m1_subset_1(k6_partfun1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_461,plain,(
    ! [A_122,B_121,F_123,C_119,D_124,E_120] :
      ( k4_relset_1(A_122,B_121,C_119,D_124,E_120,F_123) = k5_relat_1(E_120,F_123)
      | ~ m1_subset_1(F_123,k1_zfmisc_1(k2_zfmisc_1(C_119,D_124)))
      | ~ m1_subset_1(E_120,k1_zfmisc_1(k2_zfmisc_1(A_122,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_492,plain,(
    ! [A_129,B_130,A_131,E_132] :
      ( k4_relset_1(A_129,B_130,A_131,A_131,E_132,k6_partfun1(A_131)) = k5_relat_1(E_132,k6_partfun1(A_131))
      | ~ m1_subset_1(E_132,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(resolution,[status(thm)],[c_30,c_461])).

tff(c_498,plain,(
    ! [A_131] : k4_relset_1('#skF_1','#skF_2',A_131,A_131,'#skF_3',k6_partfun1(A_131)) = k5_relat_1('#skF_3',k6_partfun1(A_131)) ),
    inference(resolution,[status(thm)],[c_36,c_492])).

tff(c_139,plain,(
    ! [A_60,B_61,D_62] :
      ( r2_relset_1(A_60,B_61,D_62,D_62)
      | ~ m1_subset_1(D_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_145,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_139])).

tff(c_74,plain,(
    ! [C_48,A_49,B_50] :
      ( v4_relat_1(C_48,A_49)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_82,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_74])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( k7_relat_1(B_8,A_7) = B_8
      | ~ v4_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_94,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_10])).

tff(c_97,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_94])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_12,A_11)),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_108,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_14])).

tff(c_112,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_108])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k5_relat_1(k6_relat_1(A_9),B_10) = B_10
      | ~ r1_tarski(k1_relat_1(B_10),A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_173,plain,(
    ! [A_67,B_68] :
      ( k5_relat_1(k6_partfun1(A_67),B_68) = B_68
      | ~ r1_tarski(k1_relat_1(B_68),A_67)
      | ~ v1_relat_1(B_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_12])).

tff(c_179,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_112,c_173])).

tff(c_188,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_179])).

tff(c_246,plain,(
    ! [D_81,B_78,F_80,E_77,C_76,A_79] :
      ( k4_relset_1(A_79,B_78,C_76,D_81,E_77,F_80) = k5_relat_1(E_77,F_80)
      | ~ m1_subset_1(F_80,k1_zfmisc_1(k2_zfmisc_1(C_76,D_81)))
      | ~ m1_subset_1(E_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_253,plain,(
    ! [A_82,B_83,E_84] :
      ( k4_relset_1(A_82,B_83,'#skF_1','#skF_2',E_84,'#skF_3') = k5_relat_1(E_84,'#skF_3')
      | ~ m1_subset_1(E_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(resolution,[status(thm)],[c_36,c_246])).

tff(c_260,plain,(
    ! [A_29] : k4_relset_1(A_29,A_29,'#skF_1','#skF_2',k6_partfun1(A_29),'#skF_3') = k5_relat_1(k6_partfun1(A_29),'#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_253])).

tff(c_34,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_62,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_266,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_62])).

tff(c_269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_188,c_266])).

tff(c_270,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_499,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_270])).

tff(c_511,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k8_relat_1('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_499])).

tff(c_514,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_422,c_411,c_511])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:53:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.34  
% 2.49/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.34  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.49/1.34  
% 2.49/1.34  %Foreground sorts:
% 2.49/1.34  
% 2.49/1.34  
% 2.49/1.34  %Background operators:
% 2.49/1.34  
% 2.49/1.34  
% 2.49/1.34  %Foreground operators:
% 2.49/1.34  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.49/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.34  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.49/1.34  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.49/1.34  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.49/1.34  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.49/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.34  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.49/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.49/1.34  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.49/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.49/1.34  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.49/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.49/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.49/1.34  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.49/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.34  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.49/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.49/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.49/1.34  
% 2.49/1.36  tff(f_94, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_2)).
% 2.49/1.36  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.49/1.36  tff(f_81, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.49/1.36  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.49/1.36  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.49/1.36  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 2.49/1.36  tff(f_87, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.49/1.36  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 2.49/1.36  tff(f_85, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.49/1.36  tff(f_73, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.49/1.36  tff(f_47, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.49/1.36  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.49/1.36  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 2.49/1.36  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.49/1.36  tff(c_50, plain, (![C_34, A_35, B_36]: (v1_relat_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.49/1.36  tff(c_58, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_50])).
% 2.49/1.36  tff(c_416, plain, (![A_109, B_110, D_111]: (r2_relset_1(A_109, B_110, D_111, D_111) | ~m1_subset_1(D_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.49/1.36  tff(c_422, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_416])).
% 2.49/1.36  tff(c_272, plain, (![C_85, B_86, A_87]: (v5_relat_1(C_85, B_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_87, B_86))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.49/1.36  tff(c_280, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_272])).
% 2.49/1.36  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.49/1.36  tff(c_343, plain, (![A_101, B_102]: (k8_relat_1(A_101, B_102)=B_102 | ~r1_tarski(k2_relat_1(B_102), A_101) | ~v1_relat_1(B_102))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.49/1.36  tff(c_399, plain, (![A_107, B_108]: (k8_relat_1(A_107, B_108)=B_108 | ~v5_relat_1(B_108, A_107) | ~v1_relat_1(B_108))), inference(resolution, [status(thm)], [c_4, c_343])).
% 2.49/1.36  tff(c_405, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_280, c_399])).
% 2.49/1.36  tff(c_411, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_405])).
% 2.49/1.36  tff(c_32, plain, (![A_30]: (k6_relat_1(A_30)=k6_partfun1(A_30))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.49/1.36  tff(c_6, plain, (![B_4, A_3]: (k5_relat_1(B_4, k6_relat_1(A_3))=k8_relat_1(A_3, B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.49/1.36  tff(c_38, plain, (![B_4, A_3]: (k5_relat_1(B_4, k6_partfun1(A_3))=k8_relat_1(A_3, B_4) | ~v1_relat_1(B_4))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_6])).
% 2.49/1.36  tff(c_30, plain, (![A_29]: (m1_subset_1(k6_partfun1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.49/1.36  tff(c_461, plain, (![A_122, B_121, F_123, C_119, D_124, E_120]: (k4_relset_1(A_122, B_121, C_119, D_124, E_120, F_123)=k5_relat_1(E_120, F_123) | ~m1_subset_1(F_123, k1_zfmisc_1(k2_zfmisc_1(C_119, D_124))) | ~m1_subset_1(E_120, k1_zfmisc_1(k2_zfmisc_1(A_122, B_121))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.49/1.36  tff(c_492, plain, (![A_129, B_130, A_131, E_132]: (k4_relset_1(A_129, B_130, A_131, A_131, E_132, k6_partfun1(A_131))=k5_relat_1(E_132, k6_partfun1(A_131)) | ~m1_subset_1(E_132, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(resolution, [status(thm)], [c_30, c_461])).
% 2.49/1.36  tff(c_498, plain, (![A_131]: (k4_relset_1('#skF_1', '#skF_2', A_131, A_131, '#skF_3', k6_partfun1(A_131))=k5_relat_1('#skF_3', k6_partfun1(A_131)))), inference(resolution, [status(thm)], [c_36, c_492])).
% 2.49/1.36  tff(c_139, plain, (![A_60, B_61, D_62]: (r2_relset_1(A_60, B_61, D_62, D_62) | ~m1_subset_1(D_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.49/1.36  tff(c_145, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_139])).
% 2.49/1.36  tff(c_74, plain, (![C_48, A_49, B_50]: (v4_relat_1(C_48, A_49) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.49/1.36  tff(c_82, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_36, c_74])).
% 2.49/1.36  tff(c_10, plain, (![B_8, A_7]: (k7_relat_1(B_8, A_7)=B_8 | ~v4_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.49/1.36  tff(c_94, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_10])).
% 2.49/1.36  tff(c_97, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_94])).
% 2.49/1.36  tff(c_14, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(k7_relat_1(B_12, A_11)), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.49/1.36  tff(c_108, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_97, c_14])).
% 2.49/1.36  tff(c_112, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_108])).
% 2.49/1.36  tff(c_12, plain, (![A_9, B_10]: (k5_relat_1(k6_relat_1(A_9), B_10)=B_10 | ~r1_tarski(k1_relat_1(B_10), A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.49/1.36  tff(c_173, plain, (![A_67, B_68]: (k5_relat_1(k6_partfun1(A_67), B_68)=B_68 | ~r1_tarski(k1_relat_1(B_68), A_67) | ~v1_relat_1(B_68))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_12])).
% 2.49/1.36  tff(c_179, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_112, c_173])).
% 2.49/1.36  tff(c_188, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_179])).
% 2.49/1.36  tff(c_246, plain, (![D_81, B_78, F_80, E_77, C_76, A_79]: (k4_relset_1(A_79, B_78, C_76, D_81, E_77, F_80)=k5_relat_1(E_77, F_80) | ~m1_subset_1(F_80, k1_zfmisc_1(k2_zfmisc_1(C_76, D_81))) | ~m1_subset_1(E_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_78))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.49/1.36  tff(c_253, plain, (![A_82, B_83, E_84]: (k4_relset_1(A_82, B_83, '#skF_1', '#skF_2', E_84, '#skF_3')=k5_relat_1(E_84, '#skF_3') | ~m1_subset_1(E_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(resolution, [status(thm)], [c_36, c_246])).
% 2.49/1.36  tff(c_260, plain, (![A_29]: (k4_relset_1(A_29, A_29, '#skF_1', '#skF_2', k6_partfun1(A_29), '#skF_3')=k5_relat_1(k6_partfun1(A_29), '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_253])).
% 2.49/1.36  tff(c_34, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.49/1.36  tff(c_62, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_34])).
% 2.49/1.36  tff(c_266, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_260, c_62])).
% 2.49/1.36  tff(c_269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_145, c_188, c_266])).
% 2.49/1.36  tff(c_270, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_34])).
% 2.49/1.36  tff(c_499, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_498, c_270])).
% 2.49/1.36  tff(c_511, plain, (~r2_relset_1('#skF_1', '#skF_2', k8_relat_1('#skF_2', '#skF_3'), '#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_38, c_499])).
% 2.49/1.36  tff(c_514, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_422, c_411, c_511])).
% 2.49/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.36  
% 2.49/1.36  Inference rules
% 2.49/1.36  ----------------------
% 2.49/1.36  #Ref     : 0
% 2.49/1.36  #Sup     : 102
% 2.49/1.36  #Fact    : 0
% 2.49/1.36  #Define  : 0
% 2.49/1.36  #Split   : 1
% 2.49/1.36  #Chain   : 0
% 2.49/1.36  #Close   : 0
% 2.49/1.36  
% 2.49/1.36  Ordering : KBO
% 2.49/1.36  
% 2.49/1.36  Simplification rules
% 2.49/1.36  ----------------------
% 2.49/1.36  #Subsume      : 0
% 2.49/1.36  #Demod        : 61
% 2.49/1.36  #Tautology    : 57
% 2.49/1.36  #SimpNegUnit  : 0
% 2.49/1.36  #BackRed      : 3
% 2.49/1.36  
% 2.49/1.36  #Partial instantiations: 0
% 2.49/1.36  #Strategies tried      : 1
% 2.49/1.36  
% 2.49/1.36  Timing (in seconds)
% 2.49/1.36  ----------------------
% 2.49/1.36  Preprocessing        : 0.32
% 2.49/1.36  Parsing              : 0.17
% 2.49/1.36  CNF conversion       : 0.02
% 2.49/1.36  Main loop            : 0.28
% 2.49/1.36  Inferencing          : 0.11
% 2.49/1.36  Reduction            : 0.09
% 2.49/1.36  Demodulation         : 0.07
% 2.49/1.36  BG Simplification    : 0.02
% 2.49/1.36  Subsumption          : 0.03
% 2.49/1.36  Abstraction          : 0.02
% 2.49/1.36  MUC search           : 0.00
% 2.49/1.36  Cooper               : 0.00
% 2.49/1.36  Total                : 0.63
% 2.49/1.36  Index Insertion      : 0.00
% 2.49/1.36  Index Deletion       : 0.00
% 2.49/1.36  Index Matching       : 0.00
% 2.49/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
