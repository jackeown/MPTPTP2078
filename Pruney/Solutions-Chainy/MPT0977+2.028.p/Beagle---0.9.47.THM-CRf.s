%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:49 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 114 expanded)
%              Number of leaves         :   35 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :  109 ( 176 expanded)
%              Number of equality atoms :   22 (  30 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_95,negated_conjecture,(
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

tff(f_88,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_86,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

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

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_68,plain,(
    ! [B_44,A_45] :
      ( v1_relat_1(B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_77,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_68])).

tff(c_84,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_77])).

tff(c_641,plain,(
    ! [C_140,B_141,A_142] :
      ( v5_relat_1(C_140,B_141)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_142,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_654,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_641])).

tff(c_725,plain,(
    ! [A_160,B_161,D_162] :
      ( r2_relset_1(A_160,B_161,D_162,D_162)
      | ~ m1_subset_1(D_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_735,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_725])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_34,plain,(
    ! [A_34] : k6_relat_1(A_34) = k6_partfun1(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_16,plain,(
    ! [B_13,A_12] :
      ( k5_relat_1(B_13,k6_relat_1(A_12)) = B_13
      | ~ r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_752,plain,(
    ! [B_170,A_171] :
      ( k5_relat_1(B_170,k6_partfun1(A_171)) = B_170
      | ~ r1_tarski(k2_relat_1(B_170),A_171)
      | ~ v1_relat_1(B_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_16])).

tff(c_756,plain,(
    ! [B_7,A_6] :
      ( k5_relat_1(B_7,k6_partfun1(A_6)) = B_7
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_752])).

tff(c_32,plain,(
    ! [A_33] : m1_subset_1(k6_relat_1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_39,plain,(
    ! [A_33] : m1_subset_1(k6_partfun1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32])).

tff(c_1218,plain,(
    ! [E_234,C_232,A_237,D_236,B_235,F_233] :
      ( k4_relset_1(A_237,B_235,C_232,D_236,E_234,F_233) = k5_relat_1(E_234,F_233)
      | ~ m1_subset_1(F_233,k1_zfmisc_1(k2_zfmisc_1(C_232,D_236)))
      | ~ m1_subset_1(E_234,k1_zfmisc_1(k2_zfmisc_1(A_237,B_235))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1830,plain,(
    ! [A_314,B_315,A_316,E_317] :
      ( k4_relset_1(A_314,B_315,A_316,A_316,E_317,k6_partfun1(A_316)) = k5_relat_1(E_317,k6_partfun1(A_316))
      | ~ m1_subset_1(E_317,k1_zfmisc_1(k2_zfmisc_1(A_314,B_315))) ) ),
    inference(resolution,[status(thm)],[c_39,c_1218])).

tff(c_1852,plain,(
    ! [A_316] : k4_relset_1('#skF_1','#skF_2',A_316,A_316,'#skF_3',k6_partfun1(A_316)) = k5_relat_1('#skF_3',k6_partfun1(A_316)) ),
    inference(resolution,[status(thm)],[c_38,c_1830])).

tff(c_183,plain,(
    ! [A_69,B_70,D_71] :
      ( r2_relset_1(A_69,B_70,D_71,D_71)
      | ~ m1_subset_1(D_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_193,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_183])).

tff(c_195,plain,(
    ! [A_72,B_73,C_74] :
      ( k1_relset_1(A_72,B_73,C_74) = k1_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_208,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_195])).

tff(c_268,plain,(
    ! [A_90,B_91,C_92] :
      ( m1_subset_1(k1_relset_1(A_90,B_91,C_92),k1_zfmisc_1(A_90))
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_295,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_268])).

tff(c_305,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_295])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_313,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_305,c_2])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k5_relat_1(k6_relat_1(A_10),B_11) = B_11
      | ~ r1_tarski(k1_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_41,plain,(
    ! [A_10,B_11] :
      ( k5_relat_1(k6_partfun1(A_10),B_11) = B_11
      | ~ r1_tarski(k1_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_14])).

tff(c_316,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_313,c_41])).

tff(c_322,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_316])).

tff(c_400,plain,(
    ! [C_99,D_103,B_102,A_104,F_100,E_101] :
      ( k4_relset_1(A_104,B_102,C_99,D_103,E_101,F_100) = k5_relat_1(E_101,F_100)
      | ~ m1_subset_1(F_100,k1_zfmisc_1(k2_zfmisc_1(C_99,D_103)))
      | ~ m1_subset_1(E_101,k1_zfmisc_1(k2_zfmisc_1(A_104,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_494,plain,(
    ! [A_116,B_117,E_118] :
      ( k4_relset_1(A_116,B_117,'#skF_1','#skF_2',E_118,'#skF_3') = k5_relat_1(E_118,'#skF_3')
      | ~ m1_subset_1(E_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(resolution,[status(thm)],[c_38,c_400])).

tff(c_516,plain,(
    ! [A_33] : k4_relset_1(A_33,A_33,'#skF_1','#skF_2',k6_partfun1(A_33),'#skF_3') = k5_relat_1(k6_partfun1(A_33),'#skF_3') ),
    inference(resolution,[status(thm)],[c_39,c_494])).

tff(c_36,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_85,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_621,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_516,c_85])).

tff(c_624,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_322,c_621])).

tff(c_625,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1853,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1852,c_625])).

tff(c_1865,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_756,c_1853])).

tff(c_1868,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_654,c_735,c_1865])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n021.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 09:31:19 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.59  
% 3.52/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.59  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.52/1.59  
% 3.52/1.59  %Foreground sorts:
% 3.52/1.59  
% 3.52/1.59  
% 3.52/1.59  %Background operators:
% 3.52/1.59  
% 3.52/1.59  
% 3.52/1.59  %Foreground operators:
% 3.52/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.52/1.59  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.52/1.59  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.52/1.59  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.52/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.52/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.52/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.52/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.52/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.52/1.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.52/1.59  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.52/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.52/1.59  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.52/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.52/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.52/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.52/1.59  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.52/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.52/1.59  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.52/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.52/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.52/1.59  
% 3.52/1.61  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.52/1.61  tff(f_95, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_2)).
% 3.52/1.61  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.52/1.61  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.52/1.61  tff(f_84, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.52/1.61  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.52/1.61  tff(f_88, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.52/1.61  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 3.52/1.61  tff(f_86, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 3.52/1.61  tff(f_76, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 3.52/1.61  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.52/1.61  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.52/1.61  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.52/1.61  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 3.52/1.61  tff(c_12, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.52/1.61  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.52/1.61  tff(c_68, plain, (![B_44, A_45]: (v1_relat_1(B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.52/1.61  tff(c_77, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_68])).
% 3.52/1.61  tff(c_84, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_77])).
% 3.52/1.61  tff(c_641, plain, (![C_140, B_141, A_142]: (v5_relat_1(C_140, B_141) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_142, B_141))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.52/1.61  tff(c_654, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_641])).
% 3.52/1.61  tff(c_725, plain, (![A_160, B_161, D_162]: (r2_relset_1(A_160, B_161, D_162, D_162) | ~m1_subset_1(D_162, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.52/1.61  tff(c_735, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_725])).
% 3.52/1.61  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.52/1.61  tff(c_34, plain, (![A_34]: (k6_relat_1(A_34)=k6_partfun1(A_34))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.52/1.61  tff(c_16, plain, (![B_13, A_12]: (k5_relat_1(B_13, k6_relat_1(A_12))=B_13 | ~r1_tarski(k2_relat_1(B_13), A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.52/1.61  tff(c_752, plain, (![B_170, A_171]: (k5_relat_1(B_170, k6_partfun1(A_171))=B_170 | ~r1_tarski(k2_relat_1(B_170), A_171) | ~v1_relat_1(B_170))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_16])).
% 3.52/1.61  tff(c_756, plain, (![B_7, A_6]: (k5_relat_1(B_7, k6_partfun1(A_6))=B_7 | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_10, c_752])).
% 3.52/1.61  tff(c_32, plain, (![A_33]: (m1_subset_1(k6_relat_1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.52/1.61  tff(c_39, plain, (![A_33]: (m1_subset_1(k6_partfun1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32])).
% 3.52/1.61  tff(c_1218, plain, (![E_234, C_232, A_237, D_236, B_235, F_233]: (k4_relset_1(A_237, B_235, C_232, D_236, E_234, F_233)=k5_relat_1(E_234, F_233) | ~m1_subset_1(F_233, k1_zfmisc_1(k2_zfmisc_1(C_232, D_236))) | ~m1_subset_1(E_234, k1_zfmisc_1(k2_zfmisc_1(A_237, B_235))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.52/1.61  tff(c_1830, plain, (![A_314, B_315, A_316, E_317]: (k4_relset_1(A_314, B_315, A_316, A_316, E_317, k6_partfun1(A_316))=k5_relat_1(E_317, k6_partfun1(A_316)) | ~m1_subset_1(E_317, k1_zfmisc_1(k2_zfmisc_1(A_314, B_315))))), inference(resolution, [status(thm)], [c_39, c_1218])).
% 3.52/1.61  tff(c_1852, plain, (![A_316]: (k4_relset_1('#skF_1', '#skF_2', A_316, A_316, '#skF_3', k6_partfun1(A_316))=k5_relat_1('#skF_3', k6_partfun1(A_316)))), inference(resolution, [status(thm)], [c_38, c_1830])).
% 3.52/1.61  tff(c_183, plain, (![A_69, B_70, D_71]: (r2_relset_1(A_69, B_70, D_71, D_71) | ~m1_subset_1(D_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.52/1.61  tff(c_193, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_183])).
% 3.52/1.61  tff(c_195, plain, (![A_72, B_73, C_74]: (k1_relset_1(A_72, B_73, C_74)=k1_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.52/1.61  tff(c_208, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_195])).
% 3.52/1.61  tff(c_268, plain, (![A_90, B_91, C_92]: (m1_subset_1(k1_relset_1(A_90, B_91, C_92), k1_zfmisc_1(A_90)) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.52/1.61  tff(c_295, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_208, c_268])).
% 3.52/1.61  tff(c_305, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_295])).
% 3.52/1.61  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.52/1.61  tff(c_313, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_305, c_2])).
% 3.52/1.61  tff(c_14, plain, (![A_10, B_11]: (k5_relat_1(k6_relat_1(A_10), B_11)=B_11 | ~r1_tarski(k1_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.52/1.61  tff(c_41, plain, (![A_10, B_11]: (k5_relat_1(k6_partfun1(A_10), B_11)=B_11 | ~r1_tarski(k1_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_14])).
% 3.52/1.61  tff(c_316, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_313, c_41])).
% 3.52/1.61  tff(c_322, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_316])).
% 3.52/1.61  tff(c_400, plain, (![C_99, D_103, B_102, A_104, F_100, E_101]: (k4_relset_1(A_104, B_102, C_99, D_103, E_101, F_100)=k5_relat_1(E_101, F_100) | ~m1_subset_1(F_100, k1_zfmisc_1(k2_zfmisc_1(C_99, D_103))) | ~m1_subset_1(E_101, k1_zfmisc_1(k2_zfmisc_1(A_104, B_102))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.52/1.61  tff(c_494, plain, (![A_116, B_117, E_118]: (k4_relset_1(A_116, B_117, '#skF_1', '#skF_2', E_118, '#skF_3')=k5_relat_1(E_118, '#skF_3') | ~m1_subset_1(E_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(resolution, [status(thm)], [c_38, c_400])).
% 3.52/1.61  tff(c_516, plain, (![A_33]: (k4_relset_1(A_33, A_33, '#skF_1', '#skF_2', k6_partfun1(A_33), '#skF_3')=k5_relat_1(k6_partfun1(A_33), '#skF_3'))), inference(resolution, [status(thm)], [c_39, c_494])).
% 3.52/1.61  tff(c_36, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.52/1.61  tff(c_85, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_36])).
% 3.52/1.61  tff(c_621, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_516, c_85])).
% 3.52/1.61  tff(c_624, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_193, c_322, c_621])).
% 3.52/1.61  tff(c_625, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_36])).
% 3.52/1.61  tff(c_1853, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1852, c_625])).
% 3.52/1.61  tff(c_1865, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3') | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_756, c_1853])).
% 3.52/1.61  tff(c_1868, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_654, c_735, c_1865])).
% 3.52/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.61  
% 3.52/1.61  Inference rules
% 3.52/1.61  ----------------------
% 3.52/1.61  #Ref     : 0
% 3.52/1.61  #Sup     : 375
% 3.52/1.61  #Fact    : 0
% 3.52/1.61  #Define  : 0
% 3.52/1.61  #Split   : 6
% 3.52/1.61  #Chain   : 0
% 3.52/1.61  #Close   : 0
% 3.52/1.61  
% 3.52/1.61  Ordering : KBO
% 3.52/1.61  
% 3.52/1.61  Simplification rules
% 3.52/1.61  ----------------------
% 3.52/1.61  #Subsume      : 27
% 3.52/1.61  #Demod        : 152
% 3.52/1.61  #Tautology    : 120
% 3.52/1.61  #SimpNegUnit  : 0
% 3.52/1.61  #BackRed      : 6
% 3.52/1.61  
% 3.52/1.61  #Partial instantiations: 0
% 3.52/1.61  #Strategies tried      : 1
% 3.52/1.61  
% 3.52/1.61  Timing (in seconds)
% 3.52/1.61  ----------------------
% 3.52/1.61  Preprocessing        : 0.32
% 3.52/1.61  Parsing              : 0.18
% 3.52/1.61  CNF conversion       : 0.02
% 3.52/1.61  Main loop            : 0.53
% 3.52/1.61  Inferencing          : 0.21
% 3.52/1.61  Reduction            : 0.16
% 3.52/1.61  Demodulation         : 0.12
% 3.52/1.61  BG Simplification    : 0.03
% 3.52/1.61  Subsumption          : 0.08
% 3.52/1.61  Abstraction          : 0.03
% 3.52/1.61  MUC search           : 0.00
% 3.52/1.61  Cooper               : 0.00
% 3.52/1.61  Total                : 0.89
% 3.52/1.61  Index Insertion      : 0.00
% 3.52/1.61  Index Deletion       : 0.00
% 3.52/1.61  Index Matching       : 0.00
% 3.52/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
