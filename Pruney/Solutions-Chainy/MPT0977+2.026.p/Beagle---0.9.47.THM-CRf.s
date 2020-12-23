%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:49 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
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
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r2_relset_1(A,B,k4_relset_1(A,A,A,B,k6_partfun1(A),C),C)
          & r2_relset_1(A,B,k4_relset_1(A,B,B,B,C,k6_partfun1(B)),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_88,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_86,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_736,plain,(
    ! [A_164,B_165,D_166] :
      ( r2_relset_1(A_164,B_165,D_166,D_166)
      | ~ m1_subset_1(D_166,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_746,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_736])).

tff(c_12,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

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

tff(c_790,plain,(
    ! [A_180,B_181,C_182] :
      ( k2_relset_1(A_180,B_181,C_182) = k2_relat_1(C_182)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_803,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_790])).

tff(c_845,plain,(
    ! [A_192,B_193,C_194] :
      ( m1_subset_1(k2_relset_1(A_192,B_193,C_194),k1_zfmisc_1(B_193))
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(A_192,B_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_872,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_803,c_845])).

tff(c_882,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_872])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_890,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_882,c_2])).

tff(c_34,plain,(
    ! [A_34] : k6_relat_1(A_34) = k6_partfun1(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_16,plain,(
    ! [B_13,A_12] :
      ( k5_relat_1(B_13,k6_relat_1(A_12)) = B_13
      | ~ r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_40,plain,(
    ! [B_13,A_12] :
      ( k5_relat_1(B_13,k6_partfun1(A_12)) = B_13
      | ~ r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_16])).

tff(c_893,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_890,c_40])).

tff(c_899,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_893])).

tff(c_32,plain,(
    ! [A_33] : m1_subset_1(k6_relat_1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_39,plain,(
    ! [A_33] : m1_subset_1(k6_partfun1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32])).

tff(c_1237,plain,(
    ! [C_233,F_234,D_237,E_235,B_236,A_238] :
      ( k4_relset_1(A_238,B_236,C_233,D_237,E_235,F_234) = k5_relat_1(E_235,F_234)
      | ~ m1_subset_1(F_234,k1_zfmisc_1(k2_zfmisc_1(C_233,D_237)))
      | ~ m1_subset_1(E_235,k1_zfmisc_1(k2_zfmisc_1(A_238,B_236))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1751,plain,(
    ! [A_298,B_299,A_300,E_301] :
      ( k4_relset_1(A_298,B_299,A_300,A_300,E_301,k6_partfun1(A_300)) = k5_relat_1(E_301,k6_partfun1(A_300))
      | ~ m1_subset_1(E_301,k1_zfmisc_1(k2_zfmisc_1(A_298,B_299))) ) ),
    inference(resolution,[status(thm)],[c_39,c_1237])).

tff(c_1773,plain,(
    ! [A_300] : k4_relset_1('#skF_1','#skF_2',A_300,A_300,'#skF_3',k6_partfun1(A_300)) = k5_relat_1('#skF_3',k6_partfun1(A_300)) ),
    inference(resolution,[status(thm)],[c_38,c_1751])).

tff(c_141,plain,(
    ! [C_60,A_61,B_62] :
      ( v4_relat_1(C_60,A_61)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_154,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_141])).

tff(c_183,plain,(
    ! [A_69,B_70,D_71] :
      ( r2_relset_1(A_69,B_70,D_71,D_71)
      | ~ m1_subset_1(D_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_193,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_183])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k5_relat_1(k6_relat_1(A_10),B_11) = B_11
      | ~ r1_tarski(k1_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_237,plain,(
    ! [A_81,B_82] :
      ( k5_relat_1(k6_partfun1(A_81),B_82) = B_82
      | ~ r1_tarski(k1_relat_1(B_82),A_81)
      | ~ v1_relat_1(B_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_14])).

tff(c_241,plain,(
    ! [A_6,B_7] :
      ( k5_relat_1(k6_partfun1(A_6),B_7) = B_7
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_237])).

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

tff(c_618,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_516,c_85])).

tff(c_630,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3')
    | ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_618])).

tff(c_633,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_154,c_193,c_630])).

tff(c_634,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1774,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1773,c_634])).

tff(c_1777,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_746,c_899,c_1774])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:37:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.65/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/1.64  
% 3.65/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/1.65  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.65/1.65  
% 3.65/1.65  %Foreground sorts:
% 3.65/1.65  
% 3.65/1.65  
% 3.65/1.65  %Background operators:
% 3.65/1.65  
% 3.65/1.65  
% 3.65/1.65  %Foreground operators:
% 3.65/1.65  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.65/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.65/1.65  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.65/1.65  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.65/1.65  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.65/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.65/1.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.65/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.65/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.65/1.65  tff('#skF_1', type, '#skF_1': $i).
% 3.65/1.65  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.65/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.65/1.65  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.65/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.65/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.65/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.65/1.65  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.65/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.65/1.65  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.65/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.65/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.65/1.65  
% 3.65/1.66  tff(f_95, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_2)).
% 3.65/1.66  tff(f_84, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.65/1.66  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.65/1.66  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.65/1.66  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.65/1.66  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.65/1.66  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.65/1.66  tff(f_88, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.65/1.66  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 3.65/1.66  tff(f_86, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 3.65/1.66  tff(f_76, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 3.65/1.66  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.65/1.66  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.65/1.66  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 3.65/1.66  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.65/1.66  tff(c_736, plain, (![A_164, B_165, D_166]: (r2_relset_1(A_164, B_165, D_166, D_166) | ~m1_subset_1(D_166, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.65/1.66  tff(c_746, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_736])).
% 3.65/1.66  tff(c_12, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.65/1.66  tff(c_68, plain, (![B_44, A_45]: (v1_relat_1(B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.65/1.66  tff(c_77, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_68])).
% 3.65/1.66  tff(c_84, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_77])).
% 3.65/1.66  tff(c_790, plain, (![A_180, B_181, C_182]: (k2_relset_1(A_180, B_181, C_182)=k2_relat_1(C_182) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.65/1.66  tff(c_803, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_790])).
% 3.65/1.66  tff(c_845, plain, (![A_192, B_193, C_194]: (m1_subset_1(k2_relset_1(A_192, B_193, C_194), k1_zfmisc_1(B_193)) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(A_192, B_193))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.65/1.66  tff(c_872, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_803, c_845])).
% 3.65/1.66  tff(c_882, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_872])).
% 3.65/1.66  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.65/1.66  tff(c_890, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_882, c_2])).
% 3.65/1.66  tff(c_34, plain, (![A_34]: (k6_relat_1(A_34)=k6_partfun1(A_34))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.65/1.66  tff(c_16, plain, (![B_13, A_12]: (k5_relat_1(B_13, k6_relat_1(A_12))=B_13 | ~r1_tarski(k2_relat_1(B_13), A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.65/1.66  tff(c_40, plain, (![B_13, A_12]: (k5_relat_1(B_13, k6_partfun1(A_12))=B_13 | ~r1_tarski(k2_relat_1(B_13), A_12) | ~v1_relat_1(B_13))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_16])).
% 3.65/1.66  tff(c_893, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_890, c_40])).
% 3.65/1.66  tff(c_899, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_893])).
% 3.65/1.66  tff(c_32, plain, (![A_33]: (m1_subset_1(k6_relat_1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.65/1.66  tff(c_39, plain, (![A_33]: (m1_subset_1(k6_partfun1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32])).
% 3.65/1.66  tff(c_1237, plain, (![C_233, F_234, D_237, E_235, B_236, A_238]: (k4_relset_1(A_238, B_236, C_233, D_237, E_235, F_234)=k5_relat_1(E_235, F_234) | ~m1_subset_1(F_234, k1_zfmisc_1(k2_zfmisc_1(C_233, D_237))) | ~m1_subset_1(E_235, k1_zfmisc_1(k2_zfmisc_1(A_238, B_236))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.65/1.66  tff(c_1751, plain, (![A_298, B_299, A_300, E_301]: (k4_relset_1(A_298, B_299, A_300, A_300, E_301, k6_partfun1(A_300))=k5_relat_1(E_301, k6_partfun1(A_300)) | ~m1_subset_1(E_301, k1_zfmisc_1(k2_zfmisc_1(A_298, B_299))))), inference(resolution, [status(thm)], [c_39, c_1237])).
% 3.65/1.66  tff(c_1773, plain, (![A_300]: (k4_relset_1('#skF_1', '#skF_2', A_300, A_300, '#skF_3', k6_partfun1(A_300))=k5_relat_1('#skF_3', k6_partfun1(A_300)))), inference(resolution, [status(thm)], [c_38, c_1751])).
% 3.65/1.66  tff(c_141, plain, (![C_60, A_61, B_62]: (v4_relat_1(C_60, A_61) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.65/1.66  tff(c_154, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_141])).
% 3.65/1.66  tff(c_183, plain, (![A_69, B_70, D_71]: (r2_relset_1(A_69, B_70, D_71, D_71) | ~m1_subset_1(D_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.65/1.66  tff(c_193, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_183])).
% 3.65/1.66  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.65/1.66  tff(c_14, plain, (![A_10, B_11]: (k5_relat_1(k6_relat_1(A_10), B_11)=B_11 | ~r1_tarski(k1_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.65/1.66  tff(c_237, plain, (![A_81, B_82]: (k5_relat_1(k6_partfun1(A_81), B_82)=B_82 | ~r1_tarski(k1_relat_1(B_82), A_81) | ~v1_relat_1(B_82))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_14])).
% 3.65/1.66  tff(c_241, plain, (![A_6, B_7]: (k5_relat_1(k6_partfun1(A_6), B_7)=B_7 | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_10, c_237])).
% 3.65/1.66  tff(c_400, plain, (![C_99, D_103, B_102, A_104, F_100, E_101]: (k4_relset_1(A_104, B_102, C_99, D_103, E_101, F_100)=k5_relat_1(E_101, F_100) | ~m1_subset_1(F_100, k1_zfmisc_1(k2_zfmisc_1(C_99, D_103))) | ~m1_subset_1(E_101, k1_zfmisc_1(k2_zfmisc_1(A_104, B_102))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.65/1.66  tff(c_494, plain, (![A_116, B_117, E_118]: (k4_relset_1(A_116, B_117, '#skF_1', '#skF_2', E_118, '#skF_3')=k5_relat_1(E_118, '#skF_3') | ~m1_subset_1(E_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(resolution, [status(thm)], [c_38, c_400])).
% 3.65/1.66  tff(c_516, plain, (![A_33]: (k4_relset_1(A_33, A_33, '#skF_1', '#skF_2', k6_partfun1(A_33), '#skF_3')=k5_relat_1(k6_partfun1(A_33), '#skF_3'))), inference(resolution, [status(thm)], [c_39, c_494])).
% 3.65/1.66  tff(c_36, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.65/1.66  tff(c_85, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_36])).
% 3.65/1.66  tff(c_618, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_516, c_85])).
% 3.65/1.66  tff(c_630, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3') | ~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_241, c_618])).
% 3.65/1.66  tff(c_633, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_154, c_193, c_630])).
% 3.65/1.66  tff(c_634, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_36])).
% 3.65/1.66  tff(c_1774, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1773, c_634])).
% 3.65/1.66  tff(c_1777, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_746, c_899, c_1774])).
% 3.65/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/1.66  
% 3.65/1.66  Inference rules
% 3.65/1.66  ----------------------
% 3.65/1.66  #Ref     : 0
% 3.65/1.66  #Sup     : 360
% 3.65/1.66  #Fact    : 0
% 3.65/1.66  #Define  : 0
% 3.65/1.66  #Split   : 6
% 3.65/1.66  #Chain   : 0
% 3.65/1.66  #Close   : 0
% 3.65/1.66  
% 3.65/1.66  Ordering : KBO
% 3.65/1.66  
% 3.65/1.66  Simplification rules
% 3.65/1.66  ----------------------
% 3.65/1.66  #Subsume      : 23
% 3.65/1.66  #Demod        : 149
% 3.65/1.66  #Tautology    : 117
% 3.65/1.66  #SimpNegUnit  : 0
% 3.65/1.66  #BackRed      : 6
% 3.65/1.66  
% 3.65/1.66  #Partial instantiations: 0
% 3.65/1.66  #Strategies tried      : 1
% 3.65/1.66  
% 3.65/1.66  Timing (in seconds)
% 3.65/1.66  ----------------------
% 3.65/1.67  Preprocessing        : 0.33
% 3.65/1.67  Parsing              : 0.19
% 3.65/1.67  CNF conversion       : 0.02
% 3.65/1.67  Main loop            : 0.53
% 3.65/1.67  Inferencing          : 0.21
% 3.65/1.67  Reduction            : 0.17
% 3.65/1.67  Demodulation         : 0.12
% 3.65/1.67  BG Simplification    : 0.03
% 3.65/1.67  Subsumption          : 0.08
% 3.65/1.67  Abstraction          : 0.03
% 3.65/1.67  MUC search           : 0.00
% 3.65/1.67  Cooper               : 0.00
% 3.65/1.67  Total                : 0.90
% 3.65/1.67  Index Insertion      : 0.00
% 3.65/1.67  Index Deletion       : 0.00
% 3.65/1.67  Index Matching       : 0.00
% 3.65/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
