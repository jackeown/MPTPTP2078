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
% DateTime   : Thu Dec  3 10:17:37 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 362 expanded)
%              Number of leaves         :   40 ( 130 expanded)
%              Depth                    :   11
%              Number of atoms          :  195 (1111 expanded)
%              Number of equality atoms :   49 ( 151 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_140,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ~ v1_xboole_0(D)
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,A,D)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,D))) )
           => ( ( r1_tarski(B,A)
                & r1_tarski(k7_relset_1(A,D,E,B),C) )
             => ( v1_funct_1(k2_partfun1(A,D,E,B))
                & v1_funct_2(k2_partfun1(A,D,E,B),B,C)
                & m1_subset_1(k2_partfun1(A,D,E,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).

tff(f_107,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( k1_relset_1(A,B,C) = A
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_849,plain,(
    ! [A_203,B_204,C_205,D_206] :
      ( k2_partfun1(A_203,B_204,C_205,D_206) = k7_relat_1(C_205,D_206)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_203,B_204)))
      | ~ v1_funct_1(C_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_858,plain,(
    ! [D_206] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_206) = k7_relat_1('#skF_5',D_206)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_849])).

tff(c_866,plain,(
    ! [D_206] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_206) = k7_relat_1('#skF_5',D_206) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_858])).

tff(c_85,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_94,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_85])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_9,A_8)),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_351,plain,(
    ! [A_122,B_123,C_124,D_125] :
      ( k7_relset_1(A_122,B_123,C_124,D_125) = k9_relat_1(C_124,D_125)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_358,plain,(
    ! [D_125] : k7_relset_1('#skF_1','#skF_4','#skF_5',D_125) = k9_relat_1('#skF_5',D_125) ),
    inference(resolution,[status(thm)],[c_56,c_351])).

tff(c_52,plain,(
    r1_tarski(k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_359,plain,(
    r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_52])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( k2_relat_1(k7_relat_1(B_7,A_6)) = k9_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k7_relat_1(B_11,A_10),B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_75,plain,(
    ! [B_50,A_51] :
      ( v1_relat_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_95,plain,(
    ! [A_55,B_56] :
      ( v1_relat_1(A_55)
      | ~ v1_relat_1(B_56)
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(resolution,[status(thm)],[c_6,c_75])).

tff(c_112,plain,(
    ! [B_11,A_10] :
      ( v1_relat_1(k7_relat_1(B_11,A_10))
      | ~ v1_relat_1(B_11) ) ),
    inference(resolution,[status(thm)],[c_14,c_95])).

tff(c_447,plain,(
    ! [C_145,A_146,B_147] :
      ( m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147)))
      | ~ r1_tarski(k2_relat_1(C_145),B_147)
      | ~ r1_tarski(k1_relat_1(C_145),A_146)
      | ~ v1_relat_1(C_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_409,plain,(
    ! [A_137,B_138,C_139,D_140] :
      ( k2_partfun1(A_137,B_138,C_139,D_140) = k7_relat_1(C_139,D_140)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138)))
      | ~ v1_funct_1(C_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_414,plain,(
    ! [D_140] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_140) = k7_relat_1('#skF_5',D_140)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_409])).

tff(c_418,plain,(
    ! [D_140] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_140) = k7_relat_1('#skF_5',D_140) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_414])).

tff(c_212,plain,(
    ! [A_83,B_84,C_85,D_86] :
      ( v1_funct_1(k2_partfun1(A_83,B_84,C_85,D_86))
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ v1_funct_1(C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_217,plain,(
    ! [D_86] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_86))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_212])).

tff(c_221,plain,(
    ! [D_86] : v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_86)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_217])).

tff(c_50,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_118,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_224,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_118])).

tff(c_225,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_267,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_225])).

tff(c_421,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_267])).

tff(c_485,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_447,c_421])).

tff(c_538,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_485])).

tff(c_541,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_112,c_538])).

tff(c_545,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_541])).

tff(c_546,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_485])).

tff(c_548,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_546])).

tff(c_551,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_548])).

tff(c_554,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_359,c_551])).

tff(c_555,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_546])).

tff(c_589,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_555])).

tff(c_593,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_589])).

tff(c_594,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_225])).

tff(c_874,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_866,c_594])).

tff(c_721,plain,(
    ! [A_181,B_182,C_183,D_184] :
      ( v1_funct_1(k2_partfun1(A_181,B_182,C_183,D_184))
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182)))
      | ~ v1_funct_1(C_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_728,plain,(
    ! [D_184] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_184))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_721])).

tff(c_735,plain,(
    ! [D_184] : v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_184)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_728])).

tff(c_870,plain,(
    ! [D_184] : v1_funct_1(k7_relat_1('#skF_5',D_184)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_866,c_735])).

tff(c_54,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_58,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_619,plain,(
    ! [A_160,B_161,C_162] :
      ( k1_relset_1(A_160,B_161,C_162) = k1_relat_1(C_162)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_632,plain,(
    k1_relset_1('#skF_1','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_619])).

tff(c_945,plain,(
    ! [B_210,A_211,C_212] :
      ( k1_xboole_0 = B_210
      | k1_relset_1(A_211,B_210,C_212) = A_211
      | ~ v1_funct_2(C_212,A_211,B_210)
      | ~ m1_subset_1(C_212,k1_zfmisc_1(k2_zfmisc_1(A_211,B_210))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_958,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_1','#skF_4','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_945])).

tff(c_965,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_632,c_958])).

tff(c_966,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_965])).

tff(c_16,plain,(
    ! [B_13,A_12] :
      ( k1_relat_1(k7_relat_1(B_13,A_12)) = A_12
      | ~ r1_tarski(A_12,k1_relat_1(B_13))
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_971,plain,(
    ! [A_12] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_12)) = A_12
      | ~ r1_tarski(A_12,'#skF_1')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_966,c_16])).

tff(c_975,plain,(
    ! [A_12] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_12)) = A_12
      | ~ r1_tarski(A_12,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_971])).

tff(c_595,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_225])).

tff(c_630,plain,(
    k1_relset_1('#skF_2','#skF_3',k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) = k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_595,c_619])).

tff(c_868,plain,(
    k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) = k1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_866,c_866,c_630])).

tff(c_873,plain,(
    m1_subset_1(k7_relat_1('#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_866,c_595])).

tff(c_1028,plain,(
    ! [B_217,C_218,A_219] :
      ( k1_xboole_0 = B_217
      | v1_funct_2(C_218,A_219,B_217)
      | k1_relset_1(A_219,B_217,C_218) != A_219
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(A_219,B_217))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1031,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_873,c_1028])).

tff(c_1043,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3')
    | k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_868,c_1031])).

tff(c_1044,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_874,c_1043])).

tff(c_1050,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1044])).

tff(c_1053,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_975,c_1050])).

tff(c_1057,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1053])).

tff(c_1059,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_2')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1044])).

tff(c_1084,plain,(
    k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1059,c_868])).

tff(c_1161,plain,(
    ! [C_223,A_224,B_225] :
      ( v1_funct_2(C_223,A_224,B_225)
      | k1_relset_1(A_224,B_225,C_223) != A_224
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(A_224,B_225)))
      | ~ v1_funct_1(C_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1164,plain,
    ( v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) != '#skF_2'
    | ~ v1_funct_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_873,c_1161])).

tff(c_1177,plain,(
    v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_870,c_1084,c_1164])).

tff(c_1179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_874,c_1177])).

tff(c_1180,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_965])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1191,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1180,c_2])).

tff(c_1193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1191])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:16:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.50  
% 3.15/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.50  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.15/1.50  
% 3.15/1.50  %Foreground sorts:
% 3.15/1.50  
% 3.15/1.50  
% 3.15/1.50  %Background operators:
% 3.15/1.50  
% 3.15/1.50  
% 3.15/1.50  %Foreground operators:
% 3.15/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.15/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.50  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.15/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.15/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.15/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.15/1.50  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.15/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.15/1.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.15/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.15/1.50  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.15/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.15/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.15/1.50  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.15/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.15/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.15/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.15/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.15/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.50  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.15/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.15/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.15/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.15/1.50  
% 3.15/1.52  tff(f_140, negated_conjecture, ~(![A, B, C, D]: (~v1_xboole_0(D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, A, D)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, D)))) => ((r1_tarski(B, A) & r1_tarski(k7_relset_1(A, D, E, B), C)) => ((v1_funct_1(k2_partfun1(A, D, E, B)) & v1_funct_2(k2_partfun1(A, D, E, B), B, C)) & m1_subset_1(k2_partfun1(A, D, E, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_funct_2)).
% 3.15/1.52  tff(f_107, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.15/1.52  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.15/1.52  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 3.15/1.52  tff(f_67, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.15/1.52  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.15/1.52  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 3.15/1.52  tff(f_30, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.15/1.52  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.15/1.52  tff(f_75, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 3.15/1.52  tff(f_101, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 3.15/1.52  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.15/1.52  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.15/1.52  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 3.15/1.52  tff(f_119, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_funct_2)).
% 3.15/1.52  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.15/1.52  tff(c_62, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.15/1.52  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.15/1.52  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.15/1.52  tff(c_849, plain, (![A_203, B_204, C_205, D_206]: (k2_partfun1(A_203, B_204, C_205, D_206)=k7_relat_1(C_205, D_206) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_203, B_204))) | ~v1_funct_1(C_205))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.15/1.52  tff(c_858, plain, (![D_206]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_206)=k7_relat_1('#skF_5', D_206) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_849])).
% 3.15/1.52  tff(c_866, plain, (![D_206]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_206)=k7_relat_1('#skF_5', D_206))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_858])).
% 3.15/1.52  tff(c_85, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.15/1.52  tff(c_94, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_85])).
% 3.15/1.52  tff(c_12, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(k7_relat_1(B_9, A_8)), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.15/1.52  tff(c_351, plain, (![A_122, B_123, C_124, D_125]: (k7_relset_1(A_122, B_123, C_124, D_125)=k9_relat_1(C_124, D_125) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.15/1.52  tff(c_358, plain, (![D_125]: (k7_relset_1('#skF_1', '#skF_4', '#skF_5', D_125)=k9_relat_1('#skF_5', D_125))), inference(resolution, [status(thm)], [c_56, c_351])).
% 3.15/1.52  tff(c_52, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.15/1.52  tff(c_359, plain, (r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_358, c_52])).
% 3.15/1.52  tff(c_10, plain, (![B_7, A_6]: (k2_relat_1(k7_relat_1(B_7, A_6))=k9_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.15/1.52  tff(c_14, plain, (![B_11, A_10]: (r1_tarski(k7_relat_1(B_11, A_10), B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.15/1.52  tff(c_6, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.15/1.52  tff(c_75, plain, (![B_50, A_51]: (v1_relat_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.15/1.52  tff(c_95, plain, (![A_55, B_56]: (v1_relat_1(A_55) | ~v1_relat_1(B_56) | ~r1_tarski(A_55, B_56))), inference(resolution, [status(thm)], [c_6, c_75])).
% 3.15/1.52  tff(c_112, plain, (![B_11, A_10]: (v1_relat_1(k7_relat_1(B_11, A_10)) | ~v1_relat_1(B_11))), inference(resolution, [status(thm)], [c_14, c_95])).
% 3.15/1.52  tff(c_447, plain, (![C_145, A_146, B_147]: (m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))) | ~r1_tarski(k2_relat_1(C_145), B_147) | ~r1_tarski(k1_relat_1(C_145), A_146) | ~v1_relat_1(C_145))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.15/1.52  tff(c_409, plain, (![A_137, B_138, C_139, D_140]: (k2_partfun1(A_137, B_138, C_139, D_140)=k7_relat_1(C_139, D_140) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))) | ~v1_funct_1(C_139))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.15/1.52  tff(c_414, plain, (![D_140]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_140)=k7_relat_1('#skF_5', D_140) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_409])).
% 3.15/1.52  tff(c_418, plain, (![D_140]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_140)=k7_relat_1('#skF_5', D_140))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_414])).
% 3.15/1.52  tff(c_212, plain, (![A_83, B_84, C_85, D_86]: (v1_funct_1(k2_partfun1(A_83, B_84, C_85, D_86)) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~v1_funct_1(C_85))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.15/1.52  tff(c_217, plain, (![D_86]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_86)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_212])).
% 3.15/1.52  tff(c_221, plain, (![D_86]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_86)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_217])).
% 3.15/1.52  tff(c_50, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.15/1.52  tff(c_118, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_50])).
% 3.15/1.52  tff(c_224, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_221, c_118])).
% 3.15/1.52  tff(c_225, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_50])).
% 3.15/1.52  tff(c_267, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_225])).
% 3.15/1.52  tff(c_421, plain, (~m1_subset_1(k7_relat_1('#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_418, c_267])).
% 3.15/1.52  tff(c_485, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_447, c_421])).
% 3.15/1.52  tff(c_538, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_485])).
% 3.15/1.52  tff(c_541, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_112, c_538])).
% 3.15/1.52  tff(c_545, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_541])).
% 3.15/1.52  tff(c_546, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_485])).
% 3.15/1.52  tff(c_548, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3')), inference(splitLeft, [status(thm)], [c_546])).
% 3.15/1.52  tff(c_551, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_10, c_548])).
% 3.15/1.52  tff(c_554, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_359, c_551])).
% 3.15/1.52  tff(c_555, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2')), inference(splitRight, [status(thm)], [c_546])).
% 3.15/1.52  tff(c_589, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_12, c_555])).
% 3.15/1.52  tff(c_593, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_589])).
% 3.15/1.52  tff(c_594, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_225])).
% 3.15/1.52  tff(c_874, plain, (~v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_866, c_594])).
% 3.15/1.52  tff(c_721, plain, (![A_181, B_182, C_183, D_184]: (v1_funct_1(k2_partfun1(A_181, B_182, C_183, D_184)) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))) | ~v1_funct_1(C_183))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.15/1.52  tff(c_728, plain, (![D_184]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_184)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_721])).
% 3.15/1.52  tff(c_735, plain, (![D_184]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_184)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_728])).
% 3.15/1.52  tff(c_870, plain, (![D_184]: (v1_funct_1(k7_relat_1('#skF_5', D_184)))), inference(demodulation, [status(thm), theory('equality')], [c_866, c_735])).
% 3.15/1.52  tff(c_54, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.15/1.52  tff(c_58, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.15/1.52  tff(c_619, plain, (![A_160, B_161, C_162]: (k1_relset_1(A_160, B_161, C_162)=k1_relat_1(C_162) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.15/1.52  tff(c_632, plain, (k1_relset_1('#skF_1', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_619])).
% 3.15/1.52  tff(c_945, plain, (![B_210, A_211, C_212]: (k1_xboole_0=B_210 | k1_relset_1(A_211, B_210, C_212)=A_211 | ~v1_funct_2(C_212, A_211, B_210) | ~m1_subset_1(C_212, k1_zfmisc_1(k2_zfmisc_1(A_211, B_210))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.15/1.52  tff(c_958, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_1', '#skF_4', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_945])).
% 3.15/1.52  tff(c_965, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_632, c_958])).
% 3.15/1.52  tff(c_966, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_965])).
% 3.15/1.52  tff(c_16, plain, (![B_13, A_12]: (k1_relat_1(k7_relat_1(B_13, A_12))=A_12 | ~r1_tarski(A_12, k1_relat_1(B_13)) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.15/1.52  tff(c_971, plain, (![A_12]: (k1_relat_1(k7_relat_1('#skF_5', A_12))=A_12 | ~r1_tarski(A_12, '#skF_1') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_966, c_16])).
% 3.15/1.52  tff(c_975, plain, (![A_12]: (k1_relat_1(k7_relat_1('#skF_5', A_12))=A_12 | ~r1_tarski(A_12, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_971])).
% 3.15/1.52  tff(c_595, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_225])).
% 3.15/1.52  tff(c_630, plain, (k1_relset_1('#skF_2', '#skF_3', k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_595, c_619])).
% 3.15/1.52  tff(c_868, plain, (k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))=k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_866, c_866, c_630])).
% 3.15/1.52  tff(c_873, plain, (m1_subset_1(k7_relat_1('#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_866, c_595])).
% 3.15/1.52  tff(c_1028, plain, (![B_217, C_218, A_219]: (k1_xboole_0=B_217 | v1_funct_2(C_218, A_219, B_217) | k1_relset_1(A_219, B_217, C_218)!=A_219 | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(A_219, B_217))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.15/1.52  tff(c_1031, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(resolution, [status(thm)], [c_873, c_1028])).
% 3.15/1.52  tff(c_1043, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3') | k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_868, c_1031])).
% 3.15/1.52  tff(c_1044, plain, (k1_xboole_0='#skF_3' | k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_874, c_1043])).
% 3.15/1.52  tff(c_1050, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_1044])).
% 3.15/1.52  tff(c_1053, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_975, c_1050])).
% 3.15/1.52  tff(c_1057, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_1053])).
% 3.15/1.52  tff(c_1059, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))='#skF_2'), inference(splitRight, [status(thm)], [c_1044])).
% 3.15/1.52  tff(c_1084, plain, (k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1059, c_868])).
% 3.15/1.52  tff(c_1161, plain, (![C_223, A_224, B_225]: (v1_funct_2(C_223, A_224, B_225) | k1_relset_1(A_224, B_225, C_223)!=A_224 | ~m1_subset_1(C_223, k1_zfmisc_1(k2_zfmisc_1(A_224, B_225))) | ~v1_funct_1(C_223))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.15/1.52  tff(c_1164, plain, (v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))!='#skF_2' | ~v1_funct_1(k7_relat_1('#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_873, c_1161])).
% 3.15/1.52  tff(c_1177, plain, (v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_870, c_1084, c_1164])).
% 3.15/1.52  tff(c_1179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_874, c_1177])).
% 3.15/1.52  tff(c_1180, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_965])).
% 3.15/1.52  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.15/1.52  tff(c_1191, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1180, c_2])).
% 3.15/1.52  tff(c_1193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_1191])).
% 3.15/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.52  
% 3.15/1.52  Inference rules
% 3.15/1.52  ----------------------
% 3.15/1.52  #Ref     : 0
% 3.15/1.52  #Sup     : 231
% 3.15/1.52  #Fact    : 0
% 3.15/1.52  #Define  : 0
% 3.15/1.52  #Split   : 10
% 3.15/1.52  #Chain   : 0
% 3.15/1.52  #Close   : 0
% 3.15/1.52  
% 3.15/1.52  Ordering : KBO
% 3.15/1.52  
% 3.15/1.52  Simplification rules
% 3.15/1.52  ----------------------
% 3.15/1.52  #Subsume      : 10
% 3.15/1.52  #Demod        : 165
% 3.15/1.52  #Tautology    : 86
% 3.15/1.52  #SimpNegUnit  : 3
% 3.15/1.52  #BackRed      : 37
% 3.15/1.52  
% 3.15/1.52  #Partial instantiations: 0
% 3.15/1.52  #Strategies tried      : 1
% 3.15/1.52  
% 3.15/1.52  Timing (in seconds)
% 3.15/1.52  ----------------------
% 3.15/1.52  Preprocessing        : 0.32
% 3.15/1.52  Parsing              : 0.17
% 3.15/1.52  CNF conversion       : 0.02
% 3.15/1.52  Main loop            : 0.42
% 3.15/1.52  Inferencing          : 0.15
% 3.15/1.52  Reduction            : 0.13
% 3.15/1.52  Demodulation         : 0.09
% 3.15/1.52  BG Simplification    : 0.03
% 3.15/1.52  Subsumption          : 0.07
% 3.15/1.52  Abstraction          : 0.03
% 3.15/1.53  MUC search           : 0.00
% 3.15/1.53  Cooper               : 0.00
% 3.15/1.53  Total                : 0.78
% 3.15/1.53  Index Insertion      : 0.00
% 3.15/1.53  Index Deletion       : 0.00
% 3.15/1.53  Index Matching       : 0.00
% 3.15/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
