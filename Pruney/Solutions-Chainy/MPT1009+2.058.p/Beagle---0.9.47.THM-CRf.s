%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:50 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 223 expanded)
%              Number of leaves         :   43 (  93 expanded)
%              Depth                    :   13
%              Number of atoms          :  137 ( 448 expanded)
%              Number of equality atoms :   60 ( 145 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_111,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_81,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_132,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_145,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_132])).

tff(c_30,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k9_relat_1(B_19,A_18),k2_relat_1(B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_42,plain,(
    ! [A_24] :
      ( k1_relat_1(A_24) != k1_xboole_0
      | k1_xboole_0 = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_154,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_145,c_42])).

tff(c_176,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_377,plain,(
    ! [B_106,A_107] :
      ( k1_tarski(k1_funct_1(B_106,A_107)) = k2_relat_1(B_106)
      | k1_tarski(A_107) != k1_relat_1(B_106)
      | ~ v1_funct_1(B_106)
      | ~ v1_relat_1(B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_54,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_383,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_54])).

tff(c_401,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_62,c_383])).

tff(c_417,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_401])).

tff(c_290,plain,(
    ! [C_85,A_86,B_87] :
      ( v4_relat_1(C_85,A_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_303,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_58,c_290])).

tff(c_28,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_467,plain,(
    ! [B_126,C_127,A_128] :
      ( k2_tarski(B_126,C_127) = A_128
      | k1_tarski(C_127) = A_128
      | k1_tarski(B_126) = A_128
      | k1_xboole_0 = A_128
      | ~ r1_tarski(A_128,k2_tarski(B_126,C_127)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_487,plain,(
    ! [A_1,A_128] :
      ( k2_tarski(A_1,A_1) = A_128
      | k1_tarski(A_1) = A_128
      | k1_tarski(A_1) = A_128
      | k1_xboole_0 = A_128
      | ~ r1_tarski(A_128,k1_tarski(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_467])).

tff(c_537,plain,(
    ! [A_135,A_136] :
      ( k1_tarski(A_135) = A_136
      | k1_tarski(A_135) = A_136
      | k1_tarski(A_135) = A_136
      | k1_xboole_0 = A_136
      | ~ r1_tarski(A_136,k1_tarski(A_135)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_487])).

tff(c_557,plain,(
    ! [A_137,B_138] :
      ( k1_tarski(A_137) = k1_relat_1(B_138)
      | k1_relat_1(B_138) = k1_xboole_0
      | ~ v4_relat_1(B_138,k1_tarski(A_137))
      | ~ v1_relat_1(B_138) ) ),
    inference(resolution,[status(thm)],[c_28,c_537])).

tff(c_563,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_303,c_557])).

tff(c_570,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_563])).

tff(c_572,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_417,c_570])).

tff(c_574,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_401])).

tff(c_581,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_574,c_58])).

tff(c_52,plain,(
    ! [A_33,B_34,C_35,D_36] :
      ( k7_relset_1(A_33,B_34,C_35,D_36) = k9_relat_1(C_35,D_36)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_642,plain,(
    ! [D_36] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_36) = k9_relat_1('#skF_4',D_36) ),
    inference(resolution,[status(thm)],[c_581,c_52])).

tff(c_573,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_401])).

tff(c_873,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_574,c_573])).

tff(c_874,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_642,c_873])).

tff(c_887,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_874])).

tff(c_891,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_887])).

tff(c_892,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_18,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_107,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(A_53,B_54)
      | ~ m1_subset_1(A_53,k1_zfmisc_1(B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_119,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(resolution,[status(thm)],[c_18,c_107])).

tff(c_896,plain,(
    ! [A_10] : r1_tarski('#skF_4',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_892,c_119])).

tff(c_36,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_900,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_892,c_892,c_36])).

tff(c_899,plain,(
    ! [A_10] : m1_subset_1('#skF_4',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_892,c_18])).

tff(c_998,plain,(
    ! [C_176,A_177,B_178] :
      ( v4_relat_1(C_176,A_177)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1009,plain,(
    ! [A_179] : v4_relat_1('#skF_4',A_179) ),
    inference(resolution,[status(thm)],[c_899,c_998])).

tff(c_34,plain,(
    ! [B_23,A_22] :
      ( k7_relat_1(B_23,A_22) = B_23
      | ~ v4_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1012,plain,(
    ! [A_179] :
      ( k7_relat_1('#skF_4',A_179) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1009,c_34])).

tff(c_1016,plain,(
    ! [A_180] : k7_relat_1('#skF_4',A_180) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_1012])).

tff(c_32,plain,(
    ! [B_21,A_20] :
      ( k2_relat_1(k7_relat_1(B_21,A_20)) = k9_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1021,plain,(
    ! [A_180] :
      ( k9_relat_1('#skF_4',A_180) = k2_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1016,c_32])).

tff(c_1026,plain,(
    ! [A_180] : k9_relat_1('#skF_4',A_180) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_900,c_1021])).

tff(c_1119,plain,(
    ! [A_211,B_212,C_213,D_214] :
      ( k7_relset_1(A_211,B_212,C_213,D_214) = k9_relat_1(C_213,D_214)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(A_211,B_212))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1122,plain,(
    ! [A_211,B_212,D_214] : k7_relset_1(A_211,B_212,'#skF_4',D_214) = k9_relat_1('#skF_4',D_214) ),
    inference(resolution,[status(thm)],[c_899,c_1119])).

tff(c_1127,plain,(
    ! [A_211,B_212,D_214] : k7_relset_1(A_211,B_212,'#skF_4',D_214) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1026,c_1122])).

tff(c_1129,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1127,c_54])).

tff(c_1132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_896,c_1129])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:07:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.49  
% 3.25/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.49  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.25/1.49  
% 3.25/1.49  %Foreground sorts:
% 3.25/1.49  
% 3.25/1.49  
% 3.25/1.49  %Background operators:
% 3.25/1.49  
% 3.25/1.49  
% 3.25/1.49  %Foreground operators:
% 3.25/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.25/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.25/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.25/1.49  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.25/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.25/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.25/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.25/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.25/1.49  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.25/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.25/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.25/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.25/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.25/1.49  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.25/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.25/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.25/1.49  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.25/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.25/1.49  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.25/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.25/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.25/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.25/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.49  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.25/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.25/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.25/1.49  
% 3.25/1.51  tff(f_123, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 3.25/1.51  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.25/1.51  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 3.25/1.51  tff(f_89, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.25/1.51  tff(f_97, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.25/1.51  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.25/1.51  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.25/1.51  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.25/1.51  tff(f_46, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.25/1.51  tff(f_111, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.25/1.51  tff(f_48, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.25/1.51  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.25/1.51  tff(f_81, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.25/1.51  tff(f_78, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.25/1.51  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.25/1.51  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.25/1.51  tff(c_132, plain, (![C_58, A_59, B_60]: (v1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.25/1.51  tff(c_145, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_132])).
% 3.25/1.51  tff(c_30, plain, (![B_19, A_18]: (r1_tarski(k9_relat_1(B_19, A_18), k2_relat_1(B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.25/1.51  tff(c_42, plain, (![A_24]: (k1_relat_1(A_24)!=k1_xboole_0 | k1_xboole_0=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.25/1.51  tff(c_154, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_145, c_42])).
% 3.25/1.51  tff(c_176, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_154])).
% 3.25/1.51  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.25/1.51  tff(c_377, plain, (![B_106, A_107]: (k1_tarski(k1_funct_1(B_106, A_107))=k2_relat_1(B_106) | k1_tarski(A_107)!=k1_relat_1(B_106) | ~v1_funct_1(B_106) | ~v1_relat_1(B_106))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.25/1.51  tff(c_54, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.25/1.51  tff(c_383, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_377, c_54])).
% 3.25/1.51  tff(c_401, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_62, c_383])).
% 3.25/1.51  tff(c_417, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_401])).
% 3.25/1.51  tff(c_290, plain, (![C_85, A_86, B_87]: (v4_relat_1(C_85, A_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.25/1.51  tff(c_303, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_58, c_290])).
% 3.25/1.51  tff(c_28, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(B_17), A_16) | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.25/1.51  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.25/1.51  tff(c_467, plain, (![B_126, C_127, A_128]: (k2_tarski(B_126, C_127)=A_128 | k1_tarski(C_127)=A_128 | k1_tarski(B_126)=A_128 | k1_xboole_0=A_128 | ~r1_tarski(A_128, k2_tarski(B_126, C_127)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.25/1.51  tff(c_487, plain, (![A_1, A_128]: (k2_tarski(A_1, A_1)=A_128 | k1_tarski(A_1)=A_128 | k1_tarski(A_1)=A_128 | k1_xboole_0=A_128 | ~r1_tarski(A_128, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_467])).
% 3.25/1.51  tff(c_537, plain, (![A_135, A_136]: (k1_tarski(A_135)=A_136 | k1_tarski(A_135)=A_136 | k1_tarski(A_135)=A_136 | k1_xboole_0=A_136 | ~r1_tarski(A_136, k1_tarski(A_135)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_487])).
% 3.25/1.51  tff(c_557, plain, (![A_137, B_138]: (k1_tarski(A_137)=k1_relat_1(B_138) | k1_relat_1(B_138)=k1_xboole_0 | ~v4_relat_1(B_138, k1_tarski(A_137)) | ~v1_relat_1(B_138))), inference(resolution, [status(thm)], [c_28, c_537])).
% 3.25/1.51  tff(c_563, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_303, c_557])).
% 3.25/1.51  tff(c_570, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_145, c_563])).
% 3.25/1.51  tff(c_572, plain, $false, inference(negUnitSimplification, [status(thm)], [c_176, c_417, c_570])).
% 3.25/1.51  tff(c_574, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_401])).
% 3.25/1.51  tff(c_581, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_574, c_58])).
% 3.25/1.51  tff(c_52, plain, (![A_33, B_34, C_35, D_36]: (k7_relset_1(A_33, B_34, C_35, D_36)=k9_relat_1(C_35, D_36) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.25/1.51  tff(c_642, plain, (![D_36]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_36)=k9_relat_1('#skF_4', D_36))), inference(resolution, [status(thm)], [c_581, c_52])).
% 3.25/1.51  tff(c_573, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_401])).
% 3.25/1.51  tff(c_873, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_574, c_573])).
% 3.25/1.51  tff(c_874, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_642, c_873])).
% 3.25/1.51  tff(c_887, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_874])).
% 3.25/1.51  tff(c_891, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_145, c_887])).
% 3.25/1.51  tff(c_892, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_154])).
% 3.25/1.51  tff(c_18, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.25/1.51  tff(c_107, plain, (![A_53, B_54]: (r1_tarski(A_53, B_54) | ~m1_subset_1(A_53, k1_zfmisc_1(B_54)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.25/1.51  tff(c_119, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(resolution, [status(thm)], [c_18, c_107])).
% 3.25/1.51  tff(c_896, plain, (![A_10]: (r1_tarski('#skF_4', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_892, c_119])).
% 3.25/1.51  tff(c_36, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.25/1.51  tff(c_900, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_892, c_892, c_36])).
% 3.25/1.51  tff(c_899, plain, (![A_10]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_892, c_18])).
% 3.25/1.51  tff(c_998, plain, (![C_176, A_177, B_178]: (v4_relat_1(C_176, A_177) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.25/1.51  tff(c_1009, plain, (![A_179]: (v4_relat_1('#skF_4', A_179))), inference(resolution, [status(thm)], [c_899, c_998])).
% 3.25/1.51  tff(c_34, plain, (![B_23, A_22]: (k7_relat_1(B_23, A_22)=B_23 | ~v4_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.25/1.51  tff(c_1012, plain, (![A_179]: (k7_relat_1('#skF_4', A_179)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1009, c_34])).
% 3.25/1.51  tff(c_1016, plain, (![A_180]: (k7_relat_1('#skF_4', A_180)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_1012])).
% 3.25/1.51  tff(c_32, plain, (![B_21, A_20]: (k2_relat_1(k7_relat_1(B_21, A_20))=k9_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.25/1.51  tff(c_1021, plain, (![A_180]: (k9_relat_1('#skF_4', A_180)=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1016, c_32])).
% 3.25/1.51  tff(c_1026, plain, (![A_180]: (k9_relat_1('#skF_4', A_180)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_900, c_1021])).
% 3.25/1.51  tff(c_1119, plain, (![A_211, B_212, C_213, D_214]: (k7_relset_1(A_211, B_212, C_213, D_214)=k9_relat_1(C_213, D_214) | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(A_211, B_212))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.25/1.51  tff(c_1122, plain, (![A_211, B_212, D_214]: (k7_relset_1(A_211, B_212, '#skF_4', D_214)=k9_relat_1('#skF_4', D_214))), inference(resolution, [status(thm)], [c_899, c_1119])).
% 3.25/1.51  tff(c_1127, plain, (![A_211, B_212, D_214]: (k7_relset_1(A_211, B_212, '#skF_4', D_214)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1026, c_1122])).
% 3.25/1.51  tff(c_1129, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1127, c_54])).
% 3.25/1.51  tff(c_1132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_896, c_1129])).
% 3.25/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.51  
% 3.25/1.51  Inference rules
% 3.25/1.51  ----------------------
% 3.25/1.51  #Ref     : 0
% 3.25/1.51  #Sup     : 216
% 3.25/1.51  #Fact    : 0
% 3.25/1.51  #Define  : 0
% 3.25/1.51  #Split   : 4
% 3.25/1.51  #Chain   : 0
% 3.25/1.51  #Close   : 0
% 3.25/1.51  
% 3.25/1.51  Ordering : KBO
% 3.25/1.51  
% 3.25/1.51  Simplification rules
% 3.25/1.51  ----------------------
% 3.25/1.51  #Subsume      : 2
% 3.25/1.51  #Demod        : 194
% 3.25/1.51  #Tautology    : 145
% 3.25/1.51  #SimpNegUnit  : 3
% 3.25/1.51  #BackRed      : 23
% 3.25/1.51  
% 3.25/1.51  #Partial instantiations: 0
% 3.25/1.51  #Strategies tried      : 1
% 3.25/1.51  
% 3.25/1.51  Timing (in seconds)
% 3.25/1.51  ----------------------
% 3.25/1.51  Preprocessing        : 0.34
% 3.25/1.51  Parsing              : 0.18
% 3.25/1.51  CNF conversion       : 0.02
% 3.25/1.51  Main loop            : 0.41
% 3.25/1.51  Inferencing          : 0.15
% 3.25/1.51  Reduction            : 0.14
% 3.25/1.51  Demodulation         : 0.10
% 3.25/1.51  BG Simplification    : 0.02
% 3.25/1.51  Subsumption          : 0.06
% 3.25/1.51  Abstraction          : 0.02
% 3.25/1.51  MUC search           : 0.00
% 3.25/1.51  Cooper               : 0.00
% 3.25/1.51  Total                : 0.78
% 3.25/1.51  Index Insertion      : 0.00
% 3.25/1.51  Index Deletion       : 0.00
% 3.25/1.51  Index Matching       : 0.00
% 3.25/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
