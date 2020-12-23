%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:49 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 198 expanded)
%              Number of leaves         :   43 (  85 expanded)
%              Depth                    :   11
%              Number of atoms          :  125 ( 381 expanded)
%              Number of equality atoms :   55 ( 133 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_128,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_116,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_81,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_212,plain,(
    ! [C_67,A_68,B_69] :
      ( v1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_225,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_212])).

tff(c_34,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k9_relat_1(B_21,A_20),k2_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_44,plain,(
    ! [A_24] :
      ( k1_relat_1(A_24) != k1_xboole_0
      | k1_xboole_0 = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_234,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_225,c_44])).

tff(c_236,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_234])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_483,plain,(
    ! [B_127,A_128] :
      ( k1_tarski(k1_funct_1(B_127,A_128)) = k2_relat_1(B_127)
      | k1_tarski(A_128) != k1_relat_1(B_127)
      | ~ v1_funct_1(B_127)
      | ~ v1_relat_1(B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_426,plain,(
    ! [A_104,B_105,C_106,D_107] :
      ( k7_relset_1(A_104,B_105,C_106,D_107) = k9_relat_1(C_106,D_107)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_436,plain,(
    ! [D_107] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_107) = k9_relat_1('#skF_4',D_107) ),
    inference(resolution,[status(thm)],[c_64,c_426])).

tff(c_60,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_448,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_60])).

tff(c_489,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_448])).

tff(c_507,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_68,c_489])).

tff(c_509,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_507])).

tff(c_280,plain,(
    ! [C_77,A_78,B_79] :
      ( v4_relat_1(C_77,A_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_293,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_280])).

tff(c_30,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k1_relat_1(B_18),A_17)
      | ~ v4_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_511,plain,(
    ! [B_132,C_133,A_134] :
      ( k2_tarski(B_132,C_133) = A_134
      | k1_tarski(C_133) = A_134
      | k1_tarski(B_132) = A_134
      | k1_xboole_0 = A_134
      | ~ r1_tarski(A_134,k2_tarski(B_132,C_133)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_535,plain,(
    ! [A_2,A_134] :
      ( k2_tarski(A_2,A_2) = A_134
      | k1_tarski(A_2) = A_134
      | k1_tarski(A_2) = A_134
      | k1_xboole_0 = A_134
      | ~ r1_tarski(A_134,k1_tarski(A_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_511])).

tff(c_602,plain,(
    ! [A_148,A_149] :
      ( k1_tarski(A_148) = A_149
      | k1_tarski(A_148) = A_149
      | k1_tarski(A_148) = A_149
      | k1_xboole_0 = A_149
      | ~ r1_tarski(A_149,k1_tarski(A_148)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_535])).

tff(c_644,plain,(
    ! [A_153,B_154] :
      ( k1_tarski(A_153) = k1_relat_1(B_154)
      | k1_relat_1(B_154) = k1_xboole_0
      | ~ v4_relat_1(B_154,k1_tarski(A_153))
      | ~ v1_relat_1(B_154) ) ),
    inference(resolution,[status(thm)],[c_30,c_602])).

tff(c_654,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_293,c_644])).

tff(c_662,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_654])).

tff(c_664,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_509,c_662])).

tff(c_665,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_507])).

tff(c_715,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_665])).

tff(c_719,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_715])).

tff(c_720,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_234])).

tff(c_20,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_134,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,B_55)
      | ~ m1_subset_1(A_54,k1_zfmisc_1(B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_142,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(resolution,[status(thm)],[c_20,c_134])).

tff(c_726,plain,(
    ! [A_11] : r1_tarski('#skF_4',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_720,c_142])).

tff(c_38,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_733,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_720,c_720,c_38])).

tff(c_744,plain,(
    ! [A_20] :
      ( r1_tarski(k9_relat_1('#skF_4',A_20),'#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_733,c_34])).

tff(c_815,plain,(
    ! [A_164] : r1_tarski(k9_relat_1('#skF_4',A_164),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_744])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_728,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ r1_tarski(A_1,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_720,c_720,c_2])).

tff(c_819,plain,(
    ! [A_164] : k9_relat_1('#skF_4',A_164) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_815,c_728])).

tff(c_729,plain,(
    ! [A_11] : m1_subset_1('#skF_4',k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_720,c_20])).

tff(c_1000,plain,(
    ! [A_202,B_203,C_204,D_205] :
      ( k7_relset_1(A_202,B_203,C_204,D_205) = k9_relat_1(C_204,D_205)
      | ~ m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(A_202,B_203))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1003,plain,(
    ! [A_202,B_203,D_205] : k7_relset_1(A_202,B_203,'#skF_4',D_205) = k9_relat_1('#skF_4',D_205) ),
    inference(resolution,[status(thm)],[c_729,c_1000])).

tff(c_1008,plain,(
    ! [A_202,B_203,D_205] : k7_relset_1(A_202,B_203,'#skF_4',D_205) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_819,c_1003])).

tff(c_1010,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_60])).

tff(c_1013,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_726,c_1010])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:01:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.00/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.52  
% 3.31/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.53  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.31/1.53  
% 3.31/1.53  %Foreground sorts:
% 3.31/1.53  
% 3.31/1.53  
% 3.31/1.53  %Background operators:
% 3.31/1.53  
% 3.31/1.53  
% 3.31/1.53  %Foreground operators:
% 3.31/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.31/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.31/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.31/1.53  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.31/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.31/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.31/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.31/1.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.31/1.53  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.31/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.31/1.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.31/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.31/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.31/1.53  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.31/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.31/1.53  tff('#skF_1', type, '#skF_1': $i).
% 3.31/1.53  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.31/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.31/1.53  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.31/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.31/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.31/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.31/1.53  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.31/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.53  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.31/1.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.31/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.31/1.53  
% 3.31/1.54  tff(f_128, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 3.31/1.54  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.31/1.54  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 3.31/1.54  tff(f_89, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.31/1.54  tff(f_102, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.31/1.54  tff(f_116, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.31/1.54  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.31/1.54  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.31/1.54  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.31/1.54  tff(f_50, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.31/1.54  tff(f_52, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.31/1.54  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.31/1.54  tff(f_81, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.31/1.54  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.31/1.54  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.31/1.54  tff(c_212, plain, (![C_67, A_68, B_69]: (v1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.31/1.54  tff(c_225, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_212])).
% 3.31/1.54  tff(c_34, plain, (![B_21, A_20]: (r1_tarski(k9_relat_1(B_21, A_20), k2_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.31/1.54  tff(c_44, plain, (![A_24]: (k1_relat_1(A_24)!=k1_xboole_0 | k1_xboole_0=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.31/1.54  tff(c_234, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_225, c_44])).
% 3.31/1.54  tff(c_236, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_234])).
% 3.31/1.54  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.31/1.54  tff(c_483, plain, (![B_127, A_128]: (k1_tarski(k1_funct_1(B_127, A_128))=k2_relat_1(B_127) | k1_tarski(A_128)!=k1_relat_1(B_127) | ~v1_funct_1(B_127) | ~v1_relat_1(B_127))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.31/1.54  tff(c_426, plain, (![A_104, B_105, C_106, D_107]: (k7_relset_1(A_104, B_105, C_106, D_107)=k9_relat_1(C_106, D_107) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.31/1.54  tff(c_436, plain, (![D_107]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_107)=k9_relat_1('#skF_4', D_107))), inference(resolution, [status(thm)], [c_64, c_426])).
% 3.31/1.54  tff(c_60, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.31/1.54  tff(c_448, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_436, c_60])).
% 3.31/1.54  tff(c_489, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_483, c_448])).
% 3.31/1.54  tff(c_507, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_225, c_68, c_489])).
% 3.31/1.54  tff(c_509, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_507])).
% 3.31/1.54  tff(c_280, plain, (![C_77, A_78, B_79]: (v4_relat_1(C_77, A_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.31/1.54  tff(c_293, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_64, c_280])).
% 3.31/1.54  tff(c_30, plain, (![B_18, A_17]: (r1_tarski(k1_relat_1(B_18), A_17) | ~v4_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.31/1.54  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.31/1.54  tff(c_511, plain, (![B_132, C_133, A_134]: (k2_tarski(B_132, C_133)=A_134 | k1_tarski(C_133)=A_134 | k1_tarski(B_132)=A_134 | k1_xboole_0=A_134 | ~r1_tarski(A_134, k2_tarski(B_132, C_133)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.31/1.54  tff(c_535, plain, (![A_2, A_134]: (k2_tarski(A_2, A_2)=A_134 | k1_tarski(A_2)=A_134 | k1_tarski(A_2)=A_134 | k1_xboole_0=A_134 | ~r1_tarski(A_134, k1_tarski(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_511])).
% 3.31/1.54  tff(c_602, plain, (![A_148, A_149]: (k1_tarski(A_148)=A_149 | k1_tarski(A_148)=A_149 | k1_tarski(A_148)=A_149 | k1_xboole_0=A_149 | ~r1_tarski(A_149, k1_tarski(A_148)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_535])).
% 3.31/1.54  tff(c_644, plain, (![A_153, B_154]: (k1_tarski(A_153)=k1_relat_1(B_154) | k1_relat_1(B_154)=k1_xboole_0 | ~v4_relat_1(B_154, k1_tarski(A_153)) | ~v1_relat_1(B_154))), inference(resolution, [status(thm)], [c_30, c_602])).
% 3.31/1.54  tff(c_654, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_293, c_644])).
% 3.31/1.54  tff(c_662, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_225, c_654])).
% 3.31/1.54  tff(c_664, plain, $false, inference(negUnitSimplification, [status(thm)], [c_236, c_509, c_662])).
% 3.31/1.54  tff(c_665, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_507])).
% 3.31/1.54  tff(c_715, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_665])).
% 3.31/1.54  tff(c_719, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_225, c_715])).
% 3.31/1.54  tff(c_720, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_234])).
% 3.31/1.54  tff(c_20, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.31/1.54  tff(c_134, plain, (![A_54, B_55]: (r1_tarski(A_54, B_55) | ~m1_subset_1(A_54, k1_zfmisc_1(B_55)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.31/1.54  tff(c_142, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(resolution, [status(thm)], [c_20, c_134])).
% 3.31/1.54  tff(c_726, plain, (![A_11]: (r1_tarski('#skF_4', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_720, c_142])).
% 3.31/1.54  tff(c_38, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.31/1.54  tff(c_733, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_720, c_720, c_38])).
% 3.31/1.54  tff(c_744, plain, (![A_20]: (r1_tarski(k9_relat_1('#skF_4', A_20), '#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_733, c_34])).
% 3.31/1.54  tff(c_815, plain, (![A_164]: (r1_tarski(k9_relat_1('#skF_4', A_164), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_744])).
% 3.31/1.54  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.31/1.54  tff(c_728, plain, (![A_1]: (A_1='#skF_4' | ~r1_tarski(A_1, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_720, c_720, c_2])).
% 3.31/1.54  tff(c_819, plain, (![A_164]: (k9_relat_1('#skF_4', A_164)='#skF_4')), inference(resolution, [status(thm)], [c_815, c_728])).
% 3.31/1.54  tff(c_729, plain, (![A_11]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_720, c_20])).
% 3.31/1.54  tff(c_1000, plain, (![A_202, B_203, C_204, D_205]: (k7_relset_1(A_202, B_203, C_204, D_205)=k9_relat_1(C_204, D_205) | ~m1_subset_1(C_204, k1_zfmisc_1(k2_zfmisc_1(A_202, B_203))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.31/1.54  tff(c_1003, plain, (![A_202, B_203, D_205]: (k7_relset_1(A_202, B_203, '#skF_4', D_205)=k9_relat_1('#skF_4', D_205))), inference(resolution, [status(thm)], [c_729, c_1000])).
% 3.31/1.54  tff(c_1008, plain, (![A_202, B_203, D_205]: (k7_relset_1(A_202, B_203, '#skF_4', D_205)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_819, c_1003])).
% 3.31/1.54  tff(c_1010, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1008, c_60])).
% 3.31/1.54  tff(c_1013, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_726, c_1010])).
% 3.31/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.54  
% 3.31/1.54  Inference rules
% 3.31/1.54  ----------------------
% 3.31/1.54  #Ref     : 0
% 3.31/1.54  #Sup     : 188
% 3.31/1.54  #Fact    : 0
% 3.31/1.54  #Define  : 0
% 3.31/1.54  #Split   : 3
% 3.31/1.54  #Chain   : 0
% 3.31/1.54  #Close   : 0
% 3.31/1.54  
% 3.31/1.54  Ordering : KBO
% 3.31/1.54  
% 3.31/1.54  Simplification rules
% 3.31/1.54  ----------------------
% 3.31/1.54  #Subsume      : 3
% 3.31/1.54  #Demod        : 153
% 3.31/1.54  #Tautology    : 113
% 3.31/1.54  #SimpNegUnit  : 1
% 3.31/1.54  #BackRed      : 23
% 3.31/1.54  
% 3.31/1.54  #Partial instantiations: 0
% 3.31/1.54  #Strategies tried      : 1
% 3.31/1.54  
% 3.31/1.54  Timing (in seconds)
% 3.31/1.54  ----------------------
% 3.31/1.55  Preprocessing        : 0.35
% 3.31/1.55  Parsing              : 0.19
% 3.31/1.55  CNF conversion       : 0.02
% 3.31/1.55  Main loop            : 0.39
% 3.31/1.55  Inferencing          : 0.14
% 3.31/1.55  Reduction            : 0.13
% 3.31/1.55  Demodulation         : 0.09
% 3.31/1.55  BG Simplification    : 0.02
% 3.31/1.55  Subsumption          : 0.06
% 3.31/1.55  Abstraction          : 0.02
% 3.31/1.55  MUC search           : 0.00
% 3.31/1.55  Cooper               : 0.00
% 3.31/1.55  Total                : 0.77
% 3.31/1.55  Index Insertion      : 0.00
% 3.31/1.55  Index Deletion       : 0.00
% 3.31/1.55  Index Matching       : 0.00
% 3.31/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
