%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:33 EST 2020

% Result     : Theorem 13.15s
% Output     : CNFRefutation 13.15s
% Verified   : 
% Statistics : Number of formulae       :  244 (1320 expanded)
%              Number of leaves         :   58 ( 473 expanded)
%              Depth                    :   20
%              Number of atoms          :  456 (3619 expanded)
%              Number of equality atoms :  114 ( 828 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_254,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_182,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_176,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_99,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_186,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_145,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_122,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v2_funct_1(A)
            & r1_tarski(B,k1_relat_1(A)) )
         => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_218,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_237,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(B,C)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | ( v1_funct_1(D)
            & v1_funct_2(D,A,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_208,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_91,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_86,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_206,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_103,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_172,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

tff(f_192,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_202,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_110,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_114,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_1084,plain,(
    ! [C_168,A_169,B_170] :
      ( v4_relat_1(C_168,A_169)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_1102,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_114,c_1084])).

tff(c_608,plain,(
    ! [C_107,A_108,B_109] :
      ( v1_relat_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_622,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_114,c_608])).

tff(c_32,plain,(
    ! [A_19] :
      ( k1_relat_1(A_19) != k1_xboole_0
      | k1_xboole_0 = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_652,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_622,c_32])).

tff(c_658,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_652])).

tff(c_118,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_46,plain,(
    ! [A_23] :
      ( v1_funct_1(k2_funct_1(A_23))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_108,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_293,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_296,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_293])).

tff(c_299,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_296])).

tff(c_488,plain,(
    ! [C_94,A_95,B_96] :
      ( v1_relat_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_498,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_114,c_488])).

tff(c_505,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_299,c_498])).

tff(c_507,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_112,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_1455,plain,(
    ! [A_203,B_204,C_205] :
      ( k2_relset_1(A_203,B_204,C_205) = k2_relat_1(C_205)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_203,B_204))) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_1468,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_114,c_1455])).

tff(c_1475,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_1468])).

tff(c_62,plain,(
    ! [A_33] :
      ( k1_relat_1(k2_funct_1(A_33)) = k2_relat_1(A_33)
      | ~ v2_funct_1(A_33)
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_48,plain,(
    ! [A_23] :
      ( v1_relat_1(k2_funct_1(A_23))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_791,plain,(
    ! [A_122,B_123] :
      ( r2_hidden('#skF_1'(A_122,B_123),A_122)
      | r1_tarski(A_122,B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_796,plain,(
    ! [A_122] : r1_tarski(A_122,A_122) ),
    inference(resolution,[status(thm)],[c_791,c_4])).

tff(c_28,plain,(
    ! [A_18] :
      ( k10_relat_1(A_18,k2_relat_1(A_18)) = k1_relat_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1492,plain,
    ( k10_relat_1('#skF_4','#skF_3') = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1475,c_28])).

tff(c_1507,plain,(
    k10_relat_1('#skF_4','#skF_3') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_1492])).

tff(c_1688,plain,(
    ! [B_212,A_213] :
      ( k9_relat_1(B_212,k10_relat_1(B_212,A_213)) = A_213
      | ~ r1_tarski(A_213,k2_relat_1(B_212))
      | ~ v1_funct_1(B_212)
      | ~ v1_relat_1(B_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1693,plain,(
    ! [A_213] :
      ( k9_relat_1('#skF_4',k10_relat_1('#skF_4',A_213)) = A_213
      | ~ r1_tarski(A_213,'#skF_3')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1475,c_1688])).

tff(c_1760,plain,(
    ! [A_217] :
      ( k9_relat_1('#skF_4',k10_relat_1('#skF_4',A_217)) = A_217
      | ~ r1_tarski(A_217,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_118,c_1693])).

tff(c_1769,plain,
    ( k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1507,c_1760])).

tff(c_1777,plain,(
    k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_796,c_1769])).

tff(c_2037,plain,(
    ! [A_241,B_242] :
      ( k9_relat_1(k2_funct_1(A_241),k9_relat_1(A_241,B_242)) = B_242
      | ~ r1_tarski(B_242,k1_relat_1(A_241))
      | ~ v2_funct_1(A_241)
      | ~ v1_funct_1(A_241)
      | ~ v1_relat_1(A_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2052,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1777,c_2037])).

tff(c_2077,plain,(
    k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_118,c_112,c_796,c_2052])).

tff(c_1359,plain,(
    ! [A_195] :
      ( k1_relat_1(k2_funct_1(A_195)) = k2_relat_1(A_195)
      | ~ v2_funct_1(A_195)
      | ~ v1_funct_1(A_195)
      | ~ v1_relat_1(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_26,plain,(
    ! [A_17] :
      ( k9_relat_1(A_17,k1_relat_1(A_17)) = k2_relat_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8288,plain,(
    ! [A_574] :
      ( k9_relat_1(k2_funct_1(A_574),k2_relat_1(A_574)) = k2_relat_1(k2_funct_1(A_574))
      | ~ v1_relat_1(k2_funct_1(A_574))
      | ~ v2_funct_1(A_574)
      | ~ v1_funct_1(A_574)
      | ~ v1_relat_1(A_574) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1359,c_26])).

tff(c_8315,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1475,c_8288])).

tff(c_8339,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_118,c_112,c_2077,c_8315])).

tff(c_8348,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_8339])).

tff(c_8357,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_8348])).

tff(c_8363,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_118,c_8357])).

tff(c_8365,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_8339])).

tff(c_8364,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_8339])).

tff(c_92,plain,(
    ! [A_57] :
      ( v1_funct_2(A_57,k1_relat_1(A_57),k2_relat_1(A_57))
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_8506,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8364,c_92])).

tff(c_8600,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8365,c_507,c_8506])).

tff(c_8769,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_8600])).

tff(c_8771,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_118,c_112,c_1475,c_8769])).

tff(c_90,plain,(
    ! [A_57] :
      ( m1_subset_1(A_57,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_57),k2_relat_1(A_57))))
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_8500,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4'))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8364,c_90])).

tff(c_8595,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8365,c_507,c_8500])).

tff(c_9634,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_8595])).

tff(c_9652,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_118,c_112,c_1475,c_9634])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(B_14),A_13)
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2660,plain,(
    ! [B_295,D_296,A_297,C_298] :
      ( k1_xboole_0 = B_295
      | m1_subset_1(D_296,k1_zfmisc_1(k2_zfmisc_1(A_297,C_298)))
      | ~ r1_tarski(B_295,C_298)
      | ~ m1_subset_1(D_296,k1_zfmisc_1(k2_zfmisc_1(A_297,B_295)))
      | ~ v1_funct_2(D_296,A_297,B_295)
      | ~ v1_funct_1(D_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_15222,plain,(
    ! [B_890,D_891,A_892,A_893] :
      ( k1_relat_1(B_890) = k1_xboole_0
      | m1_subset_1(D_891,k1_zfmisc_1(k2_zfmisc_1(A_892,A_893)))
      | ~ m1_subset_1(D_891,k1_zfmisc_1(k2_zfmisc_1(A_892,k1_relat_1(B_890))))
      | ~ v1_funct_2(D_891,A_892,k1_relat_1(B_890))
      | ~ v1_funct_1(D_891)
      | ~ v4_relat_1(B_890,A_893)
      | ~ v1_relat_1(B_890) ) ),
    inference(resolution,[status(thm)],[c_20,c_2660])).

tff(c_15226,plain,(
    ! [A_893] :
      ( k1_relat_1('#skF_4') = k1_xboole_0
      | m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_893)))
      | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4'))
      | ~ v1_funct_1(k2_funct_1('#skF_4'))
      | ~ v4_relat_1('#skF_4',A_893)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_9652,c_15222])).

tff(c_15259,plain,(
    ! [A_893] :
      ( k1_relat_1('#skF_4') = k1_xboole_0
      | m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_893)))
      | ~ v4_relat_1('#skF_4',A_893) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_507,c_8771,c_15226])).

tff(c_15390,plain,(
    ! [A_900] :
      ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_900)))
      | ~ v4_relat_1('#skF_4',A_900) ) ),
    inference(negUnitSimplification,[status(thm)],[c_658,c_15259])).

tff(c_506,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_568,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_506])).

tff(c_15443,plain,(
    ~ v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_15390,c_568])).

tff(c_15493,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1102,c_15443])).

tff(c_15494,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_652])).

tff(c_134,plain,(
    ! [A_65] : k6_relat_1(A_65) = k6_partfun1(A_65) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_44,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_140,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_44])).

tff(c_88,plain,(
    ! [A_56] : k6_relat_1(A_56) = k6_partfun1(A_56) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_40,plain,(
    ! [A_21] : k2_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_173,plain,(
    ! [A_67] : k2_relat_1(k6_partfun1(A_67)) = A_67 ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_40])).

tff(c_182,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_173])).

tff(c_15504,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15494,c_15494,c_182])).

tff(c_30,plain,(
    ! [A_19] :
      ( k2_relat_1(A_19) != k1_xboole_0
      | k1_xboole_0 = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_651,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_622,c_30])).

tff(c_657,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_651])).

tff(c_15582,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15504,c_15494,c_657])).

tff(c_15583,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_651])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_15666,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15583,c_8])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( v1_xboole_0(k2_zfmisc_1(A_6,B_7))
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_86,plain,(
    ! [A_55] : m1_subset_1(k6_partfun1(A_55),k1_zfmisc_1(k2_zfmisc_1(A_55,A_55))) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_16440,plain,(
    ! [C_978,B_979,A_980] :
      ( ~ v1_xboole_0(C_978)
      | ~ m1_subset_1(B_979,k1_zfmisc_1(C_978))
      | ~ r2_hidden(A_980,B_979) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16501,plain,(
    ! [A_986,A_987] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_986,A_986))
      | ~ r2_hidden(A_987,k6_partfun1(A_986)) ) ),
    inference(resolution,[status(thm)],[c_86,c_16440])).

tff(c_16506,plain,(
    ! [A_988,B_989] :
      ( ~ r2_hidden(A_988,k6_partfun1(B_989))
      | ~ v1_xboole_0(B_989) ) ),
    inference(resolution,[status(thm)],[c_10,c_16501])).

tff(c_16515,plain,(
    ! [B_990,B_991] :
      ( ~ v1_xboole_0(B_990)
      | r1_tarski(k6_partfun1(B_990),B_991) ) ),
    inference(resolution,[status(thm)],[c_6,c_16506])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16275,plain,(
    ! [C_961,B_962,A_963] :
      ( v5_relat_1(C_961,B_962)
      | ~ m1_subset_1(C_961,k1_zfmisc_1(k2_zfmisc_1(A_963,B_962))) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_16290,plain,(
    ! [A_8,B_962,A_963] :
      ( v5_relat_1(A_8,B_962)
      | ~ r1_tarski(A_8,k2_zfmisc_1(A_963,B_962)) ) ),
    inference(resolution,[status(thm)],[c_14,c_16275])).

tff(c_16605,plain,(
    ! [B_996,B_997] :
      ( v5_relat_1(k6_partfun1(B_996),B_997)
      | ~ v1_xboole_0(B_996) ) ),
    inference(resolution,[status(thm)],[c_16515,c_16290])).

tff(c_50,plain,(
    ! [A_24] : v1_relat_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_123,plain,(
    ! [A_24] : v1_relat_1(k6_partfun1(A_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_50])).

tff(c_125,plain,(
    ! [A_21] : k2_relat_1(k6_partfun1(A_21)) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_40])).

tff(c_16086,plain,(
    ! [B_931,A_932] :
      ( r1_tarski(k2_relat_1(B_931),A_932)
      | ~ v5_relat_1(B_931,A_932)
      | ~ v1_relat_1(B_931) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16096,plain,(
    ! [A_21,A_932] :
      ( r1_tarski(A_21,A_932)
      | ~ v5_relat_1(k6_partfun1(A_21),A_932)
      | ~ v1_relat_1(k6_partfun1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_16086])).

tff(c_16101,plain,(
    ! [A_21,A_932] :
      ( r1_tarski(A_21,A_932)
      | ~ v5_relat_1(k6_partfun1(A_21),A_932) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_16096])).

tff(c_16613,plain,(
    ! [B_998,B_999] :
      ( r1_tarski(B_998,B_999)
      | ~ v1_xboole_0(B_998) ) ),
    inference(resolution,[status(thm)],[c_16605,c_16101])).

tff(c_68,plain,(
    ! [A_38] : k2_funct_1(k6_relat_1(A_38)) = k6_relat_1(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_193,plain,(
    ! [A_68] : k2_funct_1(k6_partfun1(A_68)) = k6_partfun1(A_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_88,c_68])).

tff(c_202,plain,(
    k6_partfun1(k1_xboole_0) = k2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_193])).

tff(c_205,plain,(
    k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_202])).

tff(c_15660,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15583,c_15583,c_205])).

tff(c_607,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_14,c_568])).

tff(c_15694,plain,(
    ~ r1_tarski('#skF_4',k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15660,c_607])).

tff(c_16638,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_16613,c_15694])).

tff(c_16648,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15666,c_16638])).

tff(c_16649,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_506])).

tff(c_16748,plain,(
    ! [A_1007,B_1008] :
      ( r2_hidden('#skF_1'(A_1007,B_1008),A_1007)
      | r1_tarski(A_1007,B_1008) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16753,plain,(
    ! [A_1007] : r1_tarski(A_1007,A_1007) ),
    inference(resolution,[status(thm)],[c_16748,c_4])).

tff(c_16754,plain,(
    ! [C_1009,A_1010,B_1011] :
      ( v1_relat_1(C_1009)
      | ~ m1_subset_1(C_1009,k1_zfmisc_1(k2_zfmisc_1(A_1010,B_1011))) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_16772,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_114,c_16754])).

tff(c_17741,plain,(
    ! [A_1114,B_1115,C_1116] :
      ( k2_relset_1(A_1114,B_1115,C_1116) = k2_relat_1(C_1116)
      | ~ m1_subset_1(C_1116,k1_zfmisc_1(k2_zfmisc_1(A_1114,B_1115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_17760,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_114,c_17741])).

tff(c_17769,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_17760])).

tff(c_16650,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_506])).

tff(c_16768,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_16650,c_16754])).

tff(c_17789,plain,
    ( k10_relat_1('#skF_4','#skF_3') = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_17769,c_28])).

tff(c_17806,plain,(
    k10_relat_1('#skF_4','#skF_3') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16772,c_17789])).

tff(c_17861,plain,(
    ! [B_1119,A_1120] :
      ( k9_relat_1(B_1119,k10_relat_1(B_1119,A_1120)) = A_1120
      | ~ r1_tarski(A_1120,k2_relat_1(B_1119))
      | ~ v1_funct_1(B_1119)
      | ~ v1_relat_1(B_1119) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_17863,plain,(
    ! [A_1120] :
      ( k9_relat_1('#skF_4',k10_relat_1('#skF_4',A_1120)) = A_1120
      | ~ r1_tarski(A_1120,'#skF_3')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17769,c_17861])).

tff(c_18012,plain,(
    ! [A_1130] :
      ( k9_relat_1('#skF_4',k10_relat_1('#skF_4',A_1130)) = A_1130
      | ~ r1_tarski(A_1130,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16772,c_118,c_17863])).

tff(c_18021,plain,
    ( k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_17806,c_18012])).

tff(c_18029,plain,(
    k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16753,c_18021])).

tff(c_18288,plain,(
    ! [A_1150,B_1151] :
      ( k9_relat_1(k2_funct_1(A_1150),k9_relat_1(A_1150,B_1151)) = B_1151
      | ~ r1_tarski(B_1151,k1_relat_1(A_1150))
      | ~ v2_funct_1(A_1150)
      | ~ v1_funct_1(A_1150)
      | ~ v1_relat_1(A_1150) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_18303,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_18029,c_18288])).

tff(c_18328,plain,(
    k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16772,c_118,c_112,c_16753,c_18303])).

tff(c_17546,plain,(
    ! [A_1096] :
      ( k1_relat_1(k2_funct_1(A_1096)) = k2_relat_1(A_1096)
      | ~ v2_funct_1(A_1096)
      | ~ v1_funct_1(A_1096)
      | ~ v1_relat_1(A_1096) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_24137,plain,(
    ! [A_1419] :
      ( k9_relat_1(k2_funct_1(A_1419),k2_relat_1(A_1419)) = k2_relat_1(k2_funct_1(A_1419))
      | ~ v1_relat_1(k2_funct_1(A_1419))
      | ~ v2_funct_1(A_1419)
      | ~ v1_funct_1(A_1419)
      | ~ v1_relat_1(A_1419) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17546,c_26])).

tff(c_24164,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_17769,c_24137])).

tff(c_24188,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16772,c_118,c_112,c_16768,c_18328,c_24164])).

tff(c_24285,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_24188,c_92])).

tff(c_24368,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16768,c_507,c_24285])).

tff(c_24624,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_24368])).

tff(c_24626,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16772,c_118,c_112,c_17769,c_24624])).

tff(c_18082,plain,(
    ! [D_1132,C_1133,B_1134,A_1135] :
      ( m1_subset_1(D_1132,k1_zfmisc_1(k2_zfmisc_1(C_1133,B_1134)))
      | ~ r1_tarski(k2_relat_1(D_1132),B_1134)
      | ~ m1_subset_1(D_1132,k1_zfmisc_1(k2_zfmisc_1(C_1133,A_1135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_18104,plain,(
    ! [B_1134] :
      ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_1134)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_4')),B_1134) ) ),
    inference(resolution,[status(thm)],[c_16650,c_18082])).

tff(c_24209,plain,(
    ! [B_1134] :
      ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_1134)))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_1134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24188,c_18104])).

tff(c_16784,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_16772,c_32])).

tff(c_16823,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_16784])).

tff(c_16996,plain,(
    ! [C_1028,B_1029,A_1030] :
      ( v5_relat_1(C_1028,B_1029)
      | ~ m1_subset_1(C_1028,k1_zfmisc_1(k2_zfmisc_1(A_1030,B_1029))) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_17014,plain,(
    v5_relat_1(k2_funct_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_16650,c_16996])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k2_relat_1(B_16),A_15)
      | ~ v5_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_24294,plain,(
    ! [A_15] :
      ( r1_tarski(k1_relat_1('#skF_4'),A_15)
      | ~ v5_relat_1(k2_funct_1('#skF_4'),A_15)
      | ~ v1_relat_1(k2_funct_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24188,c_24])).

tff(c_24484,plain,(
    ! [A_1426] :
      ( r1_tarski(k1_relat_1('#skF_4'),A_1426)
      | ~ v5_relat_1(k2_funct_1('#skF_4'),A_1426) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16768,c_24294])).

tff(c_24539,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_17014,c_24484])).

tff(c_102,plain,(
    ! [B_59,D_61,A_58,C_60] :
      ( k1_xboole_0 = B_59
      | v1_funct_2(D_61,A_58,C_60)
      | ~ r1_tarski(B_59,C_60)
      | ~ m1_subset_1(D_61,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59)))
      | ~ v1_funct_2(D_61,A_58,B_59)
      | ~ v1_funct_1(D_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_24550,plain,(
    ! [D_61,A_58] :
      ( k1_relat_1('#skF_4') = k1_xboole_0
      | v1_funct_2(D_61,A_58,'#skF_2')
      | ~ m1_subset_1(D_61,k1_zfmisc_1(k2_zfmisc_1(A_58,k1_relat_1('#skF_4'))))
      | ~ v1_funct_2(D_61,A_58,k1_relat_1('#skF_4'))
      | ~ v1_funct_1(D_61) ) ),
    inference(resolution,[status(thm)],[c_24539,c_102])).

tff(c_24906,plain,(
    ! [D_1440,A_1441] :
      ( v1_funct_2(D_1440,A_1441,'#skF_2')
      | ~ m1_subset_1(D_1440,k1_zfmisc_1(k2_zfmisc_1(A_1441,k1_relat_1('#skF_4'))))
      | ~ v1_funct_2(D_1440,A_1441,k1_relat_1('#skF_4'))
      | ~ v1_funct_1(D_1440) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16823,c_24550])).

tff(c_24910,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_24209,c_24906])).

tff(c_24941,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16753,c_507,c_24626,c_24910])).

tff(c_24943,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16649,c_24941])).

tff(c_24944,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_16784])).

tff(c_24957,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24944,c_24944,c_182])).

tff(c_16783,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_16772,c_30])).

tff(c_16798,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_16783])).

tff(c_24947,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24944,c_16798])).

tff(c_25040,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24957,c_24947])).

tff(c_25041,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_16783])).

tff(c_25042,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_16783])).

tff(c_25290,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25041,c_25042])).

tff(c_27066,plain,(
    ! [A_1627,B_1628,C_1629] :
      ( k2_relset_1(A_1627,B_1628,C_1629) = k2_relat_1(C_1629)
      | ~ m1_subset_1(C_1629,k1_zfmisc_1(k2_zfmisc_1(A_1627,B_1628))) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_27085,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_114,c_27066])).

tff(c_27095,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_25290,c_27085])).

tff(c_25245,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25041,c_25041,c_205])).

tff(c_25316,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25245,c_16649])).

tff(c_27099,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27095,c_25316])).

tff(c_38,plain,(
    ! [A_21] : k1_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_126,plain,(
    ! [A_21] : k1_relat_1(k6_partfun1(A_21)) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_38])).

tff(c_237,plain,(
    ! [A_73] :
      ( k1_relat_1(A_73) != k1_xboole_0
      | k1_xboole_0 = A_73
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_246,plain,(
    ! [A_24] :
      ( k1_relat_1(k6_partfun1(A_24)) != k1_xboole_0
      | k6_partfun1(A_24) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_123,c_237])).

tff(c_256,plain,(
    ! [A_74] :
      ( k1_xboole_0 != A_74
      | k6_partfun1(A_74) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_246])).

tff(c_84,plain,(
    ! [A_55] : v1_partfun1(k6_partfun1(A_55),A_55) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_271,plain,(
    ! [A_74] :
      ( v1_partfun1(k1_xboole_0,A_74)
      | k1_xboole_0 != A_74 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_84])).

tff(c_25507,plain,(
    v1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25041,c_25041,c_271])).

tff(c_25315,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25245,c_16650])).

tff(c_27098,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27095,c_25315])).

tff(c_27297,plain,(
    ! [C_1636,A_1637,B_1638] :
      ( v1_funct_2(C_1636,A_1637,B_1638)
      | ~ v1_partfun1(C_1636,A_1637)
      | ~ v1_funct_1(C_1636)
      | ~ m1_subset_1(C_1636,k1_zfmisc_1(k2_zfmisc_1(A_1637,B_1638))) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_27303,plain,
    ( v1_funct_2('#skF_4','#skF_4','#skF_2')
    | ~ v1_partfun1('#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_27098,c_27297])).

tff(c_27322,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_25507,c_27303])).

tff(c_27324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27099,c_27322])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:06:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.15/5.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.15/5.81  
% 13.15/5.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.15/5.81  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 13.15/5.81  
% 13.15/5.81  %Foreground sorts:
% 13.15/5.81  
% 13.15/5.81  
% 13.15/5.81  %Background operators:
% 13.15/5.81  
% 13.15/5.81  
% 13.15/5.81  %Foreground operators:
% 13.15/5.81  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 13.15/5.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.15/5.81  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 13.15/5.81  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 13.15/5.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.15/5.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.15/5.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.15/5.81  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 13.15/5.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.15/5.81  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.15/5.81  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.15/5.81  tff('#skF_2', type, '#skF_2': $i).
% 13.15/5.81  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 13.15/5.81  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 13.15/5.81  tff('#skF_3', type, '#skF_3': $i).
% 13.15/5.81  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 13.15/5.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.15/5.81  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 13.15/5.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.15/5.81  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 13.15/5.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.15/5.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.15/5.81  tff('#skF_4', type, '#skF_4': $i).
% 13.15/5.81  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 13.15/5.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.15/5.81  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 13.15/5.81  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.15/5.81  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.15/5.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.15/5.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.15/5.81  
% 13.15/5.84  tff(f_254, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 13.15/5.84  tff(f_182, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 13.15/5.84  tff(f_176, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 13.15/5.84  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 13.15/5.84  tff(f_99, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 13.15/5.84  tff(f_186, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 13.15/5.84  tff(f_145, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 13.15/5.84  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 13.15/5.84  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 13.15/5.84  tff(f_111, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 13.15/5.84  tff(f_122, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t177_funct_1)).
% 13.15/5.84  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 13.15/5.84  tff(f_218, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 13.15/5.84  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 13.15/5.84  tff(f_237, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 13.15/5.84  tff(f_208, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 13.15/5.84  tff(f_91, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 13.15/5.84  tff(f_86, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 13.15/5.84  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 13.15/5.84  tff(f_37, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 13.15/5.84  tff(f_206, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 13.15/5.84  tff(f_48, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 13.15/5.84  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 13.15/5.84  tff(f_103, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 13.15/5.84  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 13.15/5.84  tff(f_172, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_1)).
% 13.15/5.84  tff(f_192, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relset_1)).
% 13.15/5.84  tff(f_202, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 13.15/5.84  tff(c_110, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_254])).
% 13.15/5.84  tff(c_114, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_254])).
% 13.15/5.84  tff(c_1084, plain, (![C_168, A_169, B_170]: (v4_relat_1(C_168, A_169) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))))), inference(cnfTransformation, [status(thm)], [f_182])).
% 13.15/5.84  tff(c_1102, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_114, c_1084])).
% 13.15/5.84  tff(c_608, plain, (![C_107, A_108, B_109]: (v1_relat_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_176])).
% 13.15/5.84  tff(c_622, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_114, c_608])).
% 13.15/5.84  tff(c_32, plain, (![A_19]: (k1_relat_1(A_19)!=k1_xboole_0 | k1_xboole_0=A_19 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_76])).
% 13.15/5.84  tff(c_652, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_622, c_32])).
% 13.15/5.84  tff(c_658, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_652])).
% 13.15/5.84  tff(c_118, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_254])).
% 13.15/5.84  tff(c_46, plain, (![A_23]: (v1_funct_1(k2_funct_1(A_23)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_99])).
% 13.15/5.84  tff(c_108, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_254])).
% 13.15/5.84  tff(c_293, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_108])).
% 13.15/5.84  tff(c_296, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_293])).
% 13.15/5.84  tff(c_299, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_296])).
% 13.15/5.84  tff(c_488, plain, (![C_94, A_95, B_96]: (v1_relat_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_176])).
% 13.15/5.84  tff(c_498, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_114, c_488])).
% 13.15/5.84  tff(c_505, plain, $false, inference(negUnitSimplification, [status(thm)], [c_299, c_498])).
% 13.15/5.84  tff(c_507, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_108])).
% 13.15/5.84  tff(c_112, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_254])).
% 13.15/5.84  tff(c_1455, plain, (![A_203, B_204, C_205]: (k2_relset_1(A_203, B_204, C_205)=k2_relat_1(C_205) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_203, B_204))))), inference(cnfTransformation, [status(thm)], [f_186])).
% 13.15/5.84  tff(c_1468, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_114, c_1455])).
% 13.15/5.84  tff(c_1475, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_1468])).
% 13.15/5.84  tff(c_62, plain, (![A_33]: (k1_relat_1(k2_funct_1(A_33))=k2_relat_1(A_33) | ~v2_funct_1(A_33) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_145])).
% 13.15/5.84  tff(c_48, plain, (![A_23]: (v1_relat_1(k2_funct_1(A_23)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_99])).
% 13.15/5.84  tff(c_791, plain, (![A_122, B_123]: (r2_hidden('#skF_1'(A_122, B_123), A_122) | r1_tarski(A_122, B_123))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.15/5.84  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.15/5.84  tff(c_796, plain, (![A_122]: (r1_tarski(A_122, A_122))), inference(resolution, [status(thm)], [c_791, c_4])).
% 13.15/5.84  tff(c_28, plain, (![A_18]: (k10_relat_1(A_18, k2_relat_1(A_18))=k1_relat_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.15/5.84  tff(c_1492, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1475, c_28])).
% 13.15/5.84  tff(c_1507, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_622, c_1492])).
% 13.15/5.84  tff(c_1688, plain, (![B_212, A_213]: (k9_relat_1(B_212, k10_relat_1(B_212, A_213))=A_213 | ~r1_tarski(A_213, k2_relat_1(B_212)) | ~v1_funct_1(B_212) | ~v1_relat_1(B_212))), inference(cnfTransformation, [status(thm)], [f_111])).
% 13.15/5.84  tff(c_1693, plain, (![A_213]: (k9_relat_1('#skF_4', k10_relat_1('#skF_4', A_213))=A_213 | ~r1_tarski(A_213, '#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1475, c_1688])).
% 13.15/5.84  tff(c_1760, plain, (![A_217]: (k9_relat_1('#skF_4', k10_relat_1('#skF_4', A_217))=A_217 | ~r1_tarski(A_217, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_622, c_118, c_1693])).
% 13.15/5.84  tff(c_1769, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_3' | ~r1_tarski('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1507, c_1760])).
% 13.15/5.84  tff(c_1777, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_796, c_1769])).
% 13.15/5.84  tff(c_2037, plain, (![A_241, B_242]: (k9_relat_1(k2_funct_1(A_241), k9_relat_1(A_241, B_242))=B_242 | ~r1_tarski(B_242, k1_relat_1(A_241)) | ~v2_funct_1(A_241) | ~v1_funct_1(A_241) | ~v1_relat_1(A_241))), inference(cnfTransformation, [status(thm)], [f_122])).
% 13.15/5.84  tff(c_2052, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1777, c_2037])).
% 13.15/5.84  tff(c_2077, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_622, c_118, c_112, c_796, c_2052])).
% 13.15/5.84  tff(c_1359, plain, (![A_195]: (k1_relat_1(k2_funct_1(A_195))=k2_relat_1(A_195) | ~v2_funct_1(A_195) | ~v1_funct_1(A_195) | ~v1_relat_1(A_195))), inference(cnfTransformation, [status(thm)], [f_145])).
% 13.15/5.84  tff(c_26, plain, (![A_17]: (k9_relat_1(A_17, k1_relat_1(A_17))=k2_relat_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.15/5.84  tff(c_8288, plain, (![A_574]: (k9_relat_1(k2_funct_1(A_574), k2_relat_1(A_574))=k2_relat_1(k2_funct_1(A_574)) | ~v1_relat_1(k2_funct_1(A_574)) | ~v2_funct_1(A_574) | ~v1_funct_1(A_574) | ~v1_relat_1(A_574))), inference(superposition, [status(thm), theory('equality')], [c_1359, c_26])).
% 13.15/5.84  tff(c_8315, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1475, c_8288])).
% 13.15/5.84  tff(c_8339, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_622, c_118, c_112, c_2077, c_8315])).
% 13.15/5.84  tff(c_8348, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_8339])).
% 13.15/5.84  tff(c_8357, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_8348])).
% 13.15/5.84  tff(c_8363, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_622, c_118, c_8357])).
% 13.15/5.84  tff(c_8365, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_8339])).
% 13.15/5.84  tff(c_8364, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_8339])).
% 13.15/5.84  tff(c_92, plain, (![A_57]: (v1_funct_2(A_57, k1_relat_1(A_57), k2_relat_1(A_57)) | ~v1_funct_1(A_57) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_218])).
% 13.15/5.84  tff(c_8506, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8364, c_92])).
% 13.15/5.84  tff(c_8600, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8365, c_507, c_8506])).
% 13.15/5.84  tff(c_8769, plain, (v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_62, c_8600])).
% 13.15/5.84  tff(c_8771, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_622, c_118, c_112, c_1475, c_8769])).
% 13.15/5.84  tff(c_90, plain, (![A_57]: (m1_subset_1(A_57, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_57), k2_relat_1(A_57)))) | ~v1_funct_1(A_57) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_218])).
% 13.15/5.84  tff(c_8500, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4')))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8364, c_90])).
% 13.15/5.84  tff(c_8595, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_8365, c_507, c_8500])).
% 13.15/5.84  tff(c_9634, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4')))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_62, c_8595])).
% 13.15/5.84  tff(c_9652, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_622, c_118, c_112, c_1475, c_9634])).
% 13.15/5.84  tff(c_20, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(B_14), A_13) | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 13.15/5.84  tff(c_2660, plain, (![B_295, D_296, A_297, C_298]: (k1_xboole_0=B_295 | m1_subset_1(D_296, k1_zfmisc_1(k2_zfmisc_1(A_297, C_298))) | ~r1_tarski(B_295, C_298) | ~m1_subset_1(D_296, k1_zfmisc_1(k2_zfmisc_1(A_297, B_295))) | ~v1_funct_2(D_296, A_297, B_295) | ~v1_funct_1(D_296))), inference(cnfTransformation, [status(thm)], [f_237])).
% 13.15/5.84  tff(c_15222, plain, (![B_890, D_891, A_892, A_893]: (k1_relat_1(B_890)=k1_xboole_0 | m1_subset_1(D_891, k1_zfmisc_1(k2_zfmisc_1(A_892, A_893))) | ~m1_subset_1(D_891, k1_zfmisc_1(k2_zfmisc_1(A_892, k1_relat_1(B_890)))) | ~v1_funct_2(D_891, A_892, k1_relat_1(B_890)) | ~v1_funct_1(D_891) | ~v4_relat_1(B_890, A_893) | ~v1_relat_1(B_890))), inference(resolution, [status(thm)], [c_20, c_2660])).
% 13.15/5.84  tff(c_15226, plain, (![A_893]: (k1_relat_1('#skF_4')=k1_xboole_0 | m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_893))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v4_relat_1('#skF_4', A_893) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_9652, c_15222])).
% 13.15/5.84  tff(c_15259, plain, (![A_893]: (k1_relat_1('#skF_4')=k1_xboole_0 | m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_893))) | ~v4_relat_1('#skF_4', A_893))), inference(demodulation, [status(thm), theory('equality')], [c_622, c_507, c_8771, c_15226])).
% 13.15/5.84  tff(c_15390, plain, (![A_900]: (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_900))) | ~v4_relat_1('#skF_4', A_900))), inference(negUnitSimplification, [status(thm)], [c_658, c_15259])).
% 13.15/5.84  tff(c_506, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_108])).
% 13.15/5.84  tff(c_568, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_506])).
% 13.15/5.84  tff(c_15443, plain, (~v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_15390, c_568])).
% 13.15/5.84  tff(c_15493, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1102, c_15443])).
% 13.15/5.84  tff(c_15494, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_652])).
% 13.15/5.84  tff(c_134, plain, (![A_65]: (k6_relat_1(A_65)=k6_partfun1(A_65))), inference(cnfTransformation, [status(thm)], [f_208])).
% 13.15/5.84  tff(c_44, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_91])).
% 13.15/5.84  tff(c_140, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_134, c_44])).
% 13.15/5.84  tff(c_88, plain, (![A_56]: (k6_relat_1(A_56)=k6_partfun1(A_56))), inference(cnfTransformation, [status(thm)], [f_208])).
% 13.15/5.84  tff(c_40, plain, (![A_21]: (k2_relat_1(k6_relat_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.15/5.84  tff(c_173, plain, (![A_67]: (k2_relat_1(k6_partfun1(A_67))=A_67)), inference(demodulation, [status(thm), theory('equality')], [c_88, c_40])).
% 13.15/5.84  tff(c_182, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_140, c_173])).
% 13.15/5.84  tff(c_15504, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15494, c_15494, c_182])).
% 13.15/5.84  tff(c_30, plain, (![A_19]: (k2_relat_1(A_19)!=k1_xboole_0 | k1_xboole_0=A_19 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_76])).
% 13.15/5.84  tff(c_651, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_622, c_30])).
% 13.15/5.84  tff(c_657, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_651])).
% 13.15/5.84  tff(c_15582, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15504, c_15494, c_657])).
% 13.15/5.84  tff(c_15583, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_651])).
% 13.15/5.84  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.15/5.84  tff(c_15666, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15583, c_8])).
% 13.15/5.84  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.15/5.84  tff(c_10, plain, (![A_6, B_7]: (v1_xboole_0(k2_zfmisc_1(A_6, B_7)) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.15/5.84  tff(c_86, plain, (![A_55]: (m1_subset_1(k6_partfun1(A_55), k1_zfmisc_1(k2_zfmisc_1(A_55, A_55))))), inference(cnfTransformation, [status(thm)], [f_206])).
% 13.15/5.84  tff(c_16440, plain, (![C_978, B_979, A_980]: (~v1_xboole_0(C_978) | ~m1_subset_1(B_979, k1_zfmisc_1(C_978)) | ~r2_hidden(A_980, B_979))), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.15/5.84  tff(c_16501, plain, (![A_986, A_987]: (~v1_xboole_0(k2_zfmisc_1(A_986, A_986)) | ~r2_hidden(A_987, k6_partfun1(A_986)))), inference(resolution, [status(thm)], [c_86, c_16440])).
% 13.15/5.84  tff(c_16506, plain, (![A_988, B_989]: (~r2_hidden(A_988, k6_partfun1(B_989)) | ~v1_xboole_0(B_989))), inference(resolution, [status(thm)], [c_10, c_16501])).
% 13.15/5.84  tff(c_16515, plain, (![B_990, B_991]: (~v1_xboole_0(B_990) | r1_tarski(k6_partfun1(B_990), B_991))), inference(resolution, [status(thm)], [c_6, c_16506])).
% 13.15/5.84  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.15/5.84  tff(c_16275, plain, (![C_961, B_962, A_963]: (v5_relat_1(C_961, B_962) | ~m1_subset_1(C_961, k1_zfmisc_1(k2_zfmisc_1(A_963, B_962))))), inference(cnfTransformation, [status(thm)], [f_182])).
% 13.15/5.84  tff(c_16290, plain, (![A_8, B_962, A_963]: (v5_relat_1(A_8, B_962) | ~r1_tarski(A_8, k2_zfmisc_1(A_963, B_962)))), inference(resolution, [status(thm)], [c_14, c_16275])).
% 13.15/5.84  tff(c_16605, plain, (![B_996, B_997]: (v5_relat_1(k6_partfun1(B_996), B_997) | ~v1_xboole_0(B_996))), inference(resolution, [status(thm)], [c_16515, c_16290])).
% 13.15/5.84  tff(c_50, plain, (![A_24]: (v1_relat_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 13.15/5.84  tff(c_123, plain, (![A_24]: (v1_relat_1(k6_partfun1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_50])).
% 13.15/5.84  tff(c_125, plain, (![A_21]: (k2_relat_1(k6_partfun1(A_21))=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_88, c_40])).
% 13.15/5.84  tff(c_16086, plain, (![B_931, A_932]: (r1_tarski(k2_relat_1(B_931), A_932) | ~v5_relat_1(B_931, A_932) | ~v1_relat_1(B_931))), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.15/5.84  tff(c_16096, plain, (![A_21, A_932]: (r1_tarski(A_21, A_932) | ~v5_relat_1(k6_partfun1(A_21), A_932) | ~v1_relat_1(k6_partfun1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_125, c_16086])).
% 13.15/5.84  tff(c_16101, plain, (![A_21, A_932]: (r1_tarski(A_21, A_932) | ~v5_relat_1(k6_partfun1(A_21), A_932))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_16096])).
% 13.15/5.84  tff(c_16613, plain, (![B_998, B_999]: (r1_tarski(B_998, B_999) | ~v1_xboole_0(B_998))), inference(resolution, [status(thm)], [c_16605, c_16101])).
% 13.15/5.84  tff(c_68, plain, (![A_38]: (k2_funct_1(k6_relat_1(A_38))=k6_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.15/5.84  tff(c_193, plain, (![A_68]: (k2_funct_1(k6_partfun1(A_68))=k6_partfun1(A_68))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_88, c_68])).
% 13.15/5.84  tff(c_202, plain, (k6_partfun1(k1_xboole_0)=k2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_140, c_193])).
% 13.15/5.84  tff(c_205, plain, (k2_funct_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_140, c_202])).
% 13.15/5.84  tff(c_15660, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15583, c_15583, c_205])).
% 13.15/5.84  tff(c_607, plain, (~r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_14, c_568])).
% 13.15/5.84  tff(c_15694, plain, (~r1_tarski('#skF_4', k2_zfmisc_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_15660, c_607])).
% 13.15/5.84  tff(c_16638, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_16613, c_15694])).
% 13.15/5.84  tff(c_16648, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15666, c_16638])).
% 13.15/5.84  tff(c_16649, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_506])).
% 13.15/5.84  tff(c_16748, plain, (![A_1007, B_1008]: (r2_hidden('#skF_1'(A_1007, B_1008), A_1007) | r1_tarski(A_1007, B_1008))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.15/5.84  tff(c_16753, plain, (![A_1007]: (r1_tarski(A_1007, A_1007))), inference(resolution, [status(thm)], [c_16748, c_4])).
% 13.15/5.84  tff(c_16754, plain, (![C_1009, A_1010, B_1011]: (v1_relat_1(C_1009) | ~m1_subset_1(C_1009, k1_zfmisc_1(k2_zfmisc_1(A_1010, B_1011))))), inference(cnfTransformation, [status(thm)], [f_176])).
% 13.15/5.84  tff(c_16772, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_114, c_16754])).
% 13.15/5.84  tff(c_17741, plain, (![A_1114, B_1115, C_1116]: (k2_relset_1(A_1114, B_1115, C_1116)=k2_relat_1(C_1116) | ~m1_subset_1(C_1116, k1_zfmisc_1(k2_zfmisc_1(A_1114, B_1115))))), inference(cnfTransformation, [status(thm)], [f_186])).
% 13.15/5.84  tff(c_17760, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_114, c_17741])).
% 13.15/5.84  tff(c_17769, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_17760])).
% 13.15/5.84  tff(c_16650, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_506])).
% 13.15/5.84  tff(c_16768, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_16650, c_16754])).
% 13.15/5.84  tff(c_17789, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_17769, c_28])).
% 13.15/5.84  tff(c_17806, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16772, c_17789])).
% 13.15/5.84  tff(c_17861, plain, (![B_1119, A_1120]: (k9_relat_1(B_1119, k10_relat_1(B_1119, A_1120))=A_1120 | ~r1_tarski(A_1120, k2_relat_1(B_1119)) | ~v1_funct_1(B_1119) | ~v1_relat_1(B_1119))), inference(cnfTransformation, [status(thm)], [f_111])).
% 13.15/5.84  tff(c_17863, plain, (![A_1120]: (k9_relat_1('#skF_4', k10_relat_1('#skF_4', A_1120))=A_1120 | ~r1_tarski(A_1120, '#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_17769, c_17861])).
% 13.15/5.84  tff(c_18012, plain, (![A_1130]: (k9_relat_1('#skF_4', k10_relat_1('#skF_4', A_1130))=A_1130 | ~r1_tarski(A_1130, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_16772, c_118, c_17863])).
% 13.15/5.84  tff(c_18021, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_3' | ~r1_tarski('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_17806, c_18012])).
% 13.15/5.84  tff(c_18029, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16753, c_18021])).
% 13.15/5.84  tff(c_18288, plain, (![A_1150, B_1151]: (k9_relat_1(k2_funct_1(A_1150), k9_relat_1(A_1150, B_1151))=B_1151 | ~r1_tarski(B_1151, k1_relat_1(A_1150)) | ~v2_funct_1(A_1150) | ~v1_funct_1(A_1150) | ~v1_relat_1(A_1150))), inference(cnfTransformation, [status(thm)], [f_122])).
% 13.15/5.84  tff(c_18303, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18029, c_18288])).
% 13.15/5.84  tff(c_18328, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16772, c_118, c_112, c_16753, c_18303])).
% 13.15/5.84  tff(c_17546, plain, (![A_1096]: (k1_relat_1(k2_funct_1(A_1096))=k2_relat_1(A_1096) | ~v2_funct_1(A_1096) | ~v1_funct_1(A_1096) | ~v1_relat_1(A_1096))), inference(cnfTransformation, [status(thm)], [f_145])).
% 13.15/5.84  tff(c_24137, plain, (![A_1419]: (k9_relat_1(k2_funct_1(A_1419), k2_relat_1(A_1419))=k2_relat_1(k2_funct_1(A_1419)) | ~v1_relat_1(k2_funct_1(A_1419)) | ~v2_funct_1(A_1419) | ~v1_funct_1(A_1419) | ~v1_relat_1(A_1419))), inference(superposition, [status(thm), theory('equality')], [c_17546, c_26])).
% 13.15/5.84  tff(c_24164, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_17769, c_24137])).
% 13.15/5.84  tff(c_24188, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16772, c_118, c_112, c_16768, c_18328, c_24164])).
% 13.15/5.84  tff(c_24285, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_24188, c_92])).
% 13.15/5.84  tff(c_24368, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_16768, c_507, c_24285])).
% 13.15/5.84  tff(c_24624, plain, (v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_62, c_24368])).
% 13.15/5.84  tff(c_24626, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_16772, c_118, c_112, c_17769, c_24624])).
% 13.15/5.84  tff(c_18082, plain, (![D_1132, C_1133, B_1134, A_1135]: (m1_subset_1(D_1132, k1_zfmisc_1(k2_zfmisc_1(C_1133, B_1134))) | ~r1_tarski(k2_relat_1(D_1132), B_1134) | ~m1_subset_1(D_1132, k1_zfmisc_1(k2_zfmisc_1(C_1133, A_1135))))), inference(cnfTransformation, [status(thm)], [f_192])).
% 13.15/5.84  tff(c_18104, plain, (![B_1134]: (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_1134))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_4')), B_1134))), inference(resolution, [status(thm)], [c_16650, c_18082])).
% 13.15/5.84  tff(c_24209, plain, (![B_1134]: (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_1134))) | ~r1_tarski(k1_relat_1('#skF_4'), B_1134))), inference(demodulation, [status(thm), theory('equality')], [c_24188, c_18104])).
% 13.15/5.84  tff(c_16784, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_16772, c_32])).
% 13.15/5.84  tff(c_16823, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_16784])).
% 13.15/5.84  tff(c_16996, plain, (![C_1028, B_1029, A_1030]: (v5_relat_1(C_1028, B_1029) | ~m1_subset_1(C_1028, k1_zfmisc_1(k2_zfmisc_1(A_1030, B_1029))))), inference(cnfTransformation, [status(thm)], [f_182])).
% 13.15/5.84  tff(c_17014, plain, (v5_relat_1(k2_funct_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_16650, c_16996])).
% 13.15/5.84  tff(c_24, plain, (![B_16, A_15]: (r1_tarski(k2_relat_1(B_16), A_15) | ~v5_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.15/5.84  tff(c_24294, plain, (![A_15]: (r1_tarski(k1_relat_1('#skF_4'), A_15) | ~v5_relat_1(k2_funct_1('#skF_4'), A_15) | ~v1_relat_1(k2_funct_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_24188, c_24])).
% 13.15/5.84  tff(c_24484, plain, (![A_1426]: (r1_tarski(k1_relat_1('#skF_4'), A_1426) | ~v5_relat_1(k2_funct_1('#skF_4'), A_1426))), inference(demodulation, [status(thm), theory('equality')], [c_16768, c_24294])).
% 13.15/5.84  tff(c_24539, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_17014, c_24484])).
% 13.15/5.84  tff(c_102, plain, (![B_59, D_61, A_58, C_60]: (k1_xboole_0=B_59 | v1_funct_2(D_61, A_58, C_60) | ~r1_tarski(B_59, C_60) | ~m1_subset_1(D_61, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))) | ~v1_funct_2(D_61, A_58, B_59) | ~v1_funct_1(D_61))), inference(cnfTransformation, [status(thm)], [f_237])).
% 13.15/5.84  tff(c_24550, plain, (![D_61, A_58]: (k1_relat_1('#skF_4')=k1_xboole_0 | v1_funct_2(D_61, A_58, '#skF_2') | ~m1_subset_1(D_61, k1_zfmisc_1(k2_zfmisc_1(A_58, k1_relat_1('#skF_4')))) | ~v1_funct_2(D_61, A_58, k1_relat_1('#skF_4')) | ~v1_funct_1(D_61))), inference(resolution, [status(thm)], [c_24539, c_102])).
% 13.15/5.84  tff(c_24906, plain, (![D_1440, A_1441]: (v1_funct_2(D_1440, A_1441, '#skF_2') | ~m1_subset_1(D_1440, k1_zfmisc_1(k2_zfmisc_1(A_1441, k1_relat_1('#skF_4')))) | ~v1_funct_2(D_1440, A_1441, k1_relat_1('#skF_4')) | ~v1_funct_1(D_1440))), inference(negUnitSimplification, [status(thm)], [c_16823, c_24550])).
% 13.15/5.84  tff(c_24910, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_24209, c_24906])).
% 13.15/5.84  tff(c_24941, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16753, c_507, c_24626, c_24910])).
% 13.15/5.84  tff(c_24943, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16649, c_24941])).
% 13.15/5.84  tff(c_24944, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_16784])).
% 13.15/5.84  tff(c_24957, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24944, c_24944, c_182])).
% 13.15/5.84  tff(c_16783, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_16772, c_30])).
% 13.15/5.84  tff(c_16798, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_16783])).
% 13.15/5.84  tff(c_24947, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24944, c_16798])).
% 13.15/5.84  tff(c_25040, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24957, c_24947])).
% 13.15/5.84  tff(c_25041, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_16783])).
% 13.15/5.84  tff(c_25042, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_16783])).
% 13.15/5.84  tff(c_25290, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_25041, c_25042])).
% 13.15/5.84  tff(c_27066, plain, (![A_1627, B_1628, C_1629]: (k2_relset_1(A_1627, B_1628, C_1629)=k2_relat_1(C_1629) | ~m1_subset_1(C_1629, k1_zfmisc_1(k2_zfmisc_1(A_1627, B_1628))))), inference(cnfTransformation, [status(thm)], [f_186])).
% 13.15/5.84  tff(c_27085, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_114, c_27066])).
% 13.15/5.84  tff(c_27095, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_25290, c_27085])).
% 13.15/5.84  tff(c_25245, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_25041, c_25041, c_205])).
% 13.15/5.84  tff(c_25316, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_25245, c_16649])).
% 13.15/5.84  tff(c_27099, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_27095, c_25316])).
% 13.15/5.84  tff(c_38, plain, (![A_21]: (k1_relat_1(k6_relat_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.15/5.84  tff(c_126, plain, (![A_21]: (k1_relat_1(k6_partfun1(A_21))=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_88, c_38])).
% 13.15/5.84  tff(c_237, plain, (![A_73]: (k1_relat_1(A_73)!=k1_xboole_0 | k1_xboole_0=A_73 | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_76])).
% 13.15/5.84  tff(c_246, plain, (![A_24]: (k1_relat_1(k6_partfun1(A_24))!=k1_xboole_0 | k6_partfun1(A_24)=k1_xboole_0)), inference(resolution, [status(thm)], [c_123, c_237])).
% 13.15/5.84  tff(c_256, plain, (![A_74]: (k1_xboole_0!=A_74 | k6_partfun1(A_74)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_126, c_246])).
% 13.15/5.84  tff(c_84, plain, (![A_55]: (v1_partfun1(k6_partfun1(A_55), A_55))), inference(cnfTransformation, [status(thm)], [f_206])).
% 13.15/5.84  tff(c_271, plain, (![A_74]: (v1_partfun1(k1_xboole_0, A_74) | k1_xboole_0!=A_74)), inference(superposition, [status(thm), theory('equality')], [c_256, c_84])).
% 13.15/5.84  tff(c_25507, plain, (v1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_25041, c_25041, c_271])).
% 13.15/5.84  tff(c_25315, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_25245, c_16650])).
% 13.15/5.84  tff(c_27098, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_27095, c_25315])).
% 13.15/5.84  tff(c_27297, plain, (![C_1636, A_1637, B_1638]: (v1_funct_2(C_1636, A_1637, B_1638) | ~v1_partfun1(C_1636, A_1637) | ~v1_funct_1(C_1636) | ~m1_subset_1(C_1636, k1_zfmisc_1(k2_zfmisc_1(A_1637, B_1638))))), inference(cnfTransformation, [status(thm)], [f_202])).
% 13.15/5.84  tff(c_27303, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_2') | ~v1_partfun1('#skF_4', '#skF_4') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_27098, c_27297])).
% 13.15/5.84  tff(c_27322, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_25507, c_27303])).
% 13.15/5.84  tff(c_27324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27099, c_27322])).
% 13.15/5.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.15/5.84  
% 13.15/5.84  Inference rules
% 13.15/5.84  ----------------------
% 13.15/5.84  #Ref     : 0
% 13.15/5.84  #Sup     : 5873
% 13.15/5.84  #Fact    : 0
% 13.15/5.84  #Define  : 0
% 13.15/5.84  #Split   : 77
% 13.15/5.84  #Chain   : 0
% 13.15/5.84  #Close   : 0
% 13.15/5.84  
% 13.15/5.84  Ordering : KBO
% 13.15/5.84  
% 13.15/5.84  Simplification rules
% 13.15/5.84  ----------------------
% 13.15/5.84  #Subsume      : 1256
% 13.15/5.84  #Demod        : 6011
% 13.15/5.84  #Tautology    : 2063
% 13.15/5.84  #SimpNegUnit  : 117
% 13.15/5.84  #BackRed      : 184
% 13.15/5.84  
% 13.15/5.84  #Partial instantiations: 0
% 13.15/5.84  #Strategies tried      : 1
% 13.15/5.84  
% 13.15/5.84  Timing (in seconds)
% 13.15/5.84  ----------------------
% 13.15/5.85  Preprocessing        : 0.38
% 13.15/5.85  Parsing              : 0.20
% 13.15/5.85  CNF conversion       : 0.03
% 13.15/5.85  Main loop            : 4.66
% 13.15/5.85  Inferencing          : 1.21
% 13.15/5.85  Reduction            : 2.00
% 13.15/5.85  Demodulation         : 1.55
% 13.15/5.85  BG Simplification    : 0.10
% 13.15/5.85  Subsumption          : 1.06
% 13.15/5.85  Abstraction          : 0.12
% 13.15/5.85  MUC search           : 0.00
% 13.15/5.85  Cooper               : 0.00
% 13.15/5.85  Total                : 5.10
% 13.15/5.85  Index Insertion      : 0.00
% 13.15/5.85  Index Deletion       : 0.00
% 13.15/5.85  Index Matching       : 0.00
% 13.15/5.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
