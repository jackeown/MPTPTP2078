%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:00 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 266 expanded)
%              Number of leaves         :   39 ( 105 expanded)
%              Depth                    :   10
%              Number of atoms          :  131 ( 538 expanded)
%              Number of equality atoms :   54 ( 151 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_64,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_71,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_32,plain,(
    ! [A_16,B_17] : v1_relat_1(k2_zfmisc_1(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_151,plain,(
    ! [B_44,A_45] :
      ( v1_relat_1(B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_154,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_56,c_151])).

tff(c_157,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_154])).

tff(c_34,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k9_relat_1(B_19,A_18),k2_relat_1(B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_42,plain,(
    ! [A_20] :
      ( k1_relat_1(A_20) != k1_xboole_0
      | k1_xboole_0 = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_165,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_157,c_42])).

tff(c_167,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_165])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_333,plain,(
    ! [B_76,A_77] :
      ( k1_tarski(k1_funct_1(B_76,A_77)) = k2_relat_1(B_76)
      | k1_tarski(A_77) != k1_relat_1(B_76)
      | ~ v1_funct_1(B_76)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_52,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_342,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_52])).

tff(c_348,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_60,c_342])).

tff(c_372,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_348])).

tff(c_237,plain,(
    ! [C_54,A_55,B_56] :
      ( v4_relat_1(C_54,A_55)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_247,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_56,c_237])).

tff(c_250,plain,(
    ! [B_60,A_61] :
      ( r1_tarski(k1_relat_1(B_60),A_61)
      | ~ v4_relat_1(B_60,A_61)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( k1_tarski(B_8) = A_7
      | k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_tarski(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_409,plain,(
    ! [B_93,B_94] :
      ( k1_tarski(B_93) = k1_relat_1(B_94)
      | k1_relat_1(B_94) = k1_xboole_0
      | ~ v4_relat_1(B_94,k1_tarski(B_93))
      | ~ v1_relat_1(B_94) ) ),
    inference(resolution,[status(thm)],[c_250,c_14])).

tff(c_419,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_247,c_409])).

tff(c_425,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_419])).

tff(c_427,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_372,c_425])).

tff(c_429,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_348])).

tff(c_432,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_56])).

tff(c_512,plain,(
    ! [A_100,B_101,C_102,D_103] :
      ( k7_relset_1(A_100,B_101,C_102,D_103) = k9_relat_1(C_102,D_103)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_519,plain,(
    ! [D_103] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_103) = k9_relat_1('#skF_4',D_103) ),
    inference(resolution,[status(thm)],[c_432,c_512])).

tff(c_428,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_348])).

tff(c_458,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_428])).

tff(c_521,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_458])).

tff(c_533,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_521])).

tff(c_537,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_533])).

tff(c_538,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_36,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_548,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_538,c_36])).

tff(c_40,plain,(
    ! [A_20] :
      ( k2_relat_1(A_20) != k1_xboole_0
      | k1_xboole_0 = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_164,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_157,c_40])).

tff(c_166,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_540,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_166])).

tff(c_572,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_548,c_540])).

tff(c_573,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_599,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_8])).

tff(c_75,plain,(
    ! [A_34] : k2_zfmisc_1(A_34,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_79,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_32])).

tff(c_144,plain,(
    ! [B_41,A_42] :
      ( r1_tarski(k9_relat_1(B_41,A_42),k2_relat_1(B_41))
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_147,plain,(
    ! [A_42] :
      ( r1_tarski(k9_relat_1(k1_xboole_0,A_42),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_144])).

tff(c_149,plain,(
    ! [A_42] : r1_tarski(k9_relat_1(k1_xboole_0,A_42),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_147])).

tff(c_575,plain,(
    ! [B_106,A_107] :
      ( B_106 = A_107
      | ~ r1_tarski(B_106,A_107)
      | ~ r1_tarski(A_107,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_577,plain,(
    ! [A_42] :
      ( k9_relat_1(k1_xboole_0,A_42) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k9_relat_1(k1_xboole_0,A_42)) ) ),
    inference(resolution,[status(thm)],[c_149,c_575])).

tff(c_586,plain,(
    ! [A_42] : k9_relat_1(k1_xboole_0,A_42) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_577])).

tff(c_668,plain,(
    ! [A_42] : k9_relat_1('#skF_4',A_42) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_573,c_586])).

tff(c_885,plain,(
    ! [A_147,B_148,C_149,D_150] :
      ( k7_relset_1(A_147,B_148,C_149,D_150) = k9_relat_1(C_149,D_150)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_891,plain,(
    ! [D_150] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_150) = k9_relat_1('#skF_4',D_150) ),
    inference(resolution,[status(thm)],[c_56,c_885])).

tff(c_893,plain,(
    ! [D_150] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_150) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_668,c_891])).

tff(c_894,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_893,c_52])).

tff(c_897,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_894])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:11:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.44  
% 2.69/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.44  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.69/1.44  
% 2.69/1.44  %Foreground sorts:
% 2.69/1.44  
% 2.69/1.44  
% 2.69/1.44  %Background operators:
% 2.69/1.44  
% 2.69/1.44  
% 2.69/1.44  %Foreground operators:
% 2.69/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.69/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.69/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.69/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.69/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.69/1.44  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.69/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.69/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.69/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.69/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.69/1.44  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.69/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.69/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.69/1.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.69/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.69/1.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.69/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.69/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.69/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.69/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.69/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.69/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.69/1.44  
% 3.09/1.46  tff(f_64, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.09/1.46  tff(f_109, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 3.09/1.46  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.09/1.46  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 3.09/1.46  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.09/1.46  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.09/1.46  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.09/1.46  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.09/1.46  tff(f_43, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.09/1.46  tff(f_97, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.09/1.46  tff(f_71, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.09/1.46  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.09/1.46  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.09/1.46  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.09/1.46  tff(c_32, plain, (![A_16, B_17]: (v1_relat_1(k2_zfmisc_1(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.09/1.46  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.09/1.46  tff(c_151, plain, (![B_44, A_45]: (v1_relat_1(B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.09/1.46  tff(c_154, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_56, c_151])).
% 3.09/1.46  tff(c_157, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_154])).
% 3.09/1.46  tff(c_34, plain, (![B_19, A_18]: (r1_tarski(k9_relat_1(B_19, A_18), k2_relat_1(B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.09/1.46  tff(c_42, plain, (![A_20]: (k1_relat_1(A_20)!=k1_xboole_0 | k1_xboole_0=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.09/1.46  tff(c_165, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_157, c_42])).
% 3.09/1.46  tff(c_167, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_165])).
% 3.09/1.46  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.09/1.46  tff(c_333, plain, (![B_76, A_77]: (k1_tarski(k1_funct_1(B_76, A_77))=k2_relat_1(B_76) | k1_tarski(A_77)!=k1_relat_1(B_76) | ~v1_funct_1(B_76) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.09/1.46  tff(c_52, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.09/1.46  tff(c_342, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_333, c_52])).
% 3.09/1.46  tff(c_348, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_157, c_60, c_342])).
% 3.09/1.46  tff(c_372, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_348])).
% 3.09/1.46  tff(c_237, plain, (![C_54, A_55, B_56]: (v4_relat_1(C_54, A_55) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.09/1.46  tff(c_247, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_56, c_237])).
% 3.09/1.46  tff(c_250, plain, (![B_60, A_61]: (r1_tarski(k1_relat_1(B_60), A_61) | ~v4_relat_1(B_60, A_61) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.09/1.46  tff(c_14, plain, (![B_8, A_7]: (k1_tarski(B_8)=A_7 | k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_tarski(B_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.09/1.46  tff(c_409, plain, (![B_93, B_94]: (k1_tarski(B_93)=k1_relat_1(B_94) | k1_relat_1(B_94)=k1_xboole_0 | ~v4_relat_1(B_94, k1_tarski(B_93)) | ~v1_relat_1(B_94))), inference(resolution, [status(thm)], [c_250, c_14])).
% 3.09/1.46  tff(c_419, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_247, c_409])).
% 3.09/1.46  tff(c_425, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_157, c_419])).
% 3.09/1.46  tff(c_427, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_372, c_425])).
% 3.09/1.46  tff(c_429, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_348])).
% 3.09/1.46  tff(c_432, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_429, c_56])).
% 3.09/1.46  tff(c_512, plain, (![A_100, B_101, C_102, D_103]: (k7_relset_1(A_100, B_101, C_102, D_103)=k9_relat_1(C_102, D_103) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.09/1.46  tff(c_519, plain, (![D_103]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_103)=k9_relat_1('#skF_4', D_103))), inference(resolution, [status(thm)], [c_432, c_512])).
% 3.09/1.46  tff(c_428, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_348])).
% 3.09/1.46  tff(c_458, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_429, c_428])).
% 3.09/1.46  tff(c_521, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_519, c_458])).
% 3.09/1.46  tff(c_533, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_521])).
% 3.09/1.46  tff(c_537, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_157, c_533])).
% 3.09/1.46  tff(c_538, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_165])).
% 3.09/1.46  tff(c_36, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.09/1.46  tff(c_548, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_538, c_538, c_36])).
% 3.09/1.46  tff(c_40, plain, (![A_20]: (k2_relat_1(A_20)!=k1_xboole_0 | k1_xboole_0=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.09/1.46  tff(c_164, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_157, c_40])).
% 3.09/1.46  tff(c_166, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_164])).
% 3.09/1.46  tff(c_540, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_538, c_166])).
% 3.09/1.46  tff(c_572, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_548, c_540])).
% 3.09/1.46  tff(c_573, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_164])).
% 3.09/1.46  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.09/1.46  tff(c_599, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_573, c_8])).
% 3.09/1.46  tff(c_75, plain, (![A_34]: (k2_zfmisc_1(A_34, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.09/1.46  tff(c_79, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_75, c_32])).
% 3.09/1.46  tff(c_144, plain, (![B_41, A_42]: (r1_tarski(k9_relat_1(B_41, A_42), k2_relat_1(B_41)) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.09/1.46  tff(c_147, plain, (![A_42]: (r1_tarski(k9_relat_1(k1_xboole_0, A_42), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_144])).
% 3.09/1.46  tff(c_149, plain, (![A_42]: (r1_tarski(k9_relat_1(k1_xboole_0, A_42), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_147])).
% 3.09/1.46  tff(c_575, plain, (![B_106, A_107]: (B_106=A_107 | ~r1_tarski(B_106, A_107) | ~r1_tarski(A_107, B_106))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.09/1.46  tff(c_577, plain, (![A_42]: (k9_relat_1(k1_xboole_0, A_42)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k9_relat_1(k1_xboole_0, A_42)))), inference(resolution, [status(thm)], [c_149, c_575])).
% 3.09/1.46  tff(c_586, plain, (![A_42]: (k9_relat_1(k1_xboole_0, A_42)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_577])).
% 3.09/1.46  tff(c_668, plain, (![A_42]: (k9_relat_1('#skF_4', A_42)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_573, c_573, c_586])).
% 3.09/1.46  tff(c_885, plain, (![A_147, B_148, C_149, D_150]: (k7_relset_1(A_147, B_148, C_149, D_150)=k9_relat_1(C_149, D_150) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.09/1.46  tff(c_891, plain, (![D_150]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_150)=k9_relat_1('#skF_4', D_150))), inference(resolution, [status(thm)], [c_56, c_885])).
% 3.09/1.46  tff(c_893, plain, (![D_150]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_150)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_668, c_891])).
% 3.09/1.46  tff(c_894, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_893, c_52])).
% 3.09/1.46  tff(c_897, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_599, c_894])).
% 3.09/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.46  
% 3.09/1.46  Inference rules
% 3.09/1.46  ----------------------
% 3.09/1.46  #Ref     : 0
% 3.09/1.46  #Sup     : 168
% 3.09/1.46  #Fact    : 0
% 3.09/1.46  #Define  : 0
% 3.09/1.46  #Split   : 4
% 3.09/1.46  #Chain   : 0
% 3.09/1.46  #Close   : 0
% 3.09/1.46  
% 3.09/1.46  Ordering : KBO
% 3.09/1.46  
% 3.09/1.46  Simplification rules
% 3.09/1.46  ----------------------
% 3.09/1.46  #Subsume      : 13
% 3.09/1.46  #Demod        : 189
% 3.09/1.46  #Tautology    : 112
% 3.09/1.46  #SimpNegUnit  : 3
% 3.09/1.46  #BackRed      : 30
% 3.09/1.46  
% 3.09/1.46  #Partial instantiations: 0
% 3.09/1.46  #Strategies tried      : 1
% 3.09/1.46  
% 3.09/1.46  Timing (in seconds)
% 3.09/1.46  ----------------------
% 3.09/1.46  Preprocessing        : 0.32
% 3.09/1.46  Parsing              : 0.17
% 3.09/1.46  CNF conversion       : 0.02
% 3.09/1.46  Main loop            : 0.34
% 3.09/1.46  Inferencing          : 0.12
% 3.09/1.46  Reduction            : 0.12
% 3.09/1.46  Demodulation         : 0.08
% 3.09/1.46  BG Simplification    : 0.02
% 3.09/1.46  Subsumption          : 0.06
% 3.09/1.46  Abstraction          : 0.01
% 3.09/1.46  MUC search           : 0.00
% 3.09/1.46  Cooper               : 0.00
% 3.09/1.46  Total                : 0.70
% 3.09/1.46  Index Insertion      : 0.00
% 3.09/1.46  Index Deletion       : 0.00
% 3.09/1.46  Index Matching       : 0.00
% 3.09/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
