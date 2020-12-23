%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:00 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 265 expanded)
%              Number of leaves         :   38 ( 107 expanded)
%              Depth                    :   11
%              Number of atoms          :  131 ( 551 expanded)
%              Number of equality atoms :   51 ( 135 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_100,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_114,plain,(
    ! [B_45,A_46] :
      ( v1_relat_1(B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_46))
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_117,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_114])).

tff(c_120,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_117])).

tff(c_30,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k9_relat_1(B_20,A_19),k2_relat_1(B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_252,plain,(
    ! [A_75,B_76,C_77,D_78] :
      ( k7_relset_1(A_75,B_76,C_77,D_78) = k9_relat_1(C_77,D_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_255,plain,(
    ! [D_78] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_78) = k9_relat_1('#skF_4',D_78) ),
    inference(resolution,[status(thm)],[c_48,c_252])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_188,plain,(
    ! [B_63,A_64] :
      ( k1_tarski(k1_funct_1(B_63,A_64)) = k2_relat_1(B_63)
      | k1_tarski(A_64) != k1_relat_1(B_63)
      | ~ v1_funct_1(B_63)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_44,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_197,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_44])).

tff(c_203,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_52,c_197])).

tff(c_333,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_203])).

tff(c_334,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_333])).

tff(c_32,plain,(
    ! [A_21] :
      ( k1_relat_1(A_21) = k1_xboole_0
      | k2_relat_1(A_21) != k1_xboole_0
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_127,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_120,c_32])).

tff(c_129,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_34,plain,(
    ! [A_21] :
      ( k2_relat_1(A_21) = k1_xboole_0
      | k1_relat_1(A_21) != k1_xboole_0
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_128,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_120,c_34])).

tff(c_130,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_128])).

tff(c_272,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_203])).

tff(c_273,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_272])).

tff(c_151,plain,(
    ! [C_52,A_53,B_54] :
      ( v4_relat_1(C_52,A_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_155,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_48,c_151])).

tff(c_170,plain,(
    ! [B_61,A_62] :
      ( r1_tarski(k1_relat_1(B_61),A_62)
      | ~ v4_relat_1(B_61,A_62)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( k1_tarski(B_11) = A_10
      | k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_tarski(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_303,plain,(
    ! [B_85,B_86] :
      ( k1_tarski(B_85) = k1_relat_1(B_86)
      | k1_relat_1(B_86) = k1_xboole_0
      | ~ v4_relat_1(B_86,k1_tarski(B_85))
      | ~ v1_relat_1(B_86) ) ),
    inference(resolution,[status(thm)],[c_170,c_16])).

tff(c_309,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_155,c_303])).

tff(c_312,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_309])).

tff(c_314,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_273,c_312])).

tff(c_316,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_272])).

tff(c_36,plain,(
    ! [B_23,A_22] :
      ( k1_tarski(k1_funct_1(B_23,A_22)) = k2_relat_1(B_23)
      | k1_tarski(A_22) != k1_relat_1(B_23)
      | ~ v1_funct_1(B_23)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_256,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_44])).

tff(c_268,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_256])).

tff(c_270,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_52,c_268])).

tff(c_271,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_270])).

tff(c_330,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_271])).

tff(c_332,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_270])).

tff(c_335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_334,c_332])).

tff(c_336,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_333])).

tff(c_353,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_336])).

tff(c_357,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_353])).

tff(c_359,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_367,plain,(
    ! [A_19] :
      ( r1_tarski(k9_relat_1('#skF_4',A_19),k1_xboole_0)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_30])).

tff(c_375,plain,(
    ! [A_87] : r1_tarski(k9_relat_1('#skF_4',A_87),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_367])).

tff(c_82,plain,(
    ! [B_39,A_40] :
      ( B_39 = A_40
      | ~ r1_tarski(B_39,A_40)
      | ~ r1_tarski(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_91,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_82])).

tff(c_381,plain,(
    ! [A_87] : k9_relat_1('#skF_4',A_87) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_375,c_91])).

tff(c_541,plain,(
    ! [A_115,B_116,C_117,D_118] :
      ( k7_relset_1(A_115,B_116,C_117,D_118) = k9_relat_1(C_117,D_118)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_543,plain,(
    ! [D_118] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_118) = k9_relat_1('#skF_4',D_118) ),
    inference(resolution,[status(thm)],[c_48,c_541])).

tff(c_545,plain,(
    ! [D_118] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_118) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_543])).

tff(c_546,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_545,c_44])).

tff(c_549,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_546])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:24:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.38  
% 2.74/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.38  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.74/1.38  
% 2.74/1.38  %Foreground sorts:
% 2.74/1.38  
% 2.74/1.38  
% 2.74/1.38  %Background operators:
% 2.74/1.38  
% 2.74/1.38  
% 2.74/1.38  %Foreground operators:
% 2.74/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.74/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.74/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.74/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.74/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.74/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.74/1.38  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.74/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.74/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.74/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.74/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.74/1.38  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.74/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.74/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.74/1.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.74/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.74/1.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.74/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.74/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.74/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.74/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.74/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.74/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.74/1.38  
% 2.74/1.41  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.74/1.41  tff(f_60, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.74/1.41  tff(f_100, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 2.74/1.41  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.74/1.41  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 2.74/1.41  tff(f_88, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.74/1.41  tff(f_78, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 2.74/1.41  tff(f_70, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 2.74/1.41  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.74/1.41  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.74/1.41  tff(f_45, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.74/1.41  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.74/1.41  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.74/1.41  tff(c_28, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.74/1.41  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.74/1.41  tff(c_114, plain, (![B_45, A_46]: (v1_relat_1(B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(A_46)) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.74/1.41  tff(c_117, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_48, c_114])).
% 2.74/1.41  tff(c_120, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_117])).
% 2.74/1.41  tff(c_30, plain, (![B_20, A_19]: (r1_tarski(k9_relat_1(B_20, A_19), k2_relat_1(B_20)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.74/1.41  tff(c_252, plain, (![A_75, B_76, C_77, D_78]: (k7_relset_1(A_75, B_76, C_77, D_78)=k9_relat_1(C_77, D_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.74/1.41  tff(c_255, plain, (![D_78]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_78)=k9_relat_1('#skF_4', D_78))), inference(resolution, [status(thm)], [c_48, c_252])).
% 2.74/1.41  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.74/1.41  tff(c_188, plain, (![B_63, A_64]: (k1_tarski(k1_funct_1(B_63, A_64))=k2_relat_1(B_63) | k1_tarski(A_64)!=k1_relat_1(B_63) | ~v1_funct_1(B_63) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.74/1.41  tff(c_44, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.74/1.41  tff(c_197, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_188, c_44])).
% 2.74/1.41  tff(c_203, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_52, c_197])).
% 2.74/1.41  tff(c_333, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_255, c_203])).
% 2.74/1.41  tff(c_334, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_333])).
% 2.74/1.41  tff(c_32, plain, (![A_21]: (k1_relat_1(A_21)=k1_xboole_0 | k2_relat_1(A_21)!=k1_xboole_0 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.74/1.41  tff(c_127, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_120, c_32])).
% 2.74/1.41  tff(c_129, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_127])).
% 2.74/1.41  tff(c_34, plain, (![A_21]: (k2_relat_1(A_21)=k1_xboole_0 | k1_relat_1(A_21)!=k1_xboole_0 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.74/1.41  tff(c_128, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_120, c_34])).
% 2.74/1.41  tff(c_130, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_129, c_128])).
% 2.74/1.41  tff(c_272, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_255, c_203])).
% 2.74/1.41  tff(c_273, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_272])).
% 2.74/1.41  tff(c_151, plain, (![C_52, A_53, B_54]: (v4_relat_1(C_52, A_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.74/1.41  tff(c_155, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_151])).
% 2.74/1.41  tff(c_170, plain, (![B_61, A_62]: (r1_tarski(k1_relat_1(B_61), A_62) | ~v4_relat_1(B_61, A_62) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.74/1.41  tff(c_16, plain, (![B_11, A_10]: (k1_tarski(B_11)=A_10 | k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_tarski(B_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.74/1.41  tff(c_303, plain, (![B_85, B_86]: (k1_tarski(B_85)=k1_relat_1(B_86) | k1_relat_1(B_86)=k1_xboole_0 | ~v4_relat_1(B_86, k1_tarski(B_85)) | ~v1_relat_1(B_86))), inference(resolution, [status(thm)], [c_170, c_16])).
% 2.74/1.41  tff(c_309, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_155, c_303])).
% 2.74/1.41  tff(c_312, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_120, c_309])).
% 2.74/1.41  tff(c_314, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_273, c_312])).
% 2.74/1.41  tff(c_316, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_272])).
% 2.74/1.41  tff(c_36, plain, (![B_23, A_22]: (k1_tarski(k1_funct_1(B_23, A_22))=k2_relat_1(B_23) | k1_tarski(A_22)!=k1_relat_1(B_23) | ~v1_funct_1(B_23) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.74/1.41  tff(c_256, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_255, c_44])).
% 2.74/1.41  tff(c_268, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_36, c_256])).
% 2.74/1.41  tff(c_270, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_52, c_268])).
% 2.74/1.41  tff(c_271, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_270])).
% 2.74/1.41  tff(c_330, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_316, c_271])).
% 2.74/1.41  tff(c_332, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_270])).
% 2.74/1.41  tff(c_335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_334, c_332])).
% 2.74/1.41  tff(c_336, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_333])).
% 2.74/1.41  tff(c_353, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_336])).
% 2.74/1.41  tff(c_357, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_120, c_353])).
% 2.74/1.41  tff(c_359, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_127])).
% 2.74/1.41  tff(c_367, plain, (![A_19]: (r1_tarski(k9_relat_1('#skF_4', A_19), k1_xboole_0) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_359, c_30])).
% 2.74/1.41  tff(c_375, plain, (![A_87]: (r1_tarski(k9_relat_1('#skF_4', A_87), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_367])).
% 2.74/1.41  tff(c_82, plain, (![B_39, A_40]: (B_39=A_40 | ~r1_tarski(B_39, A_40) | ~r1_tarski(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.74/1.41  tff(c_91, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_82])).
% 2.74/1.41  tff(c_381, plain, (![A_87]: (k9_relat_1('#skF_4', A_87)=k1_xboole_0)), inference(resolution, [status(thm)], [c_375, c_91])).
% 2.74/1.41  tff(c_541, plain, (![A_115, B_116, C_117, D_118]: (k7_relset_1(A_115, B_116, C_117, D_118)=k9_relat_1(C_117, D_118) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.74/1.41  tff(c_543, plain, (![D_118]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_118)=k9_relat_1('#skF_4', D_118))), inference(resolution, [status(thm)], [c_48, c_541])).
% 2.74/1.41  tff(c_545, plain, (![D_118]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_118)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_381, c_543])).
% 2.74/1.41  tff(c_546, plain, (~r1_tarski(k1_xboole_0, k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_545, c_44])).
% 2.74/1.41  tff(c_549, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_546])).
% 2.74/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.41  
% 2.74/1.41  Inference rules
% 2.74/1.41  ----------------------
% 2.74/1.41  #Ref     : 0
% 2.74/1.41  #Sup     : 95
% 2.74/1.41  #Fact    : 0
% 2.74/1.41  #Define  : 0
% 2.74/1.41  #Split   : 5
% 2.74/1.41  #Chain   : 0
% 2.74/1.41  #Close   : 0
% 2.74/1.41  
% 2.74/1.41  Ordering : KBO
% 2.74/1.41  
% 2.74/1.41  Simplification rules
% 2.74/1.41  ----------------------
% 2.74/1.41  #Subsume      : 5
% 2.74/1.41  #Demod        : 64
% 2.74/1.41  #Tautology    : 57
% 2.74/1.41  #SimpNegUnit  : 3
% 2.74/1.41  #BackRed      : 11
% 2.74/1.41  
% 2.74/1.41  #Partial instantiations: 0
% 2.74/1.41  #Strategies tried      : 1
% 2.74/1.41  
% 2.74/1.41  Timing (in seconds)
% 2.74/1.41  ----------------------
% 2.74/1.42  Preprocessing        : 0.34
% 2.74/1.42  Parsing              : 0.18
% 2.74/1.42  CNF conversion       : 0.02
% 2.74/1.42  Main loop            : 0.30
% 2.74/1.42  Inferencing          : 0.11
% 2.74/1.42  Reduction            : 0.09
% 2.74/1.42  Demodulation         : 0.07
% 2.74/1.42  BG Simplification    : 0.02
% 2.74/1.42  Subsumption          : 0.05
% 2.74/1.42  Abstraction          : 0.02
% 2.74/1.42  MUC search           : 0.00
% 2.74/1.42  Cooper               : 0.00
% 2.74/1.42  Total                : 0.69
% 2.74/1.42  Index Insertion      : 0.00
% 2.74/1.42  Index Deletion       : 0.00
% 2.74/1.42  Index Matching       : 0.00
% 2.74/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
