%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:49 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 262 expanded)
%              Number of leaves         :   43 ( 107 expanded)
%              Depth                    :   14
%              Number of atoms          :  181 ( 559 expanded)
%              Number of equality atoms :   96 ( 206 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_130,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_118,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(D,k1_enumset1(A,B,C))
    <=> ~ ( D != k1_xboole_0
          & D != k1_tarski(A)
          & D != k1_tarski(B)
          & D != k1_tarski(C)
          & D != k2_tarski(A,B)
          & D != k2_tarski(B,C)
          & D != k2_tarski(A,C)
          & D != k1_enumset1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_83,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_184,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_188,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_184])).

tff(c_32,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k9_relat_1(B_15,A_14),k2_relat_1(B_15))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_44,plain,(
    ! [A_20] :
      ( k1_relat_1(A_20) != k1_xboole_0
      | k1_xboole_0 = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_195,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_188,c_44])).

tff(c_197,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_195])).

tff(c_339,plain,(
    ! [A_98,B_99,C_100,D_101] :
      ( k7_relset_1(A_98,B_99,C_100,D_101) = k9_relat_1(C_100,D_101)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_342,plain,(
    ! [D_101] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_101) = k9_relat_1('#skF_4',D_101) ),
    inference(resolution,[status(thm)],[c_66,c_339])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_343,plain,(
    ! [B_102,A_103] :
      ( k1_tarski(k1_funct_1(B_102,A_103)) = k2_relat_1(B_102)
      | k1_tarski(A_103) != k1_relat_1(B_102)
      | ~ v1_funct_1(B_102)
      | ~ v1_relat_1(B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_62,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_358,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_62])).

tff(c_376,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_70,c_358])).

tff(c_394,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_376])).

tff(c_395,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_394])).

tff(c_231,plain,(
    ! [C_77,A_78,B_79] :
      ( v4_relat_1(C_77,A_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_235,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_66,c_231])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k1_relat_1(B_13),A_12)
      | ~ v4_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_422,plain,(
    ! [A_109,B_110,C_111,D_112] :
      ( k1_enumset1(A_109,B_110,C_111) = D_112
      | k2_tarski(A_109,C_111) = D_112
      | k2_tarski(B_110,C_111) = D_112
      | k2_tarski(A_109,B_110) = D_112
      | k1_tarski(C_111) = D_112
      | k1_tarski(B_110) = D_112
      | k1_tarski(A_109) = D_112
      | k1_xboole_0 = D_112
      | ~ r1_tarski(D_112,k1_enumset1(A_109,B_110,C_111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_441,plain,(
    ! [A_3,B_4,D_112] :
      ( k1_enumset1(A_3,A_3,B_4) = D_112
      | k2_tarski(A_3,B_4) = D_112
      | k2_tarski(A_3,B_4) = D_112
      | k2_tarski(A_3,A_3) = D_112
      | k1_tarski(B_4) = D_112
      | k1_tarski(A_3) = D_112
      | k1_tarski(A_3) = D_112
      | k1_xboole_0 = D_112
      | ~ r1_tarski(D_112,k2_tarski(A_3,B_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_422])).

tff(c_584,plain,(
    ! [A_138,B_139,D_140] :
      ( k2_tarski(A_138,B_139) = D_140
      | k2_tarski(A_138,B_139) = D_140
      | k2_tarski(A_138,B_139) = D_140
      | k1_tarski(A_138) = D_140
      | k1_tarski(B_139) = D_140
      | k1_tarski(A_138) = D_140
      | k1_tarski(A_138) = D_140
      | k1_xboole_0 = D_140
      | ~ r1_tarski(D_140,k2_tarski(A_138,B_139)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_441])).

tff(c_623,plain,(
    ! [A_141,B_142,B_143] :
      ( k2_tarski(A_141,B_142) = k1_relat_1(B_143)
      | k1_tarski(B_142) = k1_relat_1(B_143)
      | k1_tarski(A_141) = k1_relat_1(B_143)
      | k1_relat_1(B_143) = k1_xboole_0
      | ~ v4_relat_1(B_143,k2_tarski(A_141,B_142))
      | ~ v1_relat_1(B_143) ) ),
    inference(resolution,[status(thm)],[c_30,c_584])).

tff(c_630,plain,(
    ! [A_2,B_143] :
      ( k2_tarski(A_2,A_2) = k1_relat_1(B_143)
      | k1_tarski(A_2) = k1_relat_1(B_143)
      | k1_tarski(A_2) = k1_relat_1(B_143)
      | k1_relat_1(B_143) = k1_xboole_0
      | ~ v4_relat_1(B_143,k1_tarski(A_2))
      | ~ v1_relat_1(B_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_623])).

tff(c_635,plain,(
    ! [A_144,B_145] :
      ( k1_tarski(A_144) = k1_relat_1(B_145)
      | k1_tarski(A_144) = k1_relat_1(B_145)
      | k1_tarski(A_144) = k1_relat_1(B_145)
      | k1_relat_1(B_145) = k1_xboole_0
      | ~ v4_relat_1(B_145,k1_tarski(A_144))
      | ~ v1_relat_1(B_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_630])).

tff(c_641,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_235,c_635])).

tff(c_648,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_641])).

tff(c_650,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_395,c_648])).

tff(c_652,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_394])).

tff(c_52,plain,(
    ! [B_23,A_22] :
      ( k1_tarski(k1_funct_1(B_23,A_22)) = k2_relat_1(B_23)
      | k1_tarski(A_22) != k1_relat_1(B_23)
      | ~ v1_funct_1(B_23)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_378,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_62])).

tff(c_390,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_378])).

tff(c_392,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_70,c_390])).

tff(c_393,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_392])).

tff(c_693,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_393])).

tff(c_694,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_392])).

tff(c_823,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_694])).

tff(c_827,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_823])).

tff(c_828,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_838,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_828,c_2])).

tff(c_38,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_839,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_828,c_828,c_38])).

tff(c_40,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_840,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_828,c_828,c_40])).

tff(c_1007,plain,(
    ! [B_179,A_180] :
      ( v4_relat_1(B_179,A_180)
      | ~ r1_tarski(k1_relat_1(B_179),A_180)
      | ~ v1_relat_1(B_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1013,plain,(
    ! [A_180] :
      ( v4_relat_1('#skF_4',A_180)
      | ~ r1_tarski('#skF_4',A_180)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_840,c_1007])).

tff(c_1018,plain,(
    ! [A_181] : v4_relat_1('#skF_4',A_181) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_838,c_1013])).

tff(c_36,plain,(
    ! [B_19,A_18] :
      ( k7_relat_1(B_19,A_18) = B_19
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1021,plain,(
    ! [A_181] :
      ( k7_relat_1('#skF_4',A_181) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1018,c_36])).

tff(c_1026,plain,(
    ! [A_182] : k7_relat_1('#skF_4',A_182) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_1021])).

tff(c_34,plain,(
    ! [B_17,A_16] :
      ( k2_relat_1(k7_relat_1(B_17,A_16)) = k9_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1031,plain,(
    ! [A_182] :
      ( k9_relat_1('#skF_4',A_182) = k2_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1026,c_34])).

tff(c_1036,plain,(
    ! [A_182] : k9_relat_1('#skF_4',A_182) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_839,c_1031])).

tff(c_1094,plain,(
    ! [A_189,B_190,C_191,D_192] :
      ( k7_relset_1(A_189,B_190,C_191,D_192) = k9_relat_1(C_191,D_192)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1096,plain,(
    ! [D_192] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_192) = k9_relat_1('#skF_4',D_192) ),
    inference(resolution,[status(thm)],[c_66,c_1094])).

tff(c_1098,plain,(
    ! [D_192] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_192) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1036,c_1096])).

tff(c_1099,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1098,c_62])).

tff(c_1102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_838,c_1099])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:50:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/1.52  
% 3.40/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/1.52  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.40/1.52  
% 3.40/1.52  %Foreground sorts:
% 3.40/1.52  
% 3.40/1.52  
% 3.40/1.52  %Background operators:
% 3.40/1.52  
% 3.40/1.52  
% 3.40/1.52  %Foreground operators:
% 3.40/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.40/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.40/1.52  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.40/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.40/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.40/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.40/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.40/1.52  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.40/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.40/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.40/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.40/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.40/1.52  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.40/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.40/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.40/1.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.40/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.40/1.52  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.40/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.40/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.40/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.40/1.52  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.40/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.40/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.40/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.40/1.52  
% 3.40/1.54  tff(f_130, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 3.40/1.54  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.40/1.54  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 3.40/1.54  tff(f_91, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.40/1.54  tff(f_118, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.40/1.54  tff(f_104, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.40/1.54  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.40/1.54  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.40/1.54  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.40/1.54  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.40/1.54  tff(f_60, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 3.40/1.54  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.40/1.54  tff(f_83, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.40/1.54  tff(f_80, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.40/1.54  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.40/1.54  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.40/1.54  tff(c_184, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.40/1.54  tff(c_188, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_184])).
% 3.40/1.54  tff(c_32, plain, (![B_15, A_14]: (r1_tarski(k9_relat_1(B_15, A_14), k2_relat_1(B_15)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.40/1.54  tff(c_44, plain, (![A_20]: (k1_relat_1(A_20)!=k1_xboole_0 | k1_xboole_0=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.40/1.54  tff(c_195, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_188, c_44])).
% 3.40/1.54  tff(c_197, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_195])).
% 3.40/1.54  tff(c_339, plain, (![A_98, B_99, C_100, D_101]: (k7_relset_1(A_98, B_99, C_100, D_101)=k9_relat_1(C_100, D_101) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.40/1.54  tff(c_342, plain, (![D_101]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_101)=k9_relat_1('#skF_4', D_101))), inference(resolution, [status(thm)], [c_66, c_339])).
% 3.40/1.54  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.40/1.54  tff(c_343, plain, (![B_102, A_103]: (k1_tarski(k1_funct_1(B_102, A_103))=k2_relat_1(B_102) | k1_tarski(A_103)!=k1_relat_1(B_102) | ~v1_funct_1(B_102) | ~v1_relat_1(B_102))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.40/1.54  tff(c_62, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.40/1.54  tff(c_358, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_343, c_62])).
% 3.40/1.54  tff(c_376, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_188, c_70, c_358])).
% 3.40/1.54  tff(c_394, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_342, c_376])).
% 3.40/1.54  tff(c_395, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_394])).
% 3.40/1.54  tff(c_231, plain, (![C_77, A_78, B_79]: (v4_relat_1(C_77, A_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.40/1.54  tff(c_235, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_66, c_231])).
% 3.40/1.54  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.40/1.54  tff(c_30, plain, (![B_13, A_12]: (r1_tarski(k1_relat_1(B_13), A_12) | ~v4_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.40/1.54  tff(c_6, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.40/1.54  tff(c_422, plain, (![A_109, B_110, C_111, D_112]: (k1_enumset1(A_109, B_110, C_111)=D_112 | k2_tarski(A_109, C_111)=D_112 | k2_tarski(B_110, C_111)=D_112 | k2_tarski(A_109, B_110)=D_112 | k1_tarski(C_111)=D_112 | k1_tarski(B_110)=D_112 | k1_tarski(A_109)=D_112 | k1_xboole_0=D_112 | ~r1_tarski(D_112, k1_enumset1(A_109, B_110, C_111)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.40/1.54  tff(c_441, plain, (![A_3, B_4, D_112]: (k1_enumset1(A_3, A_3, B_4)=D_112 | k2_tarski(A_3, B_4)=D_112 | k2_tarski(A_3, B_4)=D_112 | k2_tarski(A_3, A_3)=D_112 | k1_tarski(B_4)=D_112 | k1_tarski(A_3)=D_112 | k1_tarski(A_3)=D_112 | k1_xboole_0=D_112 | ~r1_tarski(D_112, k2_tarski(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_422])).
% 3.40/1.54  tff(c_584, plain, (![A_138, B_139, D_140]: (k2_tarski(A_138, B_139)=D_140 | k2_tarski(A_138, B_139)=D_140 | k2_tarski(A_138, B_139)=D_140 | k1_tarski(A_138)=D_140 | k1_tarski(B_139)=D_140 | k1_tarski(A_138)=D_140 | k1_tarski(A_138)=D_140 | k1_xboole_0=D_140 | ~r1_tarski(D_140, k2_tarski(A_138, B_139)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6, c_441])).
% 3.40/1.54  tff(c_623, plain, (![A_141, B_142, B_143]: (k2_tarski(A_141, B_142)=k1_relat_1(B_143) | k1_tarski(B_142)=k1_relat_1(B_143) | k1_tarski(A_141)=k1_relat_1(B_143) | k1_relat_1(B_143)=k1_xboole_0 | ~v4_relat_1(B_143, k2_tarski(A_141, B_142)) | ~v1_relat_1(B_143))), inference(resolution, [status(thm)], [c_30, c_584])).
% 3.40/1.54  tff(c_630, plain, (![A_2, B_143]: (k2_tarski(A_2, A_2)=k1_relat_1(B_143) | k1_tarski(A_2)=k1_relat_1(B_143) | k1_tarski(A_2)=k1_relat_1(B_143) | k1_relat_1(B_143)=k1_xboole_0 | ~v4_relat_1(B_143, k1_tarski(A_2)) | ~v1_relat_1(B_143))), inference(superposition, [status(thm), theory('equality')], [c_4, c_623])).
% 3.40/1.54  tff(c_635, plain, (![A_144, B_145]: (k1_tarski(A_144)=k1_relat_1(B_145) | k1_tarski(A_144)=k1_relat_1(B_145) | k1_tarski(A_144)=k1_relat_1(B_145) | k1_relat_1(B_145)=k1_xboole_0 | ~v4_relat_1(B_145, k1_tarski(A_144)) | ~v1_relat_1(B_145))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_630])).
% 3.40/1.54  tff(c_641, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_235, c_635])).
% 3.40/1.54  tff(c_648, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_188, c_641])).
% 3.40/1.54  tff(c_650, plain, $false, inference(negUnitSimplification, [status(thm)], [c_197, c_395, c_648])).
% 3.40/1.54  tff(c_652, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_394])).
% 3.40/1.54  tff(c_52, plain, (![B_23, A_22]: (k1_tarski(k1_funct_1(B_23, A_22))=k2_relat_1(B_23) | k1_tarski(A_22)!=k1_relat_1(B_23) | ~v1_funct_1(B_23) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.40/1.54  tff(c_378, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_342, c_62])).
% 3.40/1.54  tff(c_390, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_52, c_378])).
% 3.40/1.54  tff(c_392, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_188, c_70, c_390])).
% 3.40/1.54  tff(c_393, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_392])).
% 3.40/1.54  tff(c_693, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_652, c_393])).
% 3.40/1.54  tff(c_694, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_392])).
% 3.40/1.54  tff(c_823, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_694])).
% 3.40/1.54  tff(c_827, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_188, c_823])).
% 3.40/1.54  tff(c_828, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_195])).
% 3.40/1.54  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.40/1.54  tff(c_838, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_828, c_2])).
% 3.40/1.54  tff(c_38, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.40/1.54  tff(c_839, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_828, c_828, c_38])).
% 3.40/1.54  tff(c_40, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.40/1.54  tff(c_840, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_828, c_828, c_40])).
% 3.40/1.54  tff(c_1007, plain, (![B_179, A_180]: (v4_relat_1(B_179, A_180) | ~r1_tarski(k1_relat_1(B_179), A_180) | ~v1_relat_1(B_179))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.40/1.54  tff(c_1013, plain, (![A_180]: (v4_relat_1('#skF_4', A_180) | ~r1_tarski('#skF_4', A_180) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_840, c_1007])).
% 3.40/1.54  tff(c_1018, plain, (![A_181]: (v4_relat_1('#skF_4', A_181))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_838, c_1013])).
% 3.40/1.54  tff(c_36, plain, (![B_19, A_18]: (k7_relat_1(B_19, A_18)=B_19 | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.40/1.54  tff(c_1021, plain, (![A_181]: (k7_relat_1('#skF_4', A_181)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1018, c_36])).
% 3.40/1.54  tff(c_1026, plain, (![A_182]: (k7_relat_1('#skF_4', A_182)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_188, c_1021])).
% 3.40/1.54  tff(c_34, plain, (![B_17, A_16]: (k2_relat_1(k7_relat_1(B_17, A_16))=k9_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.40/1.54  tff(c_1031, plain, (![A_182]: (k9_relat_1('#skF_4', A_182)=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1026, c_34])).
% 3.40/1.54  tff(c_1036, plain, (![A_182]: (k9_relat_1('#skF_4', A_182)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_188, c_839, c_1031])).
% 3.40/1.54  tff(c_1094, plain, (![A_189, B_190, C_191, D_192]: (k7_relset_1(A_189, B_190, C_191, D_192)=k9_relat_1(C_191, D_192) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.40/1.54  tff(c_1096, plain, (![D_192]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_192)=k9_relat_1('#skF_4', D_192))), inference(resolution, [status(thm)], [c_66, c_1094])).
% 3.40/1.54  tff(c_1098, plain, (![D_192]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_192)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1036, c_1096])).
% 3.40/1.54  tff(c_1099, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1098, c_62])).
% 3.40/1.54  tff(c_1102, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_838, c_1099])).
% 3.40/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/1.54  
% 3.40/1.54  Inference rules
% 3.40/1.54  ----------------------
% 3.40/1.54  #Ref     : 0
% 3.40/1.54  #Sup     : 229
% 3.40/1.54  #Fact    : 0
% 3.40/1.54  #Define  : 0
% 3.40/1.54  #Split   : 5
% 3.40/1.54  #Chain   : 0
% 3.40/1.54  #Close   : 0
% 3.40/1.54  
% 3.40/1.54  Ordering : KBO
% 3.40/1.54  
% 3.40/1.54  Simplification rules
% 3.40/1.54  ----------------------
% 3.40/1.54  #Subsume      : 14
% 3.40/1.54  #Demod        : 214
% 3.40/1.54  #Tautology    : 139
% 3.40/1.54  #SimpNegUnit  : 1
% 3.40/1.54  #BackRed      : 28
% 3.40/1.54  
% 3.40/1.54  #Partial instantiations: 0
% 3.40/1.54  #Strategies tried      : 1
% 3.40/1.54  
% 3.40/1.54  Timing (in seconds)
% 3.40/1.54  ----------------------
% 3.40/1.54  Preprocessing        : 0.34
% 3.40/1.54  Parsing              : 0.18
% 3.40/1.54  CNF conversion       : 0.02
% 3.40/1.54  Main loop            : 0.44
% 3.40/1.54  Inferencing          : 0.16
% 3.40/1.54  Reduction            : 0.16
% 3.40/1.54  Demodulation         : 0.12
% 3.40/1.54  BG Simplification    : 0.02
% 3.40/1.54  Subsumption          : 0.07
% 3.40/1.54  Abstraction          : 0.02
% 3.40/1.54  MUC search           : 0.00
% 3.40/1.54  Cooper               : 0.00
% 3.40/1.54  Total                : 0.81
% 3.40/1.54  Index Insertion      : 0.00
% 3.40/1.54  Index Deletion       : 0.00
% 3.40/1.54  Index Matching       : 0.00
% 3.40/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
