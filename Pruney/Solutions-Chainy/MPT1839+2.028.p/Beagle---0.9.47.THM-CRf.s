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
% DateTime   : Thu Dec  3 10:28:25 EST 2020

% Result     : Theorem 19.00s
% Output     : CNFRefutation 19.00s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 220 expanded)
%              Number of leaves         :   43 (  95 expanded)
%              Depth                    :   16
%              Number of atoms          :  135 ( 465 expanded)
%              Number of equality atoms :   51 ( 121 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_1 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_52,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_126,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_41,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_114,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_104,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_64,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_341,plain,(
    ! [A_92,B_93] :
      ( r1_tarski(A_92,B_93)
      | k4_xboole_0(A_92,B_93) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_82,plain,(
    ~ r1_tarski('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_359,plain,(
    k4_xboole_0('#skF_8','#skF_9') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_341,c_82])).

tff(c_14,plain,(
    ! [A_10] : k3_xboole_0(A_10,A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_142,plain,(
    ! [A_67,B_68] : r1_tarski(k3_xboole_0(A_67,B_68),A_67) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_148,plain,(
    ! [A_10] : r1_tarski(A_10,A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_142])).

tff(c_220,plain,(
    ! [A_83,B_84] :
      ( k4_xboole_0(A_83,B_84) = k1_xboole_0
      | ~ r1_tarski(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_230,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_148,c_220])).

tff(c_386,plain,(
    ! [A_99,B_100] : k5_xboole_0(A_99,k3_xboole_0(A_99,B_100)) = k4_xboole_0(A_99,B_100) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_401,plain,(
    ! [A_10] : k5_xboole_0(A_10,A_10) = k4_xboole_0(A_10,A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_386])).

tff(c_406,plain,(
    ! [A_10] : k5_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_401])).

tff(c_88,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_86,plain,(
    v1_zfmisc_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_80,plain,(
    ! [A_53] :
      ( m1_subset_1('#skF_7'(A_53),A_53)
      | ~ v1_zfmisc_1(A_53)
      | v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_672,plain,(
    ! [A_130,B_131] :
      ( k6_domain_1(A_130,B_131) = k1_tarski(B_131)
      | ~ m1_subset_1(B_131,A_130)
      | v1_xboole_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2905,plain,(
    ! [A_265] :
      ( k6_domain_1(A_265,'#skF_7'(A_265)) = k1_tarski('#skF_7'(A_265))
      | ~ v1_zfmisc_1(A_265)
      | v1_xboole_0(A_265) ) ),
    inference(resolution,[status(thm)],[c_80,c_672])).

tff(c_78,plain,(
    ! [A_53] :
      ( k6_domain_1(A_53,'#skF_7'(A_53)) = A_53
      | ~ v1_zfmisc_1(A_53)
      | v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_24122,plain,(
    ! [A_11505] :
      ( k1_tarski('#skF_7'(A_11505)) = A_11505
      | ~ v1_zfmisc_1(A_11505)
      | v1_xboole_0(A_11505)
      | ~ v1_zfmisc_1(A_11505)
      | v1_xboole_0(A_11505) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2905,c_78])).

tff(c_44,plain,(
    ! [C_31] : r2_hidden(C_31,k1_tarski(C_31)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_136,plain,(
    ! [B_64,A_65] :
      ( ~ r2_hidden(B_64,A_65)
      | ~ v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_140,plain,(
    ! [C_31] : ~ v1_xboole_0(k1_tarski(C_31)) ),
    inference(resolution,[status(thm)],[c_44,c_136])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_173,plain,(
    ! [C_77,A_78] :
      ( C_77 = A_78
      | ~ r2_hidden(C_77,k1_tarski(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_177,plain,(
    ! [A_78] :
      ( '#skF_1'(k1_tarski(A_78)) = A_78
      | v1_xboole_0(k1_tarski(A_78)) ) ),
    inference(resolution,[status(thm)],[c_4,c_173])).

tff(c_183,plain,(
    ! [A_78] : '#skF_1'(k1_tarski(A_78)) = A_78 ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_177])).

tff(c_76654,plain,(
    ! [A_20774] :
      ( '#skF_7'(A_20774) = '#skF_1'(A_20774)
      | ~ v1_zfmisc_1(A_20774)
      | v1_xboole_0(A_20774)
      | ~ v1_zfmisc_1(A_20774)
      | v1_xboole_0(A_20774) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24122,c_183])).

tff(c_76656,plain,
    ( '#skF_7'('#skF_8') = '#skF_1'('#skF_8')
    | ~ v1_zfmisc_1('#skF_8')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_86,c_76654])).

tff(c_76659,plain,
    ( '#skF_7'('#skF_8') = '#skF_1'('#skF_8')
    | v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_76656])).

tff(c_76660,plain,(
    '#skF_7'('#skF_8') = '#skF_1'('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_76659])).

tff(c_2911,plain,(
    ! [A_265] :
      ( k1_tarski('#skF_7'(A_265)) = A_265
      | ~ v1_zfmisc_1(A_265)
      | v1_xboole_0(A_265)
      | ~ v1_zfmisc_1(A_265)
      | v1_xboole_0(A_265) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2905,c_78])).

tff(c_76664,plain,
    ( k1_tarski('#skF_1'('#skF_8')) = '#skF_8'
    | ~ v1_zfmisc_1('#skF_8')
    | v1_xboole_0('#skF_8')
    | ~ v1_zfmisc_1('#skF_8')
    | v1_xboole_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_76660,c_2911])).

tff(c_76677,plain,
    ( k1_tarski('#skF_1'('#skF_8')) = '#skF_8'
    | v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_86,c_76664])).

tff(c_76678,plain,(
    k1_tarski('#skF_1'('#skF_8')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_76677])).

tff(c_30,plain,(
    ! [A_19,B_20] : r1_tarski(k3_xboole_0(A_19,B_20),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_606,plain,(
    ! [B_121,A_122] :
      ( k1_tarski(B_121) = A_122
      | k1_xboole_0 = A_122
      | ~ r1_tarski(A_122,k1_tarski(B_121)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_633,plain,(
    ! [B_121,B_20] :
      ( k3_xboole_0(k1_tarski(B_121),B_20) = k1_tarski(B_121)
      | k3_xboole_0(k1_tarski(B_121),B_20) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_606])).

tff(c_77216,plain,(
    ! [B_20] :
      ( k3_xboole_0('#skF_8',B_20) = k1_tarski('#skF_1'('#skF_8'))
      | k3_xboole_0(k1_tarski('#skF_1'('#skF_8')),B_20) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76678,c_633])).

tff(c_86431,plain,(
    ! [B_23522] :
      ( k3_xboole_0('#skF_8',B_23522) = '#skF_8'
      | k3_xboole_0('#skF_8',B_23522) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76678,c_76678,c_77216])).

tff(c_38,plain,(
    ! [A_24] : k4_xboole_0(A_24,k1_xboole_0) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | k4_xboole_0(A_15,B_16) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_645,plain,(
    ! [C_125,B_126,A_127] :
      ( r2_hidden(C_125,B_126)
      | ~ r2_hidden(C_125,A_127)
      | ~ r1_tarski(A_127,B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_780,plain,(
    ! [A_142,B_143] :
      ( r2_hidden('#skF_1'(A_142),B_143)
      | ~ r1_tarski(A_142,B_143)
      | v1_xboole_0(A_142) ) ),
    inference(resolution,[status(thm)],[c_4,c_645])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_806,plain,(
    ! [B_144,A_145] :
      ( ~ v1_xboole_0(B_144)
      | ~ r1_tarski(A_145,B_144)
      | v1_xboole_0(A_145) ) ),
    inference(resolution,[status(thm)],[c_780,c_2])).

tff(c_901,plain,(
    ! [B_152,A_153] :
      ( ~ v1_xboole_0(B_152)
      | v1_xboole_0(A_153)
      | k4_xboole_0(A_153,B_152) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_806])).

tff(c_905,plain,(
    ! [A_153] :
      ( v1_xboole_0(A_153)
      | k4_xboole_0(A_153,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_901])).

tff(c_920,plain,(
    ! [A_158] :
      ( v1_xboole_0(A_158)
      | k1_xboole_0 != A_158 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_905])).

tff(c_84,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_940,plain,(
    k3_xboole_0('#skF_8','#skF_9') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_920,c_84])).

tff(c_86833,plain,(
    k3_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_86431,c_940])).

tff(c_28,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_87107,plain,(
    k5_xboole_0('#skF_8','#skF_8') = k4_xboole_0('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_86833,c_28])).

tff(c_87169,plain,(
    k4_xboole_0('#skF_8','#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_87107])).

tff(c_87171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_359,c_87169])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:25:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.00/11.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.00/11.17  
% 19.00/11.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.00/11.18  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_1 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_5 > #skF_4
% 19.00/11.18  
% 19.00/11.18  %Foreground sorts:
% 19.00/11.18  
% 19.00/11.18  
% 19.00/11.18  %Background operators:
% 19.00/11.18  
% 19.00/11.18  
% 19.00/11.18  %Foreground operators:
% 19.00/11.18  tff('#skF_7', type, '#skF_7': $i > $i).
% 19.00/11.18  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 19.00/11.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.00/11.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 19.00/11.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 19.00/11.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 19.00/11.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 19.00/11.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 19.00/11.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 19.00/11.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 19.00/11.18  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 19.00/11.18  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 19.00/11.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.00/11.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 19.00/11.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 19.00/11.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 19.00/11.18  tff('#skF_9', type, '#skF_9': $i).
% 19.00/11.18  tff('#skF_8', type, '#skF_8': $i).
% 19.00/11.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.00/11.18  tff(k3_tarski, type, k3_tarski: $i > $i).
% 19.00/11.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.00/11.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 19.00/11.18  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 19.00/11.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 19.00/11.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 19.00/11.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 19.00/11.18  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 19.00/11.18  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 19.00/11.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 19.00/11.18  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 19.00/11.18  
% 19.00/11.19  tff(f_52, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 19.00/11.19  tff(f_126, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 19.00/11.19  tff(f_41, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 19.00/11.19  tff(f_56, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 19.00/11.19  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 19.00/11.19  tff(f_114, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 19.00/11.19  tff(f_104, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 19.00/11.19  tff(f_73, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 19.00/11.19  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 19.00/11.19  tff(f_85, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 19.00/11.19  tff(f_64, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 19.00/11.19  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 19.00/11.19  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 19.00/11.19  tff(c_341, plain, (![A_92, B_93]: (r1_tarski(A_92, B_93) | k4_xboole_0(A_92, B_93)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 19.00/11.19  tff(c_82, plain, (~r1_tarski('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_126])).
% 19.00/11.19  tff(c_359, plain, (k4_xboole_0('#skF_8', '#skF_9')!=k1_xboole_0), inference(resolution, [status(thm)], [c_341, c_82])).
% 19.00/11.19  tff(c_14, plain, (![A_10]: (k3_xboole_0(A_10, A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_41])).
% 19.00/11.19  tff(c_142, plain, (![A_67, B_68]: (r1_tarski(k3_xboole_0(A_67, B_68), A_67))), inference(cnfTransformation, [status(thm)], [f_56])).
% 19.00/11.19  tff(c_148, plain, (![A_10]: (r1_tarski(A_10, A_10))), inference(superposition, [status(thm), theory('equality')], [c_14, c_142])).
% 19.00/11.19  tff(c_220, plain, (![A_83, B_84]: (k4_xboole_0(A_83, B_84)=k1_xboole_0 | ~r1_tarski(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_52])).
% 19.00/11.19  tff(c_230, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_148, c_220])).
% 19.00/11.19  tff(c_386, plain, (![A_99, B_100]: (k5_xboole_0(A_99, k3_xboole_0(A_99, B_100))=k4_xboole_0(A_99, B_100))), inference(cnfTransformation, [status(thm)], [f_54])).
% 19.00/11.19  tff(c_401, plain, (![A_10]: (k5_xboole_0(A_10, A_10)=k4_xboole_0(A_10, A_10))), inference(superposition, [status(thm), theory('equality')], [c_14, c_386])).
% 19.00/11.19  tff(c_406, plain, (![A_10]: (k5_xboole_0(A_10, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_230, c_401])).
% 19.00/11.19  tff(c_88, plain, (~v1_xboole_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_126])).
% 19.00/11.19  tff(c_86, plain, (v1_zfmisc_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_126])).
% 19.00/11.19  tff(c_80, plain, (![A_53]: (m1_subset_1('#skF_7'(A_53), A_53) | ~v1_zfmisc_1(A_53) | v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_114])).
% 19.00/11.19  tff(c_672, plain, (![A_130, B_131]: (k6_domain_1(A_130, B_131)=k1_tarski(B_131) | ~m1_subset_1(B_131, A_130) | v1_xboole_0(A_130))), inference(cnfTransformation, [status(thm)], [f_104])).
% 19.00/11.19  tff(c_2905, plain, (![A_265]: (k6_domain_1(A_265, '#skF_7'(A_265))=k1_tarski('#skF_7'(A_265)) | ~v1_zfmisc_1(A_265) | v1_xboole_0(A_265))), inference(resolution, [status(thm)], [c_80, c_672])).
% 19.00/11.19  tff(c_78, plain, (![A_53]: (k6_domain_1(A_53, '#skF_7'(A_53))=A_53 | ~v1_zfmisc_1(A_53) | v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_114])).
% 19.00/11.19  tff(c_24122, plain, (![A_11505]: (k1_tarski('#skF_7'(A_11505))=A_11505 | ~v1_zfmisc_1(A_11505) | v1_xboole_0(A_11505) | ~v1_zfmisc_1(A_11505) | v1_xboole_0(A_11505))), inference(superposition, [status(thm), theory('equality')], [c_2905, c_78])).
% 19.00/11.19  tff(c_44, plain, (![C_31]: (r2_hidden(C_31, k1_tarski(C_31)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 19.00/11.19  tff(c_136, plain, (![B_64, A_65]: (~r2_hidden(B_64, A_65) | ~v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_31])).
% 19.00/11.19  tff(c_140, plain, (![C_31]: (~v1_xboole_0(k1_tarski(C_31)))), inference(resolution, [status(thm)], [c_44, c_136])).
% 19.00/11.19  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 19.00/11.19  tff(c_173, plain, (![C_77, A_78]: (C_77=A_78 | ~r2_hidden(C_77, k1_tarski(A_78)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 19.00/11.19  tff(c_177, plain, (![A_78]: ('#skF_1'(k1_tarski(A_78))=A_78 | v1_xboole_0(k1_tarski(A_78)))), inference(resolution, [status(thm)], [c_4, c_173])).
% 19.00/11.19  tff(c_183, plain, (![A_78]: ('#skF_1'(k1_tarski(A_78))=A_78)), inference(negUnitSimplification, [status(thm)], [c_140, c_177])).
% 19.00/11.19  tff(c_76654, plain, (![A_20774]: ('#skF_7'(A_20774)='#skF_1'(A_20774) | ~v1_zfmisc_1(A_20774) | v1_xboole_0(A_20774) | ~v1_zfmisc_1(A_20774) | v1_xboole_0(A_20774))), inference(superposition, [status(thm), theory('equality')], [c_24122, c_183])).
% 19.00/11.19  tff(c_76656, plain, ('#skF_7'('#skF_8')='#skF_1'('#skF_8') | ~v1_zfmisc_1('#skF_8') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_86, c_76654])).
% 19.00/11.19  tff(c_76659, plain, ('#skF_7'('#skF_8')='#skF_1'('#skF_8') | v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_76656])).
% 19.00/11.19  tff(c_76660, plain, ('#skF_7'('#skF_8')='#skF_1'('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_88, c_76659])).
% 19.00/11.19  tff(c_2911, plain, (![A_265]: (k1_tarski('#skF_7'(A_265))=A_265 | ~v1_zfmisc_1(A_265) | v1_xboole_0(A_265) | ~v1_zfmisc_1(A_265) | v1_xboole_0(A_265))), inference(superposition, [status(thm), theory('equality')], [c_2905, c_78])).
% 19.00/11.19  tff(c_76664, plain, (k1_tarski('#skF_1'('#skF_8'))='#skF_8' | ~v1_zfmisc_1('#skF_8') | v1_xboole_0('#skF_8') | ~v1_zfmisc_1('#skF_8') | v1_xboole_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_76660, c_2911])).
% 19.00/11.19  tff(c_76677, plain, (k1_tarski('#skF_1'('#skF_8'))='#skF_8' | v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_86, c_76664])).
% 19.00/11.19  tff(c_76678, plain, (k1_tarski('#skF_1'('#skF_8'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_88, c_76677])).
% 19.00/11.19  tff(c_30, plain, (![A_19, B_20]: (r1_tarski(k3_xboole_0(A_19, B_20), A_19))), inference(cnfTransformation, [status(thm)], [f_56])).
% 19.00/11.19  tff(c_606, plain, (![B_121, A_122]: (k1_tarski(B_121)=A_122 | k1_xboole_0=A_122 | ~r1_tarski(A_122, k1_tarski(B_121)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 19.00/11.19  tff(c_633, plain, (![B_121, B_20]: (k3_xboole_0(k1_tarski(B_121), B_20)=k1_tarski(B_121) | k3_xboole_0(k1_tarski(B_121), B_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_606])).
% 19.00/11.19  tff(c_77216, plain, (![B_20]: (k3_xboole_0('#skF_8', B_20)=k1_tarski('#skF_1'('#skF_8')) | k3_xboole_0(k1_tarski('#skF_1'('#skF_8')), B_20)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_76678, c_633])).
% 19.00/11.19  tff(c_86431, plain, (![B_23522]: (k3_xboole_0('#skF_8', B_23522)='#skF_8' | k3_xboole_0('#skF_8', B_23522)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_76678, c_76678, c_77216])).
% 19.00/11.19  tff(c_38, plain, (![A_24]: (k4_xboole_0(A_24, k1_xboole_0)=A_24)), inference(cnfTransformation, [status(thm)], [f_64])).
% 19.00/11.19  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 19.00/11.19  tff(c_24, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | k4_xboole_0(A_15, B_16)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 19.00/11.19  tff(c_645, plain, (![C_125, B_126, A_127]: (r2_hidden(C_125, B_126) | ~r2_hidden(C_125, A_127) | ~r1_tarski(A_127, B_126))), inference(cnfTransformation, [status(thm)], [f_38])).
% 19.00/11.19  tff(c_780, plain, (![A_142, B_143]: (r2_hidden('#skF_1'(A_142), B_143) | ~r1_tarski(A_142, B_143) | v1_xboole_0(A_142))), inference(resolution, [status(thm)], [c_4, c_645])).
% 19.00/11.19  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 19.00/11.19  tff(c_806, plain, (![B_144, A_145]: (~v1_xboole_0(B_144) | ~r1_tarski(A_145, B_144) | v1_xboole_0(A_145))), inference(resolution, [status(thm)], [c_780, c_2])).
% 19.00/11.19  tff(c_901, plain, (![B_152, A_153]: (~v1_xboole_0(B_152) | v1_xboole_0(A_153) | k4_xboole_0(A_153, B_152)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_806])).
% 19.00/11.19  tff(c_905, plain, (![A_153]: (v1_xboole_0(A_153) | k4_xboole_0(A_153, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_901])).
% 19.00/11.19  tff(c_920, plain, (![A_158]: (v1_xboole_0(A_158) | k1_xboole_0!=A_158)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_905])).
% 19.00/11.19  tff(c_84, plain, (~v1_xboole_0(k3_xboole_0('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 19.00/11.19  tff(c_940, plain, (k3_xboole_0('#skF_8', '#skF_9')!=k1_xboole_0), inference(resolution, [status(thm)], [c_920, c_84])).
% 19.00/11.19  tff(c_86833, plain, (k3_xboole_0('#skF_8', '#skF_9')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_86431, c_940])).
% 19.00/11.19  tff(c_28, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_54])).
% 19.00/11.19  tff(c_87107, plain, (k5_xboole_0('#skF_8', '#skF_8')=k4_xboole_0('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_86833, c_28])).
% 19.00/11.19  tff(c_87169, plain, (k4_xboole_0('#skF_8', '#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_406, c_87107])).
% 19.00/11.19  tff(c_87171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_359, c_87169])).
% 19.00/11.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.00/11.19  
% 19.00/11.19  Inference rules
% 19.00/11.19  ----------------------
% 19.00/11.19  #Ref     : 9
% 19.00/11.19  #Sup     : 20456
% 19.00/11.19  #Fact    : 2
% 19.00/11.19  #Define  : 0
% 19.00/11.19  #Split   : 1
% 19.00/11.19  #Chain   : 0
% 19.00/11.19  #Close   : 0
% 19.00/11.19  
% 19.00/11.19  Ordering : KBO
% 19.00/11.19  
% 19.00/11.19  Simplification rules
% 19.00/11.19  ----------------------
% 19.00/11.19  #Subsume      : 13337
% 19.00/11.19  #Demod        : 7137
% 19.00/11.19  #Tautology    : 3461
% 19.00/11.19  #SimpNegUnit  : 1083
% 19.00/11.19  #BackRed      : 22
% 19.00/11.19  
% 19.00/11.19  #Partial instantiations: 12562
% 19.00/11.19  #Strategies tried      : 1
% 19.00/11.19  
% 19.00/11.19  Timing (in seconds)
% 19.00/11.19  ----------------------
% 19.00/11.19  Preprocessing        : 0.34
% 19.00/11.19  Parsing              : 0.17
% 19.00/11.19  CNF conversion       : 0.03
% 19.00/11.19  Main loop            : 10.04
% 19.00/11.19  Inferencing          : 1.86
% 19.00/11.19  Reduction            : 4.25
% 19.00/11.19  Demodulation         : 3.24
% 19.00/11.19  BG Simplification    : 0.12
% 19.00/11.19  Subsumption          : 3.45
% 19.00/11.19  Abstraction          : 0.27
% 19.00/11.20  MUC search           : 0.00
% 19.00/11.20  Cooper               : 0.00
% 19.00/11.20  Total                : 10.42
% 19.00/11.20  Index Insertion      : 0.00
% 19.00/11.20  Index Deletion       : 0.00
% 19.00/11.20  Index Matching       : 0.00
% 19.00/11.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
