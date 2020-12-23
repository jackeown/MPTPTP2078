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
% DateTime   : Thu Dec  3 10:08:15 EST 2020

% Result     : Theorem 5.02s
% Output     : CNFRefutation 5.35s
% Verified   : 
% Statistics : Number of formulae       :  201 (1606 expanded)
%              Number of leaves         :   41 ( 533 expanded)
%              Depth                    :   18
%              Number of atoms          :  331 (3676 expanded)
%              Number of equality atoms :   77 ( 815 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff(f_89,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_144,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_103,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_123,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_109,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_32,plain,(
    ! [A_25,B_26] : v1_relat_1(k2_zfmisc_1(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_114,plain,(
    ! [B_72,A_73] :
      ( v1_relat_1(B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_73))
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_120,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_56,c_114])).

tff(c_124,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_120])).

tff(c_36,plain,(
    ! [A_29] :
      ( k2_relat_1(A_29) != k1_xboole_0
      | k1_xboole_0 = A_29
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_132,plain,
    ( k2_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_124,c_36])).

tff(c_2225,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_147,plain,(
    ! [C_76,B_77,A_78] :
      ( v5_relat_1(C_76,B_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_78,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_156,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_147])).

tff(c_30,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k2_relat_1(B_24),A_23)
      | ~ v5_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_135,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_14,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_319,plain,(
    ! [A_126,C_127,B_128] :
      ( m1_subset_1(A_126,C_127)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(C_127))
      | ~ r2_hidden(A_126,B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_373,plain,(
    ! [A_134,B_135,A_136] :
      ( m1_subset_1(A_134,B_135)
      | ~ r2_hidden(A_134,A_136)
      | ~ r1_tarski(A_136,B_135) ) ),
    inference(resolution,[status(thm)],[c_18,c_319])).

tff(c_389,plain,(
    ! [A_137,B_138] :
      ( m1_subset_1('#skF_3'(A_137),B_138)
      | ~ r1_tarski(A_137,B_138)
      | k1_xboole_0 = A_137 ) ),
    inference(resolution,[status(thm)],[c_14,c_373])).

tff(c_326,plain,(
    ! [A_129,B_130,C_131] :
      ( k2_relset_1(A_129,B_130,C_131) = k2_relat_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_335,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_326])).

tff(c_78,plain,(
    ! [D_60] :
      ( ~ r2_hidden(D_60,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1(D_60,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_83,plain,
    ( ~ m1_subset_1('#skF_3'(k2_relset_1('#skF_4','#skF_5','#skF_6')),'#skF_5')
    | k2_relset_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_78])).

tff(c_133,plain,(
    ~ m1_subset_1('#skF_3'(k2_relset_1('#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_339,plain,(
    ~ m1_subset_1('#skF_3'(k2_relat_1('#skF_6')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_133])).

tff(c_392,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
    | k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_389,c_339])).

tff(c_418,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_392])).

tff(c_427,plain,
    ( ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_418])).

tff(c_431,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_156,c_427])).

tff(c_432,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_38,plain,(
    ! [A_29] :
      ( k1_relat_1(A_29) != k1_xboole_0
      | k1_xboole_0 = A_29
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_131,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_124,c_38])).

tff(c_134,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_434,plain,(
    k1_relat_1('#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_134])).

tff(c_448,plain,(
    ! [C_139,B_140,A_141] :
      ( v5_relat_1(C_139,B_140)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_141,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_457,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_448])).

tff(c_433,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_443,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_433])).

tff(c_610,plain,(
    ! [B_180,A_181] :
      ( r1_tarski(k2_relat_1(B_180),A_181)
      | ~ v5_relat_1(B_180,A_181)
      | ~ v1_relat_1(B_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_627,plain,(
    ! [A_181] :
      ( r1_tarski('#skF_6',A_181)
      | ~ v5_relat_1('#skF_6',A_181)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_443,c_610])).

tff(c_634,plain,(
    ! [A_182] :
      ( r1_tarski('#skF_6',A_182)
      | ~ v5_relat_1('#skF_6',A_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_627])).

tff(c_654,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_457,c_634])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_704,plain,(
    ! [A_196,C_197,B_198] :
      ( m1_subset_1(A_196,C_197)
      | ~ m1_subset_1(B_198,k1_zfmisc_1(C_197))
      | ~ r2_hidden(A_196,B_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_728,plain,(
    ! [A_201,B_202,A_203] :
      ( m1_subset_1(A_201,B_202)
      | ~ r2_hidden(A_201,A_203)
      | ~ r1_tarski(A_203,B_202) ) ),
    inference(resolution,[status(thm)],[c_18,c_704])).

tff(c_1123,plain,(
    ! [A_261,B_262,B_263] :
      ( m1_subset_1('#skF_1'(A_261,B_262),B_263)
      | ~ r1_tarski(A_261,B_263)
      | r1_tarski(A_261,B_262) ) ),
    inference(resolution,[status(thm)],[c_6,c_728])).

tff(c_820,plain,(
    ! [A_212,B_213,C_214] :
      ( k2_relset_1(A_212,B_213,C_214) = k2_relat_1(C_214)
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(A_212,B_213))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_831,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_820])).

tff(c_835,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_831])).

tff(c_101,plain,(
    ! [A_67,B_68] :
      ( r2_hidden('#skF_1'(A_67,B_68),A_67)
      | r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    ! [D_52] :
      ( ~ r2_hidden(D_52,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1(D_52,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_106,plain,(
    ! [B_68] :
      ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_68),'#skF_5')
      | r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_68) ) ),
    inference(resolution,[status(thm)],[c_101,c_52])).

tff(c_840,plain,(
    ! [B_68] :
      ( ~ m1_subset_1('#skF_1'('#skF_6',B_68),'#skF_5')
      | r1_tarski('#skF_6',B_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_835,c_835,c_106])).

tff(c_1131,plain,(
    ! [B_262] :
      ( ~ r1_tarski('#skF_6','#skF_5')
      | r1_tarski('#skF_6',B_262) ) ),
    inference(resolution,[status(thm)],[c_1123,c_840])).

tff(c_1177,plain,(
    ! [B_266] : r1_tarski('#skF_6',B_266) ),
    inference(demodulation,[status(thm),theory(equality)],[c_654,c_1131])).

tff(c_529,plain,(
    ! [C_159,A_160,B_161] :
      ( v4_relat_1(C_159,A_160)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_537,plain,(
    ! [A_13,A_160,B_161] :
      ( v4_relat_1(A_13,A_160)
      | ~ r1_tarski(A_13,k2_zfmisc_1(A_160,B_161)) ) ),
    inference(resolution,[status(thm)],[c_18,c_529])).

tff(c_1234,plain,(
    ! [A_268] : v4_relat_1('#skF_6',A_268) ),
    inference(resolution,[status(thm)],[c_1177,c_537])).

tff(c_660,plain,(
    ! [B_183,A_184] :
      ( r1_tarski(k1_relat_1(B_183),A_184)
      | ~ v4_relat_1(B_183,A_184)
      | ~ v1_relat_1(B_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_121,plain,(
    ! [A_13,B_14] :
      ( v1_relat_1(A_13)
      | ~ v1_relat_1(B_14)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(resolution,[status(thm)],[c_18,c_114])).

tff(c_678,plain,(
    ! [B_183,A_184] :
      ( v1_relat_1(k1_relat_1(B_183))
      | ~ v1_relat_1(A_184)
      | ~ v4_relat_1(B_183,A_184)
      | ~ v1_relat_1(B_183) ) ),
    inference(resolution,[status(thm)],[c_660,c_121])).

tff(c_1236,plain,(
    ! [A_268] :
      ( v1_relat_1(k1_relat_1('#skF_6'))
      | ~ v1_relat_1(A_268)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1234,c_678])).

tff(c_1242,plain,(
    ! [A_268] :
      ( v1_relat_1(k1_relat_1('#skF_6'))
      | ~ v1_relat_1(A_268) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_1236])).

tff(c_1346,plain,(
    ! [A_268] : ~ v1_relat_1(A_268) ),
    inference(splitLeft,[status(thm)],[c_1242])).

tff(c_1355,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1346,c_124])).

tff(c_1356,plain,(
    v1_relat_1(k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1242])).

tff(c_1208,plain,(
    ! [A_160] : v4_relat_1('#skF_6',A_160) ),
    inference(resolution,[status(thm)],[c_1177,c_537])).

tff(c_1369,plain,(
    ! [B_278,A_279,B_280] :
      ( v4_relat_1(k1_relat_1(B_278),A_279)
      | ~ v4_relat_1(B_278,k2_zfmisc_1(A_279,B_280))
      | ~ v1_relat_1(B_278) ) ),
    inference(resolution,[status(thm)],[c_660,c_537])).

tff(c_1372,plain,(
    ! [A_279] :
      ( v4_relat_1(k1_relat_1('#skF_6'),A_279)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1208,c_1369])).

tff(c_1386,plain,(
    ! [A_281] : v4_relat_1(k1_relat_1('#skF_6'),A_281) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_1372])).

tff(c_34,plain,(
    ! [B_28,A_27] :
      ( k7_relat_1(B_28,A_27) = B_28
      | ~ v4_relat_1(B_28,A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1394,plain,(
    ! [A_281] :
      ( k7_relat_1(k1_relat_1('#skF_6'),A_281) = k1_relat_1('#skF_6')
      | ~ v1_relat_1(k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_1386,c_34])).

tff(c_1804,plain,(
    ! [A_307] : k7_relat_1(k1_relat_1('#skF_6'),A_307) = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1356,c_1394])).

tff(c_1158,plain,(
    ! [B_262] : r1_tarski('#skF_6',B_262) ),
    inference(demodulation,[status(thm),theory(equality)],[c_654,c_1131])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1248,plain,(
    ! [A_269,B_270,B_271] :
      ( m1_subset_1('#skF_2'(A_269,B_270),B_271)
      | ~ r1_tarski(B_270,B_271)
      | r1_xboole_0(A_269,B_270) ) ),
    inference(resolution,[status(thm)],[c_10,c_728])).

tff(c_89,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_2'(A_63,B_64),B_64)
      | r1_xboole_0(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_94,plain,(
    ! [A_63] :
      ( ~ m1_subset_1('#skF_2'(A_63,k2_relset_1('#skF_4','#skF_5','#skF_6')),'#skF_5')
      | r1_xboole_0(A_63,k2_relset_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_89,c_52])).

tff(c_838,plain,(
    ! [A_63] :
      ( ~ m1_subset_1('#skF_2'(A_63,'#skF_6'),'#skF_5')
      | r1_xboole_0(A_63,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_835,c_835,c_94])).

tff(c_1264,plain,(
    ! [A_269] :
      ( ~ r1_tarski('#skF_6','#skF_5')
      | r1_xboole_0(A_269,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1248,c_838])).

tff(c_1301,plain,(
    ! [A_272] : r1_xboole_0(A_272,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1158,c_1264])).

tff(c_40,plain,(
    ! [B_31,A_30] :
      ( k7_relat_1(B_31,A_30) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_31),A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_693,plain,(
    ! [B_31,A_30] :
      ( k7_relat_1(B_31,A_30) = '#skF_6'
      | ~ r1_xboole_0(k1_relat_1(B_31),A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_40])).

tff(c_1426,plain,(
    ! [B_285] :
      ( k7_relat_1(B_285,'#skF_6') = '#skF_6'
      | ~ v1_relat_1(B_285) ) ),
    inference(resolution,[status(thm)],[c_1301,c_693])).

tff(c_1442,plain,(
    k7_relat_1(k1_relat_1('#skF_6'),'#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1356,c_1426])).

tff(c_1808,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_1804,c_1442])).

tff(c_1823,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_434,c_1808])).

tff(c_1824,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_54,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_1829,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1824,c_54])).

tff(c_1825,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_1834,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1824,c_1825])).

tff(c_2182,plain,(
    ! [A_373,B_374,C_375] :
      ( k1_relset_1(A_373,B_374,C_375) = k1_relat_1(C_375)
      | ~ m1_subset_1(C_375,k1_zfmisc_1(k2_zfmisc_1(A_373,B_374))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2189,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_2182])).

tff(c_2192,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1834,c_2189])).

tff(c_2194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1829,c_2192])).

tff(c_2195,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_2635,plain,(
    ! [A_462,B_463,C_464] :
      ( k2_relset_1(A_462,B_463,C_464) = k2_relat_1(C_464)
      | ~ m1_subset_1(C_464,k1_zfmisc_1(k2_zfmisc_1(A_462,B_463))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2646,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_2635])).

tff(c_2650,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2195,c_2646])).

tff(c_2652,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2225,c_2650])).

tff(c_2653,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_2202,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_2656,plain,(
    k1_relat_1('#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2653,c_2202])).

tff(c_2771,plain,(
    ! [C_484,B_485,A_486] :
      ( v5_relat_1(C_484,B_485)
      | ~ m1_subset_1(C_484,k1_zfmisc_1(k2_zfmisc_1(A_486,B_485))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2780,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_2771])).

tff(c_2654,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_2666,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2653,c_2654])).

tff(c_2871,plain,(
    ! [B_505,A_506] :
      ( r1_tarski(k2_relat_1(B_505),A_506)
      | ~ v5_relat_1(B_505,A_506)
      | ~ v1_relat_1(B_505) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2888,plain,(
    ! [A_506] :
      ( r1_tarski('#skF_6',A_506)
      | ~ v5_relat_1('#skF_6',A_506)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2666,c_2871])).

tff(c_2895,plain,(
    ! [A_507] :
      ( r1_tarski('#skF_6',A_507)
      | ~ v5_relat_1('#skF_6',A_507) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_2888])).

tff(c_2915,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_2780,c_2895])).

tff(c_2954,plain,(
    ! [A_522,C_523,B_524] :
      ( m1_subset_1(A_522,C_523)
      | ~ m1_subset_1(B_524,k1_zfmisc_1(C_523))
      | ~ r2_hidden(A_522,B_524) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2971,plain,(
    ! [A_528,B_529,A_530] :
      ( m1_subset_1(A_528,B_529)
      | ~ r2_hidden(A_528,A_530)
      | ~ r1_tarski(A_530,B_529) ) ),
    inference(resolution,[status(thm)],[c_18,c_2954])).

tff(c_3266,plain,(
    ! [A_571,B_572,B_573] :
      ( m1_subset_1('#skF_2'(A_571,B_572),B_573)
      | ~ r1_tarski(B_572,B_573)
      | r1_xboole_0(A_571,B_572) ) ),
    inference(resolution,[status(thm)],[c_10,c_2971])).

tff(c_2203,plain,(
    ! [D_376] :
      ( ~ r2_hidden(D_376,k1_xboole_0)
      | ~ m1_subset_1(D_376,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2195,c_52])).

tff(c_2222,plain,(
    ! [A_6] :
      ( ~ m1_subset_1('#skF_2'(A_6,k1_xboole_0),'#skF_5')
      | r1_xboole_0(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_2203])).

tff(c_2758,plain,(
    ! [A_6] :
      ( ~ m1_subset_1('#skF_2'(A_6,'#skF_6'),'#skF_5')
      | r1_xboole_0(A_6,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2653,c_2653,c_2222])).

tff(c_3289,plain,(
    ! [A_571] :
      ( ~ r1_tarski('#skF_6','#skF_5')
      | r1_xboole_0(A_571,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_3266,c_2758])).

tff(c_3319,plain,(
    ! [A_574] : r1_xboole_0(A_574,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2915,c_3289])).

tff(c_2944,plain,(
    ! [B_31,A_30] :
      ( k7_relat_1(B_31,A_30) = '#skF_6'
      | ~ r1_xboole_0(k1_relat_1(B_31),A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2653,c_40])).

tff(c_3380,plain,(
    ! [B_581] :
      ( k7_relat_1(B_581,'#skF_6') = '#skF_6'
      | ~ v1_relat_1(B_581) ) ),
    inference(resolution,[status(thm)],[c_3319,c_2944])).

tff(c_3401,plain,(
    ! [A_582,B_583] : k7_relat_1(k2_zfmisc_1(A_582,B_583),'#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_32,c_3380])).

tff(c_107,plain,(
    ! [A_69,B_70] :
      ( ~ r2_hidden('#skF_1'(A_69,B_70),B_70)
      | r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_112,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_107])).

tff(c_2710,plain,(
    ! [C_469,A_470,B_471] :
      ( v4_relat_1(C_469,A_470)
      | ~ m1_subset_1(C_469,k1_zfmisc_1(k2_zfmisc_1(A_470,B_471))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2743,plain,(
    ! [A_475,A_476,B_477] :
      ( v4_relat_1(A_475,A_476)
      | ~ r1_tarski(A_475,k2_zfmisc_1(A_476,B_477)) ) ),
    inference(resolution,[status(thm)],[c_18,c_2710])).

tff(c_2751,plain,(
    ! [A_476,B_477] : v4_relat_1(k2_zfmisc_1(A_476,B_477),A_476) ),
    inference(resolution,[status(thm)],[c_112,c_2743])).

tff(c_2841,plain,(
    ! [B_502,A_503] :
      ( k7_relat_1(B_502,A_503) = B_502
      | ~ v4_relat_1(B_502,A_503)
      | ~ v1_relat_1(B_502) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2847,plain,(
    ! [A_476,B_477] :
      ( k7_relat_1(k2_zfmisc_1(A_476,B_477),A_476) = k2_zfmisc_1(A_476,B_477)
      | ~ v1_relat_1(k2_zfmisc_1(A_476,B_477)) ) ),
    inference(resolution,[status(thm)],[c_2751,c_2841])).

tff(c_2854,plain,(
    ! [A_476,B_477] : k7_relat_1(k2_zfmisc_1(A_476,B_477),A_476) = k2_zfmisc_1(A_476,B_477) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2847])).

tff(c_3416,plain,(
    ! [B_584] : k2_zfmisc_1('#skF_6',B_584) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_3401,c_2854])).

tff(c_2760,plain,(
    ! [B_482,A_483] :
      ( r1_tarski(k1_relat_1(B_482),A_483)
      | ~ v4_relat_1(B_482,A_483)
      | ~ v1_relat_1(B_482) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3061,plain,(
    ! [B_537,A_538] :
      ( v1_relat_1(k1_relat_1(B_537))
      | ~ v1_relat_1(A_538)
      | ~ v4_relat_1(B_537,A_538)
      | ~ v1_relat_1(B_537) ) ),
    inference(resolution,[status(thm)],[c_2760,c_121])).

tff(c_3065,plain,(
    ! [A_476,B_477] :
      ( v1_relat_1(k1_relat_1(k2_zfmisc_1(A_476,B_477)))
      | ~ v1_relat_1(A_476)
      | ~ v1_relat_1(k2_zfmisc_1(A_476,B_477)) ) ),
    inference(resolution,[status(thm)],[c_2751,c_3061])).

tff(c_3071,plain,(
    ! [A_476,B_477] :
      ( v1_relat_1(k1_relat_1(k2_zfmisc_1(A_476,B_477)))
      | ~ v1_relat_1(A_476) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3065])).

tff(c_3443,plain,
    ( v1_relat_1(k1_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3416,c_3071])).

tff(c_3484,plain,(
    v1_relat_1(k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_3443])).

tff(c_3535,plain,(
    ! [A_586,B_587,B_588] :
      ( m1_subset_1('#skF_1'(A_586,B_587),B_588)
      | ~ r1_tarski(A_586,B_588)
      | r1_tarski(A_586,B_587) ) ),
    inference(resolution,[status(thm)],[c_6,c_2971])).

tff(c_2220,plain,(
    ! [B_2] :
      ( ~ m1_subset_1('#skF_1'(k1_xboole_0,B_2),'#skF_5')
      | r1_tarski(k1_xboole_0,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_2203])).

tff(c_2755,plain,(
    ! [B_2] :
      ( ~ m1_subset_1('#skF_1'('#skF_6',B_2),'#skF_5')
      | r1_tarski('#skF_6',B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2653,c_2653,c_2220])).

tff(c_3554,plain,(
    ! [B_587] :
      ( ~ r1_tarski('#skF_6','#skF_5')
      | r1_tarski('#skF_6',B_587) ) ),
    inference(resolution,[status(thm)],[c_3535,c_2755])).

tff(c_3580,plain,(
    ! [B_589] : r1_tarski('#skF_6',B_589) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2915,c_3554])).

tff(c_2718,plain,(
    ! [A_13,A_470,B_471] :
      ( v4_relat_1(A_13,A_470)
      | ~ r1_tarski(A_13,k2_zfmisc_1(A_470,B_471)) ) ),
    inference(resolution,[status(thm)],[c_18,c_2710])).

tff(c_3613,plain,(
    ! [A_470] : v4_relat_1('#skF_6',A_470) ),
    inference(resolution,[status(thm)],[c_3580,c_2718])).

tff(c_3862,plain,(
    ! [B_616,A_617,B_618] :
      ( v4_relat_1(k1_relat_1(B_616),A_617)
      | ~ v4_relat_1(B_616,k2_zfmisc_1(A_617,B_618))
      | ~ v1_relat_1(B_616) ) ),
    inference(resolution,[status(thm)],[c_2760,c_2718])).

tff(c_3865,plain,(
    ! [A_617] :
      ( v4_relat_1(k1_relat_1('#skF_6'),A_617)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_3613,c_3862])).

tff(c_3877,plain,(
    ! [A_619] : v4_relat_1(k1_relat_1('#skF_6'),A_619) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_3865])).

tff(c_3888,plain,(
    ! [A_619] :
      ( k7_relat_1(k1_relat_1('#skF_6'),A_619) = k1_relat_1('#skF_6')
      | ~ v1_relat_1(k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_3877,c_34])).

tff(c_4031,plain,(
    ! [A_628] : k7_relat_1(k1_relat_1('#skF_6'),A_628) = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3484,c_3888])).

tff(c_3326,plain,(
    ! [B_31] :
      ( k7_relat_1(B_31,'#skF_6') = '#skF_6'
      | ~ v1_relat_1(B_31) ) ),
    inference(resolution,[status(thm)],[c_3319,c_2944])).

tff(c_3500,plain,(
    k7_relat_1(k1_relat_1('#skF_6'),'#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3484,c_3326])).

tff(c_4035,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_4031,c_3500])).

tff(c_4050,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2656,c_4035])).

tff(c_4051,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_4057,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4051,c_54])).

tff(c_4052,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_4062,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4051,c_4052])).

tff(c_4544,plain,(
    ! [A_708,B_709,C_710] :
      ( k1_relset_1(A_708,B_709,C_710) = k1_relat_1(C_710)
      | ~ m1_subset_1(C_710,k1_zfmisc_1(k2_zfmisc_1(A_708,B_709))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_4555,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_4544])).

tff(c_4559,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4062,c_4555])).

tff(c_4561,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4057,c_4559])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:45:34 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.02/1.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.35/1.99  
% 5.35/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.35/1.99  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 5.35/1.99  
% 5.35/1.99  %Foreground sorts:
% 5.35/1.99  
% 5.35/1.99  
% 5.35/1.99  %Background operators:
% 5.35/1.99  
% 5.35/1.99  
% 5.35/1.99  %Foreground operators:
% 5.35/1.99  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.35/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.35/1.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.35/1.99  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.35/1.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.35/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.35/1.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.35/1.99  tff('#skF_5', type, '#skF_5': $i).
% 5.35/1.99  tff('#skF_6', type, '#skF_6': $i).
% 5.35/1.99  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.35/1.99  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.35/1.99  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.35/1.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.35/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.35/1.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.35/1.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.35/1.99  tff('#skF_4', type, '#skF_4': $i).
% 5.35/1.99  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.35/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.35/1.99  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.35/1.99  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.35/1.99  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.35/1.99  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.35/1.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.35/1.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.35/1.99  
% 5.35/2.02  tff(f_89, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.35/2.02  tff(f_144, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 5.35/2.02  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.35/2.02  tff(f_103, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 5.35/2.02  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.35/2.02  tff(f_87, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 5.35/2.02  tff(f_58, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.35/2.02  tff(f_62, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.35/2.02  tff(f_68, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 5.35/2.02  tff(f_123, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.35/2.02  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.35/2.02  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 5.35/2.02  tff(f_95, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 5.35/2.02  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.35/2.02  tff(f_109, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 5.35/2.02  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.35/2.02  tff(c_32, plain, (![A_25, B_26]: (v1_relat_1(k2_zfmisc_1(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.35/2.02  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.35/2.02  tff(c_114, plain, (![B_72, A_73]: (v1_relat_1(B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(A_73)) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.35/2.02  tff(c_120, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_56, c_114])).
% 5.35/2.02  tff(c_124, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_120])).
% 5.35/2.02  tff(c_36, plain, (![A_29]: (k2_relat_1(A_29)!=k1_xboole_0 | k1_xboole_0=A_29 | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.35/2.02  tff(c_132, plain, (k2_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_124, c_36])).
% 5.35/2.02  tff(c_2225, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_132])).
% 5.35/2.02  tff(c_147, plain, (![C_76, B_77, A_78]: (v5_relat_1(C_76, B_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_78, B_77))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.35/2.02  tff(c_156, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_147])).
% 5.35/2.02  tff(c_30, plain, (![B_24, A_23]: (r1_tarski(k2_relat_1(B_24), A_23) | ~v5_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.35/2.02  tff(c_135, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_132])).
% 5.35/2.02  tff(c_14, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.35/2.02  tff(c_18, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.35/2.02  tff(c_319, plain, (![A_126, C_127, B_128]: (m1_subset_1(A_126, C_127) | ~m1_subset_1(B_128, k1_zfmisc_1(C_127)) | ~r2_hidden(A_126, B_128))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.35/2.02  tff(c_373, plain, (![A_134, B_135, A_136]: (m1_subset_1(A_134, B_135) | ~r2_hidden(A_134, A_136) | ~r1_tarski(A_136, B_135))), inference(resolution, [status(thm)], [c_18, c_319])).
% 5.35/2.02  tff(c_389, plain, (![A_137, B_138]: (m1_subset_1('#skF_3'(A_137), B_138) | ~r1_tarski(A_137, B_138) | k1_xboole_0=A_137)), inference(resolution, [status(thm)], [c_14, c_373])).
% 5.35/2.02  tff(c_326, plain, (![A_129, B_130, C_131]: (k2_relset_1(A_129, B_130, C_131)=k2_relat_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.35/2.02  tff(c_335, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_326])).
% 5.35/2.02  tff(c_78, plain, (![D_60]: (~r2_hidden(D_60, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1(D_60, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.35/2.02  tff(c_83, plain, (~m1_subset_1('#skF_3'(k2_relset_1('#skF_4', '#skF_5', '#skF_6')), '#skF_5') | k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_78])).
% 5.35/2.02  tff(c_133, plain, (~m1_subset_1('#skF_3'(k2_relset_1('#skF_4', '#skF_5', '#skF_6')), '#skF_5')), inference(splitLeft, [status(thm)], [c_83])).
% 5.35/2.02  tff(c_339, plain, (~m1_subset_1('#skF_3'(k2_relat_1('#skF_6')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_335, c_133])).
% 5.35/2.02  tff(c_392, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | k2_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_389, c_339])).
% 5.35/2.02  tff(c_418, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_135, c_392])).
% 5.35/2.02  tff(c_427, plain, (~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_30, c_418])).
% 5.35/2.02  tff(c_431, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_156, c_427])).
% 5.35/2.02  tff(c_432, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_132])).
% 5.35/2.02  tff(c_38, plain, (![A_29]: (k1_relat_1(A_29)!=k1_xboole_0 | k1_xboole_0=A_29 | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.35/2.02  tff(c_131, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_124, c_38])).
% 5.35/2.02  tff(c_134, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_131])).
% 5.35/2.02  tff(c_434, plain, (k1_relat_1('#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_432, c_134])).
% 5.35/2.02  tff(c_448, plain, (![C_139, B_140, A_141]: (v5_relat_1(C_139, B_140) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_141, B_140))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.35/2.02  tff(c_457, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_448])).
% 5.35/2.02  tff(c_433, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_132])).
% 5.35/2.02  tff(c_443, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_432, c_433])).
% 5.35/2.02  tff(c_610, plain, (![B_180, A_181]: (r1_tarski(k2_relat_1(B_180), A_181) | ~v5_relat_1(B_180, A_181) | ~v1_relat_1(B_180))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.35/2.02  tff(c_627, plain, (![A_181]: (r1_tarski('#skF_6', A_181) | ~v5_relat_1('#skF_6', A_181) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_443, c_610])).
% 5.35/2.02  tff(c_634, plain, (![A_182]: (r1_tarski('#skF_6', A_182) | ~v5_relat_1('#skF_6', A_182))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_627])).
% 5.35/2.02  tff(c_654, plain, (r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_457, c_634])).
% 5.35/2.02  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.35/2.02  tff(c_704, plain, (![A_196, C_197, B_198]: (m1_subset_1(A_196, C_197) | ~m1_subset_1(B_198, k1_zfmisc_1(C_197)) | ~r2_hidden(A_196, B_198))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.35/2.02  tff(c_728, plain, (![A_201, B_202, A_203]: (m1_subset_1(A_201, B_202) | ~r2_hidden(A_201, A_203) | ~r1_tarski(A_203, B_202))), inference(resolution, [status(thm)], [c_18, c_704])).
% 5.35/2.02  tff(c_1123, plain, (![A_261, B_262, B_263]: (m1_subset_1('#skF_1'(A_261, B_262), B_263) | ~r1_tarski(A_261, B_263) | r1_tarski(A_261, B_262))), inference(resolution, [status(thm)], [c_6, c_728])).
% 5.35/2.02  tff(c_820, plain, (![A_212, B_213, C_214]: (k2_relset_1(A_212, B_213, C_214)=k2_relat_1(C_214) | ~m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(A_212, B_213))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.35/2.02  tff(c_831, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_820])).
% 5.35/2.02  tff(c_835, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_443, c_831])).
% 5.35/2.02  tff(c_101, plain, (![A_67, B_68]: (r2_hidden('#skF_1'(A_67, B_68), A_67) | r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.35/2.02  tff(c_52, plain, (![D_52]: (~r2_hidden(D_52, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1(D_52, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.35/2.02  tff(c_106, plain, (![B_68]: (~m1_subset_1('#skF_1'(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_68), '#skF_5') | r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_68))), inference(resolution, [status(thm)], [c_101, c_52])).
% 5.35/2.02  tff(c_840, plain, (![B_68]: (~m1_subset_1('#skF_1'('#skF_6', B_68), '#skF_5') | r1_tarski('#skF_6', B_68))), inference(demodulation, [status(thm), theory('equality')], [c_835, c_835, c_106])).
% 5.35/2.02  tff(c_1131, plain, (![B_262]: (~r1_tarski('#skF_6', '#skF_5') | r1_tarski('#skF_6', B_262))), inference(resolution, [status(thm)], [c_1123, c_840])).
% 5.35/2.02  tff(c_1177, plain, (![B_266]: (r1_tarski('#skF_6', B_266))), inference(demodulation, [status(thm), theory('equality')], [c_654, c_1131])).
% 5.35/2.02  tff(c_529, plain, (![C_159, A_160, B_161]: (v4_relat_1(C_159, A_160) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.35/2.02  tff(c_537, plain, (![A_13, A_160, B_161]: (v4_relat_1(A_13, A_160) | ~r1_tarski(A_13, k2_zfmisc_1(A_160, B_161)))), inference(resolution, [status(thm)], [c_18, c_529])).
% 5.35/2.02  tff(c_1234, plain, (![A_268]: (v4_relat_1('#skF_6', A_268))), inference(resolution, [status(thm)], [c_1177, c_537])).
% 5.35/2.02  tff(c_660, plain, (![B_183, A_184]: (r1_tarski(k1_relat_1(B_183), A_184) | ~v4_relat_1(B_183, A_184) | ~v1_relat_1(B_183))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.35/2.02  tff(c_121, plain, (![A_13, B_14]: (v1_relat_1(A_13) | ~v1_relat_1(B_14) | ~r1_tarski(A_13, B_14))), inference(resolution, [status(thm)], [c_18, c_114])).
% 5.35/2.02  tff(c_678, plain, (![B_183, A_184]: (v1_relat_1(k1_relat_1(B_183)) | ~v1_relat_1(A_184) | ~v4_relat_1(B_183, A_184) | ~v1_relat_1(B_183))), inference(resolution, [status(thm)], [c_660, c_121])).
% 5.35/2.02  tff(c_1236, plain, (![A_268]: (v1_relat_1(k1_relat_1('#skF_6')) | ~v1_relat_1(A_268) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_1234, c_678])).
% 5.35/2.02  tff(c_1242, plain, (![A_268]: (v1_relat_1(k1_relat_1('#skF_6')) | ~v1_relat_1(A_268))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_1236])).
% 5.35/2.02  tff(c_1346, plain, (![A_268]: (~v1_relat_1(A_268))), inference(splitLeft, [status(thm)], [c_1242])).
% 5.35/2.02  tff(c_1355, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1346, c_124])).
% 5.35/2.02  tff(c_1356, plain, (v1_relat_1(k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_1242])).
% 5.35/2.02  tff(c_1208, plain, (![A_160]: (v4_relat_1('#skF_6', A_160))), inference(resolution, [status(thm)], [c_1177, c_537])).
% 5.35/2.02  tff(c_1369, plain, (![B_278, A_279, B_280]: (v4_relat_1(k1_relat_1(B_278), A_279) | ~v4_relat_1(B_278, k2_zfmisc_1(A_279, B_280)) | ~v1_relat_1(B_278))), inference(resolution, [status(thm)], [c_660, c_537])).
% 5.35/2.02  tff(c_1372, plain, (![A_279]: (v4_relat_1(k1_relat_1('#skF_6'), A_279) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_1208, c_1369])).
% 5.35/2.02  tff(c_1386, plain, (![A_281]: (v4_relat_1(k1_relat_1('#skF_6'), A_281))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_1372])).
% 5.35/2.02  tff(c_34, plain, (![B_28, A_27]: (k7_relat_1(B_28, A_27)=B_28 | ~v4_relat_1(B_28, A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.35/2.02  tff(c_1394, plain, (![A_281]: (k7_relat_1(k1_relat_1('#skF_6'), A_281)=k1_relat_1('#skF_6') | ~v1_relat_1(k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_1386, c_34])).
% 5.35/2.02  tff(c_1804, plain, (![A_307]: (k7_relat_1(k1_relat_1('#skF_6'), A_307)=k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1356, c_1394])).
% 5.35/2.02  tff(c_1158, plain, (![B_262]: (r1_tarski('#skF_6', B_262))), inference(demodulation, [status(thm), theory('equality')], [c_654, c_1131])).
% 5.35/2.02  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.35/2.02  tff(c_1248, plain, (![A_269, B_270, B_271]: (m1_subset_1('#skF_2'(A_269, B_270), B_271) | ~r1_tarski(B_270, B_271) | r1_xboole_0(A_269, B_270))), inference(resolution, [status(thm)], [c_10, c_728])).
% 5.35/2.02  tff(c_89, plain, (![A_63, B_64]: (r2_hidden('#skF_2'(A_63, B_64), B_64) | r1_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.35/2.02  tff(c_94, plain, (![A_63]: (~m1_subset_1('#skF_2'(A_63, k2_relset_1('#skF_4', '#skF_5', '#skF_6')), '#skF_5') | r1_xboole_0(A_63, k2_relset_1('#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_89, c_52])).
% 5.35/2.02  tff(c_838, plain, (![A_63]: (~m1_subset_1('#skF_2'(A_63, '#skF_6'), '#skF_5') | r1_xboole_0(A_63, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_835, c_835, c_94])).
% 5.35/2.02  tff(c_1264, plain, (![A_269]: (~r1_tarski('#skF_6', '#skF_5') | r1_xboole_0(A_269, '#skF_6'))), inference(resolution, [status(thm)], [c_1248, c_838])).
% 5.35/2.02  tff(c_1301, plain, (![A_272]: (r1_xboole_0(A_272, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1158, c_1264])).
% 5.35/2.02  tff(c_40, plain, (![B_31, A_30]: (k7_relat_1(B_31, A_30)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_31), A_30) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.35/2.02  tff(c_693, plain, (![B_31, A_30]: (k7_relat_1(B_31, A_30)='#skF_6' | ~r1_xboole_0(k1_relat_1(B_31), A_30) | ~v1_relat_1(B_31))), inference(demodulation, [status(thm), theory('equality')], [c_432, c_40])).
% 5.35/2.02  tff(c_1426, plain, (![B_285]: (k7_relat_1(B_285, '#skF_6')='#skF_6' | ~v1_relat_1(B_285))), inference(resolution, [status(thm)], [c_1301, c_693])).
% 5.35/2.02  tff(c_1442, plain, (k7_relat_1(k1_relat_1('#skF_6'), '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_1356, c_1426])).
% 5.35/2.02  tff(c_1808, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_1804, c_1442])).
% 5.35/2.02  tff(c_1823, plain, $false, inference(negUnitSimplification, [status(thm)], [c_434, c_1808])).
% 5.35/2.02  tff(c_1824, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_131])).
% 5.35/2.02  tff(c_54, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.35/2.02  tff(c_1829, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1824, c_54])).
% 5.35/2.02  tff(c_1825, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_131])).
% 5.35/2.02  tff(c_1834, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1824, c_1825])).
% 5.35/2.02  tff(c_2182, plain, (![A_373, B_374, C_375]: (k1_relset_1(A_373, B_374, C_375)=k1_relat_1(C_375) | ~m1_subset_1(C_375, k1_zfmisc_1(k2_zfmisc_1(A_373, B_374))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.35/2.02  tff(c_2189, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_2182])).
% 5.35/2.02  tff(c_2192, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1834, c_2189])).
% 5.35/2.02  tff(c_2194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1829, c_2192])).
% 5.35/2.02  tff(c_2195, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_83])).
% 5.35/2.02  tff(c_2635, plain, (![A_462, B_463, C_464]: (k2_relset_1(A_462, B_463, C_464)=k2_relat_1(C_464) | ~m1_subset_1(C_464, k1_zfmisc_1(k2_zfmisc_1(A_462, B_463))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.35/2.02  tff(c_2646, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_2635])).
% 5.35/2.02  tff(c_2650, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2195, c_2646])).
% 5.35/2.02  tff(c_2652, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2225, c_2650])).
% 5.35/2.02  tff(c_2653, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_132])).
% 5.35/2.02  tff(c_2202, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_131])).
% 5.35/2.02  tff(c_2656, plain, (k1_relat_1('#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2653, c_2202])).
% 5.35/2.02  tff(c_2771, plain, (![C_484, B_485, A_486]: (v5_relat_1(C_484, B_485) | ~m1_subset_1(C_484, k1_zfmisc_1(k2_zfmisc_1(A_486, B_485))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.35/2.02  tff(c_2780, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_2771])).
% 5.35/2.02  tff(c_2654, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_132])).
% 5.35/2.02  tff(c_2666, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2653, c_2654])).
% 5.35/2.02  tff(c_2871, plain, (![B_505, A_506]: (r1_tarski(k2_relat_1(B_505), A_506) | ~v5_relat_1(B_505, A_506) | ~v1_relat_1(B_505))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.35/2.02  tff(c_2888, plain, (![A_506]: (r1_tarski('#skF_6', A_506) | ~v5_relat_1('#skF_6', A_506) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2666, c_2871])).
% 5.35/2.02  tff(c_2895, plain, (![A_507]: (r1_tarski('#skF_6', A_507) | ~v5_relat_1('#skF_6', A_507))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_2888])).
% 5.35/2.02  tff(c_2915, plain, (r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_2780, c_2895])).
% 5.35/2.02  tff(c_2954, plain, (![A_522, C_523, B_524]: (m1_subset_1(A_522, C_523) | ~m1_subset_1(B_524, k1_zfmisc_1(C_523)) | ~r2_hidden(A_522, B_524))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.35/2.02  tff(c_2971, plain, (![A_528, B_529, A_530]: (m1_subset_1(A_528, B_529) | ~r2_hidden(A_528, A_530) | ~r1_tarski(A_530, B_529))), inference(resolution, [status(thm)], [c_18, c_2954])).
% 5.35/2.02  tff(c_3266, plain, (![A_571, B_572, B_573]: (m1_subset_1('#skF_2'(A_571, B_572), B_573) | ~r1_tarski(B_572, B_573) | r1_xboole_0(A_571, B_572))), inference(resolution, [status(thm)], [c_10, c_2971])).
% 5.35/2.02  tff(c_2203, plain, (![D_376]: (~r2_hidden(D_376, k1_xboole_0) | ~m1_subset_1(D_376, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2195, c_52])).
% 5.35/2.02  tff(c_2222, plain, (![A_6]: (~m1_subset_1('#skF_2'(A_6, k1_xboole_0), '#skF_5') | r1_xboole_0(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_2203])).
% 5.35/2.02  tff(c_2758, plain, (![A_6]: (~m1_subset_1('#skF_2'(A_6, '#skF_6'), '#skF_5') | r1_xboole_0(A_6, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2653, c_2653, c_2222])).
% 5.35/2.02  tff(c_3289, plain, (![A_571]: (~r1_tarski('#skF_6', '#skF_5') | r1_xboole_0(A_571, '#skF_6'))), inference(resolution, [status(thm)], [c_3266, c_2758])).
% 5.35/2.02  tff(c_3319, plain, (![A_574]: (r1_xboole_0(A_574, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2915, c_3289])).
% 5.35/2.02  tff(c_2944, plain, (![B_31, A_30]: (k7_relat_1(B_31, A_30)='#skF_6' | ~r1_xboole_0(k1_relat_1(B_31), A_30) | ~v1_relat_1(B_31))), inference(demodulation, [status(thm), theory('equality')], [c_2653, c_40])).
% 5.35/2.02  tff(c_3380, plain, (![B_581]: (k7_relat_1(B_581, '#skF_6')='#skF_6' | ~v1_relat_1(B_581))), inference(resolution, [status(thm)], [c_3319, c_2944])).
% 5.35/2.02  tff(c_3401, plain, (![A_582, B_583]: (k7_relat_1(k2_zfmisc_1(A_582, B_583), '#skF_6')='#skF_6')), inference(resolution, [status(thm)], [c_32, c_3380])).
% 5.35/2.02  tff(c_107, plain, (![A_69, B_70]: (~r2_hidden('#skF_1'(A_69, B_70), B_70) | r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.35/2.02  tff(c_112, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_107])).
% 5.35/2.02  tff(c_2710, plain, (![C_469, A_470, B_471]: (v4_relat_1(C_469, A_470) | ~m1_subset_1(C_469, k1_zfmisc_1(k2_zfmisc_1(A_470, B_471))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.35/2.02  tff(c_2743, plain, (![A_475, A_476, B_477]: (v4_relat_1(A_475, A_476) | ~r1_tarski(A_475, k2_zfmisc_1(A_476, B_477)))), inference(resolution, [status(thm)], [c_18, c_2710])).
% 5.35/2.02  tff(c_2751, plain, (![A_476, B_477]: (v4_relat_1(k2_zfmisc_1(A_476, B_477), A_476))), inference(resolution, [status(thm)], [c_112, c_2743])).
% 5.35/2.02  tff(c_2841, plain, (![B_502, A_503]: (k7_relat_1(B_502, A_503)=B_502 | ~v4_relat_1(B_502, A_503) | ~v1_relat_1(B_502))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.35/2.02  tff(c_2847, plain, (![A_476, B_477]: (k7_relat_1(k2_zfmisc_1(A_476, B_477), A_476)=k2_zfmisc_1(A_476, B_477) | ~v1_relat_1(k2_zfmisc_1(A_476, B_477)))), inference(resolution, [status(thm)], [c_2751, c_2841])).
% 5.35/2.02  tff(c_2854, plain, (![A_476, B_477]: (k7_relat_1(k2_zfmisc_1(A_476, B_477), A_476)=k2_zfmisc_1(A_476, B_477))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2847])).
% 5.35/2.02  tff(c_3416, plain, (![B_584]: (k2_zfmisc_1('#skF_6', B_584)='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3401, c_2854])).
% 5.35/2.02  tff(c_2760, plain, (![B_482, A_483]: (r1_tarski(k1_relat_1(B_482), A_483) | ~v4_relat_1(B_482, A_483) | ~v1_relat_1(B_482))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.35/2.02  tff(c_3061, plain, (![B_537, A_538]: (v1_relat_1(k1_relat_1(B_537)) | ~v1_relat_1(A_538) | ~v4_relat_1(B_537, A_538) | ~v1_relat_1(B_537))), inference(resolution, [status(thm)], [c_2760, c_121])).
% 5.35/2.02  tff(c_3065, plain, (![A_476, B_477]: (v1_relat_1(k1_relat_1(k2_zfmisc_1(A_476, B_477))) | ~v1_relat_1(A_476) | ~v1_relat_1(k2_zfmisc_1(A_476, B_477)))), inference(resolution, [status(thm)], [c_2751, c_3061])).
% 5.35/2.02  tff(c_3071, plain, (![A_476, B_477]: (v1_relat_1(k1_relat_1(k2_zfmisc_1(A_476, B_477))) | ~v1_relat_1(A_476))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3065])).
% 5.35/2.02  tff(c_3443, plain, (v1_relat_1(k1_relat_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3416, c_3071])).
% 5.35/2.02  tff(c_3484, plain, (v1_relat_1(k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_3443])).
% 5.35/2.02  tff(c_3535, plain, (![A_586, B_587, B_588]: (m1_subset_1('#skF_1'(A_586, B_587), B_588) | ~r1_tarski(A_586, B_588) | r1_tarski(A_586, B_587))), inference(resolution, [status(thm)], [c_6, c_2971])).
% 5.35/2.02  tff(c_2220, plain, (![B_2]: (~m1_subset_1('#skF_1'(k1_xboole_0, B_2), '#skF_5') | r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_2203])).
% 5.35/2.02  tff(c_2755, plain, (![B_2]: (~m1_subset_1('#skF_1'('#skF_6', B_2), '#skF_5') | r1_tarski('#skF_6', B_2))), inference(demodulation, [status(thm), theory('equality')], [c_2653, c_2653, c_2220])).
% 5.35/2.02  tff(c_3554, plain, (![B_587]: (~r1_tarski('#skF_6', '#skF_5') | r1_tarski('#skF_6', B_587))), inference(resolution, [status(thm)], [c_3535, c_2755])).
% 5.35/2.02  tff(c_3580, plain, (![B_589]: (r1_tarski('#skF_6', B_589))), inference(demodulation, [status(thm), theory('equality')], [c_2915, c_3554])).
% 5.35/2.02  tff(c_2718, plain, (![A_13, A_470, B_471]: (v4_relat_1(A_13, A_470) | ~r1_tarski(A_13, k2_zfmisc_1(A_470, B_471)))), inference(resolution, [status(thm)], [c_18, c_2710])).
% 5.35/2.02  tff(c_3613, plain, (![A_470]: (v4_relat_1('#skF_6', A_470))), inference(resolution, [status(thm)], [c_3580, c_2718])).
% 5.35/2.02  tff(c_3862, plain, (![B_616, A_617, B_618]: (v4_relat_1(k1_relat_1(B_616), A_617) | ~v4_relat_1(B_616, k2_zfmisc_1(A_617, B_618)) | ~v1_relat_1(B_616))), inference(resolution, [status(thm)], [c_2760, c_2718])).
% 5.35/2.02  tff(c_3865, plain, (![A_617]: (v4_relat_1(k1_relat_1('#skF_6'), A_617) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_3613, c_3862])).
% 5.35/2.02  tff(c_3877, plain, (![A_619]: (v4_relat_1(k1_relat_1('#skF_6'), A_619))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_3865])).
% 5.35/2.02  tff(c_3888, plain, (![A_619]: (k7_relat_1(k1_relat_1('#skF_6'), A_619)=k1_relat_1('#skF_6') | ~v1_relat_1(k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_3877, c_34])).
% 5.35/2.02  tff(c_4031, plain, (![A_628]: (k7_relat_1(k1_relat_1('#skF_6'), A_628)=k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_3484, c_3888])).
% 5.35/2.02  tff(c_3326, plain, (![B_31]: (k7_relat_1(B_31, '#skF_6')='#skF_6' | ~v1_relat_1(B_31))), inference(resolution, [status(thm)], [c_3319, c_2944])).
% 5.35/2.02  tff(c_3500, plain, (k7_relat_1(k1_relat_1('#skF_6'), '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_3484, c_3326])).
% 5.35/2.02  tff(c_4035, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_4031, c_3500])).
% 5.35/2.02  tff(c_4050, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2656, c_4035])).
% 5.35/2.02  tff(c_4051, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_131])).
% 5.35/2.02  tff(c_4057, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4051, c_54])).
% 5.35/2.02  tff(c_4052, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_131])).
% 5.35/2.02  tff(c_4062, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4051, c_4052])).
% 5.35/2.02  tff(c_4544, plain, (![A_708, B_709, C_710]: (k1_relset_1(A_708, B_709, C_710)=k1_relat_1(C_710) | ~m1_subset_1(C_710, k1_zfmisc_1(k2_zfmisc_1(A_708, B_709))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.35/2.02  tff(c_4555, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_4544])).
% 5.35/2.02  tff(c_4559, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4062, c_4555])).
% 5.35/2.02  tff(c_4561, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4057, c_4559])).
% 5.35/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.35/2.02  
% 5.35/2.02  Inference rules
% 5.35/2.02  ----------------------
% 5.35/2.02  #Ref     : 0
% 5.35/2.02  #Sup     : 915
% 5.35/2.02  #Fact    : 0
% 5.35/2.02  #Define  : 0
% 5.35/2.02  #Split   : 18
% 5.35/2.02  #Chain   : 0
% 5.35/2.02  #Close   : 0
% 5.35/2.02  
% 5.35/2.02  Ordering : KBO
% 5.35/2.02  
% 5.35/2.02  Simplification rules
% 5.35/2.02  ----------------------
% 5.35/2.02  #Subsume      : 136
% 5.35/2.02  #Demod        : 423
% 5.35/2.02  #Tautology    : 300
% 5.35/2.02  #SimpNegUnit  : 53
% 5.35/2.02  #BackRed      : 50
% 5.35/2.02  
% 5.35/2.02  #Partial instantiations: 0
% 5.35/2.02  #Strategies tried      : 1
% 5.35/2.02  
% 5.35/2.02  Timing (in seconds)
% 5.35/2.02  ----------------------
% 5.35/2.02  Preprocessing        : 0.33
% 5.35/2.02  Parsing              : 0.18
% 5.35/2.02  CNF conversion       : 0.02
% 5.35/2.02  Main loop            : 0.90
% 5.35/2.02  Inferencing          : 0.35
% 5.35/2.02  Reduction            : 0.26
% 5.35/2.02  Demodulation         : 0.18
% 5.35/2.02  BG Simplification    : 0.04
% 5.35/2.02  Subsumption          : 0.16
% 5.35/2.02  Abstraction          : 0.04
% 5.35/2.02  MUC search           : 0.00
% 5.35/2.02  Cooper               : 0.00
% 5.35/2.02  Total                : 1.29
% 5.35/2.02  Index Insertion      : 0.00
% 5.35/2.02  Index Deletion       : 0.00
% 5.35/2.02  Index Matching       : 0.00
% 5.35/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
