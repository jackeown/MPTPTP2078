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
% DateTime   : Thu Dec  3 10:08:14 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 203 expanded)
%              Number of leaves         :   37 (  82 expanded)
%              Depth                    :    8
%              Number of atoms          :  148 ( 406 expanded)
%              Number of equality atoms :   40 (  77 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k3_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_relset_1,type,(
    k3_relset_1: ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_121,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_70,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_54,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_32,plain,(
    ! [A_22,B_23] : v1_relat_1(k2_zfmisc_1(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_101,plain,(
    ! [B_66,A_67] :
      ( v1_relat_1(B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_67))
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_107,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_101])).

tff(c_111,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_107])).

tff(c_36,plain,(
    ! [A_24] :
      ( k2_relat_1(A_24) = k1_xboole_0
      | k1_relat_1(A_24) != k1_xboole_0
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_115,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_111,c_36])).

tff(c_116,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_544,plain,(
    ! [A_145] :
      ( k1_relat_1(A_145) = k1_xboole_0
      | k2_relat_1(A_145) != k1_xboole_0
      | ~ v1_relat_1(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_553,plain,
    ( k1_relat_1('#skF_5') = k1_xboole_0
    | k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_111,c_544])).

tff(c_561,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_553])).

tff(c_129,plain,(
    ! [A_70] :
      ( k1_relat_1(A_70) = k1_xboole_0
      | k2_relat_1(A_70) != k1_xboole_0
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_132,plain,
    ( k1_relat_1('#skF_5') = k1_xboole_0
    | k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_111,c_129])).

tff(c_138,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_132])).

tff(c_247,plain,(
    ! [C_95,B_96,A_97] :
      ( v5_relat_1(C_95,B_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_97,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_256,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_247])).

tff(c_30,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k2_relat_1(B_21),A_20)
      | ~ v5_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_318,plain,(
    ! [A_111,C_112,B_113] :
      ( m1_subset_1(A_111,C_112)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(C_112))
      | ~ r2_hidden(A_111,B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_356,plain,(
    ! [A_122,B_123,A_124] :
      ( m1_subset_1(A_122,B_123)
      | ~ r2_hidden(A_122,A_124)
      | ~ r1_tarski(A_124,B_123) ) ),
    inference(resolution,[status(thm)],[c_22,c_318])).

tff(c_411,plain,(
    ! [A_132,B_133] :
      ( m1_subset_1('#skF_1'(A_132),B_133)
      | ~ r1_tarski(A_132,B_133)
      | v1_xboole_0(A_132) ) ),
    inference(resolution,[status(thm)],[c_4,c_356])).

tff(c_328,plain,(
    ! [A_118,B_119,C_120] :
      ( k2_relset_1(A_118,B_119,C_120) = k2_relat_1(C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_337,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_328])).

tff(c_70,plain,(
    ! [D_58] :
      ( ~ r2_hidden(D_58,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_58,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_75,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4')
    | v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_70])).

tff(c_117,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_339,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_5')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_117])).

tff(c_443,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_411,c_339])).

tff(c_451,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_443])).

tff(c_454,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_451])).

tff(c_461,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_256,c_454])).

tff(c_462,plain,(
    v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_443])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_141,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_2'(A_73,B_74),A_73)
      | r1_tarski(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_156,plain,(
    ! [A_73,B_74] :
      ( ~ v1_xboole_0(A_73)
      | r1_tarski(A_73,B_74) ) ),
    inference(resolution,[status(thm)],[c_141,c_2])).

tff(c_157,plain,(
    ! [A_75,B_76] :
      ( ~ v1_xboole_0(A_75)
      | r1_tarski(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_141,c_2])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_195,plain,(
    ! [B_82,A_83] :
      ( B_82 = A_83
      | ~ r1_tarski(B_82,A_83)
      | ~ v1_xboole_0(A_83) ) ),
    inference(resolution,[status(thm)],[c_157,c_14])).

tff(c_209,plain,(
    ! [B_84,A_85] :
      ( B_84 = A_85
      | ~ v1_xboole_0(B_84)
      | ~ v1_xboole_0(A_85) ) ),
    inference(resolution,[status(thm)],[c_156,c_195])).

tff(c_212,plain,(
    ! [A_85] :
      ( k1_xboole_0 = A_85
      | ~ v1_xboole_0(A_85) ) ),
    inference(resolution,[status(thm)],[c_12,c_209])).

tff(c_468,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_462,c_212])).

tff(c_480,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_468])).

tff(c_481,plain,(
    v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_495,plain,(
    ! [A_139,B_140] :
      ( r2_hidden('#skF_2'(A_139,B_140),A_139)
      | r1_tarski(A_139,B_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_510,plain,(
    ! [A_139,B_140] :
      ( ~ v1_xboole_0(A_139)
      | r1_tarski(A_139,B_140) ) ),
    inference(resolution,[status(thm)],[c_495,c_2])).

tff(c_511,plain,(
    ! [A_141,B_142] :
      ( ~ v1_xboole_0(A_141)
      | r1_tarski(A_141,B_142) ) ),
    inference(resolution,[status(thm)],[c_495,c_2])).

tff(c_570,plain,(
    ! [B_146,A_147] :
      ( B_146 = A_147
      | ~ r1_tarski(B_146,A_147)
      | ~ v1_xboole_0(A_147) ) ),
    inference(resolution,[status(thm)],[c_511,c_14])).

tff(c_584,plain,(
    ! [B_148,A_149] :
      ( B_148 = A_149
      | ~ v1_xboole_0(B_148)
      | ~ v1_xboole_0(A_149) ) ),
    inference(resolution,[status(thm)],[c_510,c_570])).

tff(c_601,plain,(
    ! [A_153] :
      ( k1_xboole_0 = A_153
      | ~ v1_xboole_0(A_153) ) ),
    inference(resolution,[status(thm)],[c_12,c_584])).

tff(c_608,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_481,c_601])).

tff(c_917,plain,(
    ! [A_209,B_210,C_211] :
      ( k2_relset_1(A_209,B_210,C_211) = k2_relat_1(C_211)
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(A_209,B_210))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_928,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_917])).

tff(c_932,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_928])).

tff(c_934,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_561,c_932])).

tff(c_936,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_1679,plain,(
    ! [A_325,B_326,C_327] :
      ( k1_relset_1(A_325,B_326,C_327) = k1_relat_1(C_327)
      | ~ m1_subset_1(C_327,k1_zfmisc_1(k2_zfmisc_1(A_325,B_326))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1686,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_1679])).

tff(c_1689,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_936,c_1686])).

tff(c_1691,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1689])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:42:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.64  
% 3.47/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.64  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k3_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.47/1.64  
% 3.47/1.64  %Foreground sorts:
% 3.47/1.64  
% 3.47/1.64  
% 3.47/1.64  %Background operators:
% 3.47/1.64  
% 3.47/1.64  
% 3.47/1.64  %Foreground operators:
% 3.47/1.64  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.47/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.47/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.47/1.64  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.47/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.47/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.47/1.64  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 3.47/1.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.47/1.64  tff('#skF_5', type, '#skF_5': $i).
% 3.47/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.47/1.64  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.47/1.64  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.47/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.47/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.47/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.47/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.47/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.47/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.47/1.64  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.47/1.64  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.47/1.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.47/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.47/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.47/1.64  
% 3.84/1.67  tff(f_121, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 3.84/1.67  tff(f_70, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.84/1.67  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.84/1.67  tff(f_76, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 3.84/1.67  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.84/1.67  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.84/1.67  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.84/1.67  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.84/1.67  tff(f_55, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.84/1.67  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.84/1.67  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.84/1.67  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.84/1.67  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.84/1.67  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.84/1.67  tff(c_54, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.84/1.67  tff(c_32, plain, (![A_22, B_23]: (v1_relat_1(k2_zfmisc_1(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.84/1.67  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.84/1.67  tff(c_101, plain, (![B_66, A_67]: (v1_relat_1(B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(A_67)) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.84/1.67  tff(c_107, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_56, c_101])).
% 3.84/1.67  tff(c_111, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_107])).
% 3.84/1.67  tff(c_36, plain, (![A_24]: (k2_relat_1(A_24)=k1_xboole_0 | k1_relat_1(A_24)!=k1_xboole_0 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.84/1.67  tff(c_115, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k1_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_111, c_36])).
% 3.84/1.67  tff(c_116, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_115])).
% 3.84/1.67  tff(c_544, plain, (![A_145]: (k1_relat_1(A_145)=k1_xboole_0 | k2_relat_1(A_145)!=k1_xboole_0 | ~v1_relat_1(A_145))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.84/1.67  tff(c_553, plain, (k1_relat_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_111, c_544])).
% 3.84/1.67  tff(c_561, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_116, c_553])).
% 3.84/1.67  tff(c_129, plain, (![A_70]: (k1_relat_1(A_70)=k1_xboole_0 | k2_relat_1(A_70)!=k1_xboole_0 | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.84/1.67  tff(c_132, plain, (k1_relat_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_111, c_129])).
% 3.84/1.67  tff(c_138, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_116, c_132])).
% 3.84/1.67  tff(c_247, plain, (![C_95, B_96, A_97]: (v5_relat_1(C_95, B_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_97, B_96))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.84/1.67  tff(c_256, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_247])).
% 3.84/1.67  tff(c_30, plain, (![B_21, A_20]: (r1_tarski(k2_relat_1(B_21), A_20) | ~v5_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.84/1.67  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.84/1.67  tff(c_22, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.84/1.67  tff(c_318, plain, (![A_111, C_112, B_113]: (m1_subset_1(A_111, C_112) | ~m1_subset_1(B_113, k1_zfmisc_1(C_112)) | ~r2_hidden(A_111, B_113))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.84/1.67  tff(c_356, plain, (![A_122, B_123, A_124]: (m1_subset_1(A_122, B_123) | ~r2_hidden(A_122, A_124) | ~r1_tarski(A_124, B_123))), inference(resolution, [status(thm)], [c_22, c_318])).
% 3.84/1.67  tff(c_411, plain, (![A_132, B_133]: (m1_subset_1('#skF_1'(A_132), B_133) | ~r1_tarski(A_132, B_133) | v1_xboole_0(A_132))), inference(resolution, [status(thm)], [c_4, c_356])).
% 3.84/1.67  tff(c_328, plain, (![A_118, B_119, C_120]: (k2_relset_1(A_118, B_119, C_120)=k2_relat_1(C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.84/1.67  tff(c_337, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_328])).
% 3.84/1.67  tff(c_70, plain, (![D_58]: (~r2_hidden(D_58, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_58, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.84/1.67  tff(c_75, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4') | v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_4, c_70])).
% 3.84/1.67  tff(c_117, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_75])).
% 3.84/1.67  tff(c_339, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_5')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_337, c_117])).
% 3.84/1.67  tff(c_443, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | v1_xboole_0(k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_411, c_339])).
% 3.84/1.67  tff(c_451, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_443])).
% 3.84/1.67  tff(c_454, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_451])).
% 3.84/1.67  tff(c_461, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_111, c_256, c_454])).
% 3.84/1.67  tff(c_462, plain, (v1_xboole_0(k2_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_443])).
% 3.84/1.67  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.84/1.67  tff(c_141, plain, (![A_73, B_74]: (r2_hidden('#skF_2'(A_73, B_74), A_73) | r1_tarski(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.84/1.67  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.84/1.67  tff(c_156, plain, (![A_73, B_74]: (~v1_xboole_0(A_73) | r1_tarski(A_73, B_74))), inference(resolution, [status(thm)], [c_141, c_2])).
% 3.84/1.67  tff(c_157, plain, (![A_75, B_76]: (~v1_xboole_0(A_75) | r1_tarski(A_75, B_76))), inference(resolution, [status(thm)], [c_141, c_2])).
% 3.84/1.67  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.84/1.67  tff(c_195, plain, (![B_82, A_83]: (B_82=A_83 | ~r1_tarski(B_82, A_83) | ~v1_xboole_0(A_83))), inference(resolution, [status(thm)], [c_157, c_14])).
% 3.84/1.67  tff(c_209, plain, (![B_84, A_85]: (B_84=A_85 | ~v1_xboole_0(B_84) | ~v1_xboole_0(A_85))), inference(resolution, [status(thm)], [c_156, c_195])).
% 3.84/1.67  tff(c_212, plain, (![A_85]: (k1_xboole_0=A_85 | ~v1_xboole_0(A_85))), inference(resolution, [status(thm)], [c_12, c_209])).
% 3.84/1.67  tff(c_468, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_462, c_212])).
% 3.84/1.67  tff(c_480, plain, $false, inference(negUnitSimplification, [status(thm)], [c_138, c_468])).
% 3.84/1.67  tff(c_481, plain, (v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_75])).
% 3.84/1.67  tff(c_495, plain, (![A_139, B_140]: (r2_hidden('#skF_2'(A_139, B_140), A_139) | r1_tarski(A_139, B_140))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.84/1.67  tff(c_510, plain, (![A_139, B_140]: (~v1_xboole_0(A_139) | r1_tarski(A_139, B_140))), inference(resolution, [status(thm)], [c_495, c_2])).
% 3.84/1.67  tff(c_511, plain, (![A_141, B_142]: (~v1_xboole_0(A_141) | r1_tarski(A_141, B_142))), inference(resolution, [status(thm)], [c_495, c_2])).
% 3.84/1.67  tff(c_570, plain, (![B_146, A_147]: (B_146=A_147 | ~r1_tarski(B_146, A_147) | ~v1_xboole_0(A_147))), inference(resolution, [status(thm)], [c_511, c_14])).
% 3.84/1.67  tff(c_584, plain, (![B_148, A_149]: (B_148=A_149 | ~v1_xboole_0(B_148) | ~v1_xboole_0(A_149))), inference(resolution, [status(thm)], [c_510, c_570])).
% 3.84/1.67  tff(c_601, plain, (![A_153]: (k1_xboole_0=A_153 | ~v1_xboole_0(A_153))), inference(resolution, [status(thm)], [c_12, c_584])).
% 3.84/1.67  tff(c_608, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_481, c_601])).
% 3.84/1.67  tff(c_917, plain, (![A_209, B_210, C_211]: (k2_relset_1(A_209, B_210, C_211)=k2_relat_1(C_211) | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(A_209, B_210))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.84/1.67  tff(c_928, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_917])).
% 3.84/1.67  tff(c_932, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_608, c_928])).
% 3.84/1.67  tff(c_934, plain, $false, inference(negUnitSimplification, [status(thm)], [c_561, c_932])).
% 3.84/1.67  tff(c_936, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_115])).
% 3.84/1.67  tff(c_1679, plain, (![A_325, B_326, C_327]: (k1_relset_1(A_325, B_326, C_327)=k1_relat_1(C_327) | ~m1_subset_1(C_327, k1_zfmisc_1(k2_zfmisc_1(A_325, B_326))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.84/1.67  tff(c_1686, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_1679])).
% 3.84/1.67  tff(c_1689, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_936, c_1686])).
% 3.84/1.67  tff(c_1691, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_1689])).
% 3.84/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.84/1.67  
% 3.84/1.67  Inference rules
% 3.84/1.67  ----------------------
% 3.84/1.67  #Ref     : 0
% 3.84/1.67  #Sup     : 321
% 3.84/1.67  #Fact    : 0
% 3.84/1.67  #Define  : 0
% 3.84/1.67  #Split   : 22
% 3.84/1.67  #Chain   : 0
% 3.84/1.67  #Close   : 0
% 3.84/1.67  
% 3.84/1.67  Ordering : KBO
% 3.84/1.67  
% 3.84/1.67  Simplification rules
% 3.84/1.67  ----------------------
% 3.84/1.67  #Subsume      : 32
% 3.84/1.67  #Demod        : 126
% 3.84/1.67  #Tautology    : 104
% 3.84/1.67  #SimpNegUnit  : 22
% 3.84/1.67  #BackRed      : 20
% 3.84/1.67  
% 3.84/1.67  #Partial instantiations: 0
% 3.84/1.67  #Strategies tried      : 1
% 3.84/1.67  
% 3.84/1.67  Timing (in seconds)
% 3.84/1.67  ----------------------
% 3.84/1.67  Preprocessing        : 0.35
% 3.84/1.68  Parsing              : 0.19
% 3.84/1.68  CNF conversion       : 0.02
% 3.84/1.68  Main loop            : 0.50
% 3.84/1.68  Inferencing          : 0.19
% 3.84/1.68  Reduction            : 0.14
% 3.84/1.68  Demodulation         : 0.09
% 3.84/1.68  BG Simplification    : 0.02
% 3.84/1.68  Subsumption          : 0.09
% 3.84/1.68  Abstraction          : 0.02
% 3.84/1.68  MUC search           : 0.00
% 3.84/1.68  Cooper               : 0.00
% 3.84/1.68  Total                : 0.90
% 3.84/1.68  Index Insertion      : 0.00
% 3.84/1.68  Index Deletion       : 0.00
% 3.84/1.68  Index Matching       : 0.00
% 3.84/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
