%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:06 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 226 expanded)
%              Number of leaves         :   36 (  94 expanded)
%              Depth                    :    8
%              Number of atoms          :  124 ( 497 expanded)
%              Number of equality atoms :   19 (  67 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_11 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ! [D] :
                    ( r2_hidden(D,k2_relset_1(B,A,C))
                  <=> ? [E] :
                        ( m1_subset_1(E,B)
                        & r2_hidden(k4_tarski(E,D),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_256,plain,(
    ! [A_131,B_132,C_133] :
      ( k2_relset_1(A_131,B_132,C_133) = k2_relat_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_260,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_256])).

tff(c_50,plain,
    ( m1_subset_1('#skF_10','#skF_7')
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_58,plain,(
    r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_262,plain,(
    r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_58])).

tff(c_52,plain,(
    ! [C_85,A_86,B_87] :
      ( v1_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_56,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_52])).

tff(c_498,plain,(
    ! [A_178,B_179,C_180,D_181] :
      ( k7_relset_1(A_178,B_179,C_180,D_181) = k9_relat_1(C_180,D_181)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_501,plain,(
    ! [D_181] : k7_relset_1('#skF_7','#skF_6','#skF_8',D_181) = k9_relat_1('#skF_8',D_181) ),
    inference(resolution,[status(thm)],[c_34,c_498])).

tff(c_554,plain,(
    ! [A_199,B_200,C_201] :
      ( k7_relset_1(A_199,B_200,C_201,A_199) = k2_relset_1(A_199,B_200,C_201)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(A_199,B_200))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_559,plain,(
    k7_relset_1('#skF_7','#skF_6','#skF_8','#skF_7') = k2_relset_1('#skF_7','#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_554])).

tff(c_562,plain,(
    k9_relat_1('#skF_8','#skF_7') = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_260,c_559])).

tff(c_272,plain,(
    ! [A_134,B_135,C_136] :
      ( r2_hidden('#skF_5'(A_134,B_135,C_136),B_135)
      | ~ r2_hidden(A_134,k9_relat_1(C_136,B_135))
      | ~ v1_relat_1(C_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_276,plain,(
    ! [A_134,B_135,C_136] :
      ( m1_subset_1('#skF_5'(A_134,B_135,C_136),B_135)
      | ~ r2_hidden(A_134,k9_relat_1(C_136,B_135))
      | ~ v1_relat_1(C_136) ) ),
    inference(resolution,[status(thm)],[c_272,c_2])).

tff(c_565,plain,(
    ! [A_134] :
      ( m1_subset_1('#skF_5'(A_134,'#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_134,k2_relat_1('#skF_8'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_562,c_276])).

tff(c_571,plain,(
    ! [A_202] :
      ( m1_subset_1('#skF_5'(A_202,'#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_202,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_565])).

tff(c_594,plain,(
    m1_subset_1('#skF_5'('#skF_11','#skF_7','#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_262,c_571])).

tff(c_595,plain,(
    ! [A_203,B_204,C_205] :
      ( r2_hidden(k4_tarski('#skF_5'(A_203,B_204,C_205),A_203),C_205)
      | ~ r2_hidden(A_203,k9_relat_1(C_205,B_204))
      | ~ v1_relat_1(C_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_40,plain,(
    ! [E_82] :
      ( ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8'))
      | ~ r2_hidden(k4_tarski(E_82,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_82,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_458,plain,(
    ! [E_82] :
      ( ~ r2_hidden('#skF_9',k2_relat_1('#skF_8'))
      | ~ r2_hidden(k4_tarski(E_82,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_82,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_40])).

tff(c_459,plain,(
    ~ r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_458])).

tff(c_332,plain,(
    ! [A_152,B_153,C_154,D_155] :
      ( k7_relset_1(A_152,B_153,C_154,D_155) = k9_relat_1(C_154,D_155)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_339,plain,(
    ! [D_155] : k7_relset_1('#skF_7','#skF_6','#skF_8',D_155) = k9_relat_1('#skF_8',D_155) ),
    inference(resolution,[status(thm)],[c_34,c_332])).

tff(c_362,plain,(
    ! [A_163,B_164,C_165] :
      ( k7_relset_1(A_163,B_164,C_165,A_163) = k2_relset_1(A_163,B_164,C_165)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_367,plain,(
    k7_relset_1('#skF_7','#skF_6','#skF_8','#skF_7') = k2_relset_1('#skF_7','#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_362])).

tff(c_370,plain,(
    k9_relat_1('#skF_8','#skF_7') = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_260,c_367])).

tff(c_373,plain,(
    ! [A_134] :
      ( m1_subset_1('#skF_5'(A_134,'#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_134,k2_relat_1('#skF_8'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_276])).

tff(c_379,plain,(
    ! [A_166] :
      ( m1_subset_1('#skF_5'(A_166,'#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_166,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_373])).

tff(c_398,plain,(
    m1_subset_1('#skF_5'('#skF_11','#skF_7','#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_262,c_379])).

tff(c_399,plain,(
    ! [A_167,B_168,C_169] :
      ( r2_hidden(k4_tarski('#skF_5'(A_167,B_168,C_169),A_167),C_169)
      | ~ r2_hidden(A_167,k9_relat_1(C_169,B_168))
      | ~ v1_relat_1(C_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_42,plain,(
    ! [E_82] :
      ( r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8')
      | ~ r2_hidden(k4_tarski(E_82,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_82,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_291,plain,(
    ! [E_82] :
      ( ~ r2_hidden(k4_tarski(E_82,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_82,'#skF_7') ) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_410,plain,(
    ! [B_168] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_168,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_168))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_399,c_291])).

tff(c_450,plain,(
    ! [B_173] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_173,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_173)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_410])).

tff(c_453,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_11','#skF_7','#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_450])).

tff(c_456,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_398,c_453])).

tff(c_457,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_6,plain,(
    ! [C_18,A_3,D_21] :
      ( r2_hidden(C_18,k2_relat_1(A_3))
      | ~ r2_hidden(k4_tarski(D_21,C_18),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_462,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_457,c_6])).

tff(c_469,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_459,c_462])).

tff(c_470,plain,(
    ! [E_82] :
      ( ~ r2_hidden(k4_tarski(E_82,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_82,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_458])).

tff(c_606,plain,(
    ! [B_204] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_204,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_204))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_595,c_470])).

tff(c_669,plain,(
    ! [B_211] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_211,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_211)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_606])).

tff(c_672,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_11','#skF_7','#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_562,c_669])).

tff(c_675,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_594,c_672])).

tff(c_677,plain,(
    ~ r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,
    ( r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8')
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_679,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_677,c_48])).

tff(c_686,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_679,c_6])).

tff(c_692,plain,(
    ! [A_212,B_213,C_214] :
      ( k2_relset_1(A_212,B_213,C_214) = k2_relat_1(C_214)
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(A_212,B_213))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_696,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_692])).

tff(c_46,plain,
    ( ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8'))
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_697,plain,(
    ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_677,c_46])).

tff(c_698,plain,(
    ~ r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_696,c_697])).

tff(c_702,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_686,c_698])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:53:54 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.43  
% 2.84/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.43  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_11 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1
% 2.84/1.43  
% 2.84/1.43  %Foreground sorts:
% 2.84/1.43  
% 2.84/1.43  
% 2.84/1.43  %Background operators:
% 2.84/1.43  
% 2.84/1.43  
% 2.84/1.43  %Foreground operators:
% 2.84/1.43  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.84/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.84/1.43  tff('#skF_11', type, '#skF_11': $i).
% 2.84/1.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.84/1.43  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.84/1.43  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.84/1.43  tff('#skF_7', type, '#skF_7': $i).
% 2.84/1.43  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.84/1.43  tff('#skF_10', type, '#skF_10': $i).
% 2.84/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.84/1.43  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.84/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.84/1.43  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.84/1.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.84/1.43  tff('#skF_9', type, '#skF_9': $i).
% 2.84/1.43  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.84/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.84/1.43  tff('#skF_8', type, '#skF_8': $i).
% 2.84/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.84/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.84/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.84/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.84/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.84/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.84/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.84/1.43  
% 2.84/1.45  tff(f_85, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (![D]: (r2_hidden(D, k2_relset_1(B, A, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(E, D), C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relset_1)).
% 2.84/1.45  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.84/1.45  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.84/1.45  tff(f_60, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.84/1.45  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 2.84/1.45  tff(f_48, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 2.84/1.45  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.84/1.45  tff(f_37, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 2.84/1.45  tff(c_34, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.84/1.45  tff(c_256, plain, (![A_131, B_132, C_133]: (k2_relset_1(A_131, B_132, C_133)=k2_relat_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.84/1.45  tff(c_260, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_34, c_256])).
% 2.84/1.45  tff(c_50, plain, (m1_subset_1('#skF_10', '#skF_7') | r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.84/1.45  tff(c_58, plain, (r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_50])).
% 2.84/1.45  tff(c_262, plain, (r2_hidden('#skF_11', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_260, c_58])).
% 2.84/1.45  tff(c_52, plain, (![C_85, A_86, B_87]: (v1_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.84/1.45  tff(c_56, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_34, c_52])).
% 2.84/1.45  tff(c_498, plain, (![A_178, B_179, C_180, D_181]: (k7_relset_1(A_178, B_179, C_180, D_181)=k9_relat_1(C_180, D_181) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.84/1.45  tff(c_501, plain, (![D_181]: (k7_relset_1('#skF_7', '#skF_6', '#skF_8', D_181)=k9_relat_1('#skF_8', D_181))), inference(resolution, [status(thm)], [c_34, c_498])).
% 2.84/1.45  tff(c_554, plain, (![A_199, B_200, C_201]: (k7_relset_1(A_199, B_200, C_201, A_199)=k2_relset_1(A_199, B_200, C_201) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(A_199, B_200))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.84/1.45  tff(c_559, plain, (k7_relset_1('#skF_7', '#skF_6', '#skF_8', '#skF_7')=k2_relset_1('#skF_7', '#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_34, c_554])).
% 2.84/1.45  tff(c_562, plain, (k9_relat_1('#skF_8', '#skF_7')=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_501, c_260, c_559])).
% 2.84/1.45  tff(c_272, plain, (![A_134, B_135, C_136]: (r2_hidden('#skF_5'(A_134, B_135, C_136), B_135) | ~r2_hidden(A_134, k9_relat_1(C_136, B_135)) | ~v1_relat_1(C_136))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.84/1.45  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.84/1.45  tff(c_276, plain, (![A_134, B_135, C_136]: (m1_subset_1('#skF_5'(A_134, B_135, C_136), B_135) | ~r2_hidden(A_134, k9_relat_1(C_136, B_135)) | ~v1_relat_1(C_136))), inference(resolution, [status(thm)], [c_272, c_2])).
% 2.84/1.45  tff(c_565, plain, (![A_134]: (m1_subset_1('#skF_5'(A_134, '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_134, k2_relat_1('#skF_8')) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_562, c_276])).
% 2.84/1.45  tff(c_571, plain, (![A_202]: (m1_subset_1('#skF_5'(A_202, '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_202, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_565])).
% 2.84/1.45  tff(c_594, plain, (m1_subset_1('#skF_5'('#skF_11', '#skF_7', '#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_262, c_571])).
% 2.84/1.45  tff(c_595, plain, (![A_203, B_204, C_205]: (r2_hidden(k4_tarski('#skF_5'(A_203, B_204, C_205), A_203), C_205) | ~r2_hidden(A_203, k9_relat_1(C_205, B_204)) | ~v1_relat_1(C_205))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.84/1.45  tff(c_40, plain, (![E_82]: (~r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_6', '#skF_8')) | ~r2_hidden(k4_tarski(E_82, '#skF_11'), '#skF_8') | ~m1_subset_1(E_82, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.84/1.45  tff(c_458, plain, (![E_82]: (~r2_hidden('#skF_9', k2_relat_1('#skF_8')) | ~r2_hidden(k4_tarski(E_82, '#skF_11'), '#skF_8') | ~m1_subset_1(E_82, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_260, c_40])).
% 2.84/1.45  tff(c_459, plain, (~r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_458])).
% 2.84/1.45  tff(c_332, plain, (![A_152, B_153, C_154, D_155]: (k7_relset_1(A_152, B_153, C_154, D_155)=k9_relat_1(C_154, D_155) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.84/1.45  tff(c_339, plain, (![D_155]: (k7_relset_1('#skF_7', '#skF_6', '#skF_8', D_155)=k9_relat_1('#skF_8', D_155))), inference(resolution, [status(thm)], [c_34, c_332])).
% 2.84/1.45  tff(c_362, plain, (![A_163, B_164, C_165]: (k7_relset_1(A_163, B_164, C_165, A_163)=k2_relset_1(A_163, B_164, C_165) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_163, B_164))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.84/1.45  tff(c_367, plain, (k7_relset_1('#skF_7', '#skF_6', '#skF_8', '#skF_7')=k2_relset_1('#skF_7', '#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_34, c_362])).
% 2.84/1.45  tff(c_370, plain, (k9_relat_1('#skF_8', '#skF_7')=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_339, c_260, c_367])).
% 2.84/1.45  tff(c_373, plain, (![A_134]: (m1_subset_1('#skF_5'(A_134, '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_134, k2_relat_1('#skF_8')) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_370, c_276])).
% 2.84/1.45  tff(c_379, plain, (![A_166]: (m1_subset_1('#skF_5'(A_166, '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_166, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_373])).
% 2.84/1.45  tff(c_398, plain, (m1_subset_1('#skF_5'('#skF_11', '#skF_7', '#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_262, c_379])).
% 2.84/1.45  tff(c_399, plain, (![A_167, B_168, C_169]: (r2_hidden(k4_tarski('#skF_5'(A_167, B_168, C_169), A_167), C_169) | ~r2_hidden(A_167, k9_relat_1(C_169, B_168)) | ~v1_relat_1(C_169))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.84/1.45  tff(c_42, plain, (![E_82]: (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8') | ~r2_hidden(k4_tarski(E_82, '#skF_11'), '#skF_8') | ~m1_subset_1(E_82, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.84/1.45  tff(c_291, plain, (![E_82]: (~r2_hidden(k4_tarski(E_82, '#skF_11'), '#skF_8') | ~m1_subset_1(E_82, '#skF_7'))), inference(splitLeft, [status(thm)], [c_42])).
% 2.84/1.45  tff(c_410, plain, (![B_168]: (~m1_subset_1('#skF_5'('#skF_11', B_168, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_168)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_399, c_291])).
% 2.84/1.45  tff(c_450, plain, (![B_173]: (~m1_subset_1('#skF_5'('#skF_11', B_173, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_173)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_410])).
% 2.84/1.45  tff(c_453, plain, (~m1_subset_1('#skF_5'('#skF_11', '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k2_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_370, c_450])).
% 2.84/1.45  tff(c_456, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_262, c_398, c_453])).
% 2.84/1.45  tff(c_457, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_42])).
% 2.84/1.45  tff(c_6, plain, (![C_18, A_3, D_21]: (r2_hidden(C_18, k2_relat_1(A_3)) | ~r2_hidden(k4_tarski(D_21, C_18), A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.84/1.45  tff(c_462, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_457, c_6])).
% 2.84/1.45  tff(c_469, plain, $false, inference(negUnitSimplification, [status(thm)], [c_459, c_462])).
% 2.84/1.45  tff(c_470, plain, (![E_82]: (~r2_hidden(k4_tarski(E_82, '#skF_11'), '#skF_8') | ~m1_subset_1(E_82, '#skF_7'))), inference(splitRight, [status(thm)], [c_458])).
% 2.84/1.45  tff(c_606, plain, (![B_204]: (~m1_subset_1('#skF_5'('#skF_11', B_204, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_204)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_595, c_470])).
% 2.84/1.45  tff(c_669, plain, (![B_211]: (~m1_subset_1('#skF_5'('#skF_11', B_211, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_211)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_606])).
% 2.84/1.45  tff(c_672, plain, (~m1_subset_1('#skF_5'('#skF_11', '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k2_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_562, c_669])).
% 2.84/1.45  tff(c_675, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_262, c_594, c_672])).
% 2.84/1.45  tff(c_677, plain, (~r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_50])).
% 2.84/1.45  tff(c_48, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8') | r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.84/1.45  tff(c_679, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_677, c_48])).
% 2.84/1.45  tff(c_686, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_679, c_6])).
% 2.84/1.45  tff(c_692, plain, (![A_212, B_213, C_214]: (k2_relset_1(A_212, B_213, C_214)=k2_relat_1(C_214) | ~m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(A_212, B_213))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.84/1.45  tff(c_696, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_34, c_692])).
% 2.84/1.45  tff(c_46, plain, (~r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_6', '#skF_8')) | r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.84/1.45  tff(c_697, plain, (~r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_677, c_46])).
% 2.84/1.45  tff(c_698, plain, (~r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_696, c_697])).
% 2.84/1.45  tff(c_702, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_686, c_698])).
% 2.84/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.45  
% 2.84/1.45  Inference rules
% 2.84/1.45  ----------------------
% 2.84/1.45  #Ref     : 0
% 2.84/1.45  #Sup     : 134
% 2.84/1.45  #Fact    : 0
% 2.84/1.45  #Define  : 0
% 2.84/1.45  #Split   : 6
% 2.84/1.45  #Chain   : 0
% 2.84/1.45  #Close   : 0
% 2.84/1.45  
% 2.84/1.45  Ordering : KBO
% 2.84/1.45  
% 2.84/1.45  Simplification rules
% 2.84/1.45  ----------------------
% 2.84/1.45  #Subsume      : 2
% 2.84/1.45  #Demod        : 42
% 2.84/1.45  #Tautology    : 31
% 2.84/1.45  #SimpNegUnit  : 3
% 2.84/1.45  #BackRed      : 6
% 2.84/1.45  
% 2.84/1.45  #Partial instantiations: 0
% 2.84/1.45  #Strategies tried      : 1
% 2.84/1.45  
% 2.84/1.45  Timing (in seconds)
% 2.84/1.45  ----------------------
% 2.84/1.45  Preprocessing        : 0.32
% 2.84/1.45  Parsing              : 0.17
% 2.84/1.45  CNF conversion       : 0.03
% 2.84/1.45  Main loop            : 0.40
% 2.84/1.46  Inferencing          : 0.16
% 2.84/1.46  Reduction            : 0.11
% 2.84/1.46  Demodulation         : 0.08
% 2.84/1.46  BG Simplification    : 0.02
% 2.84/1.46  Subsumption          : 0.06
% 2.84/1.46  Abstraction          : 0.03
% 2.84/1.46  MUC search           : 0.00
% 2.84/1.46  Cooper               : 0.00
% 2.84/1.46  Total                : 0.76
% 2.84/1.46  Index Insertion      : 0.00
% 2.84/1.46  Index Deletion       : 0.00
% 2.84/1.46  Index Matching       : 0.00
% 2.84/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
