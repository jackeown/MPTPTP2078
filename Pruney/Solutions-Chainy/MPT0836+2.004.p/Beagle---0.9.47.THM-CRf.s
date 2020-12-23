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
% DateTime   : Thu Dec  3 10:08:03 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 177 expanded)
%              Number of leaves         :   34 (  74 expanded)
%              Depth                    :   11
%              Number of atoms          :  133 ( 399 expanded)
%              Number of equality atoms :   15 (  30 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k11_relat_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ! [D] :
                    ( m1_subset_1(D,A)
                   => ( r2_hidden(D,k1_relset_1(A,B,C))
                    <=> ? [E] :
                          ( m1_subset_1(E,B)
                          & r2_hidden(k4_tarski(D,E),C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(c_32,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_491,plain,(
    ! [A_189,B_190,C_191] :
      ( k1_relset_1(A_189,B_190,C_191) = k1_relat_1(C_191)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_495,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_491])).

tff(c_225,plain,(
    ! [A_134,B_135,C_136] :
      ( k1_relset_1(A_134,B_135,C_136) = k1_relat_1(C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_229,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_225])).

tff(c_48,plain,
    ( r2_hidden('#skF_8',k1_relset_1('#skF_5','#skF_6','#skF_7'))
    | m1_subset_1('#skF_9','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_55,plain,(
    m1_subset_1('#skF_9','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_44,plain,
    ( r2_hidden('#skF_8',k1_relset_1('#skF_5','#skF_6','#skF_7'))
    | r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_56,plain,(
    r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_8,plain,(
    ! [C_22,A_7,D_25] :
      ( r2_hidden(C_22,k1_relat_1(A_7))
      | ~ r2_hidden(k4_tarski(C_22,D_25),A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_60,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_56,c_8])).

tff(c_76,plain,(
    ! [A_97,B_98,C_99] :
      ( k1_relset_1(A_97,B_98,C_99) = k1_relat_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_80,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_76])).

tff(c_38,plain,(
    ! [E_84] :
      ( ~ r2_hidden(k4_tarski('#skF_8',E_84),'#skF_7')
      | ~ m1_subset_1(E_84,'#skF_6')
      | ~ r2_hidden('#skF_8',k1_relset_1('#skF_5','#skF_6','#skF_7')) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_186,plain,(
    ! [E_127] :
      ( ~ r2_hidden(k4_tarski('#skF_8',E_127),'#skF_7')
      | ~ m1_subset_1(E_127,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_80,c_38])).

tff(c_197,plain,(
    ~ m1_subset_1('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_186])).

tff(c_207,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_197])).

tff(c_208,plain,(
    r2_hidden('#skF_8',k1_relset_1('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_230,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_208])).

tff(c_49,plain,(
    ! [C_85,A_86,B_87] :
      ( v1_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_53,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_49])).

tff(c_281,plain,(
    ! [C_150,A_151] :
      ( r2_hidden(k4_tarski(C_150,'#skF_4'(A_151,k1_relat_1(A_151),C_150)),A_151)
      | ~ r2_hidden(C_150,k1_relat_1(A_151)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_20,plain,(
    ! [B_27,C_28,A_26] :
      ( r2_hidden(B_27,k11_relat_1(C_28,A_26))
      | ~ r2_hidden(k4_tarski(A_26,B_27),C_28)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_446,plain,(
    ! [A_179,C_180] :
      ( r2_hidden('#skF_4'(A_179,k1_relat_1(A_179),C_180),k11_relat_1(A_179,C_180))
      | ~ v1_relat_1(A_179)
      | ~ r2_hidden(C_180,k1_relat_1(A_179)) ) ),
    inference(resolution,[status(thm)],[c_281,c_20])).

tff(c_4,plain,(
    ! [A_4,B_6] :
      ( k9_relat_1(A_4,k1_tarski(B_6)) = k11_relat_1(A_4,B_6)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_354,plain,(
    ! [A_162,B_163,C_164,D_165] :
      ( k7_relset_1(A_162,B_163,C_164,D_165) = k9_relat_1(C_164,D_165)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_362,plain,(
    ! [D_166] : k7_relset_1('#skF_5','#skF_6','#skF_7',D_166) = k9_relat_1('#skF_7',D_166) ),
    inference(resolution,[status(thm)],[c_32,c_354])).

tff(c_24,plain,(
    ! [A_32,B_33,C_34,D_35] :
      ( m1_subset_1(k7_relset_1(A_32,B_33,C_34,D_35),k1_zfmisc_1(B_33))
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_368,plain,(
    ! [D_166] :
      ( m1_subset_1(k9_relat_1('#skF_7',D_166),k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_24])).

tff(c_376,plain,(
    ! [D_167] : m1_subset_1(k9_relat_1('#skF_7',D_167),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_368])).

tff(c_382,plain,(
    ! [B_6] :
      ( m1_subset_1(k11_relat_1('#skF_7',B_6),k1_zfmisc_1('#skF_6'))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_376])).

tff(c_387,plain,(
    ! [B_171] : m1_subset_1(k11_relat_1('#skF_7',B_171),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_382])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( m1_subset_1(A_1,C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_390,plain,(
    ! [A_1,B_171] :
      ( m1_subset_1(A_1,'#skF_6')
      | ~ r2_hidden(A_1,k11_relat_1('#skF_7',B_171)) ) ),
    inference(resolution,[status(thm)],[c_387,c_2])).

tff(c_450,plain,(
    ! [C_180] :
      ( m1_subset_1('#skF_4'('#skF_7',k1_relat_1('#skF_7'),C_180),'#skF_6')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(C_180,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_446,c_390])).

tff(c_464,plain,(
    ! [C_181] :
      ( m1_subset_1('#skF_4'('#skF_7',k1_relat_1('#skF_7'),C_181),'#skF_6')
      | ~ r2_hidden(C_181,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_450])).

tff(c_209,plain,(
    ~ r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,(
    ! [E_84] :
      ( ~ r2_hidden(k4_tarski('#skF_8',E_84),'#skF_7')
      | ~ m1_subset_1(E_84,'#skF_6')
      | r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_235,plain,(
    ! [E_84] :
      ( ~ r2_hidden(k4_tarski('#skF_8',E_84),'#skF_7')
      | ~ m1_subset_1(E_84,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_209,c_42])).

tff(c_295,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_7',k1_relat_1('#skF_7'),'#skF_8'),'#skF_6')
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_281,c_235])).

tff(c_304,plain,(
    ~ m1_subset_1('#skF_4'('#skF_7',k1_relat_1('#skF_7'),'#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_295])).

tff(c_467,plain,(
    ~ r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_464,c_304])).

tff(c_471,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_467])).

tff(c_472,plain,(
    r2_hidden('#skF_8',k1_relset_1('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_496,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_495,c_472])).

tff(c_529,plain,(
    ! [C_202,A_203] :
      ( r2_hidden(k4_tarski(C_202,'#skF_4'(A_203,k1_relat_1(A_203),C_202)),A_203)
      | ~ r2_hidden(C_202,k1_relat_1(A_203)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_703,plain,(
    ! [A_233,C_234] :
      ( r2_hidden('#skF_4'(A_233,k1_relat_1(A_233),C_234),k11_relat_1(A_233,C_234))
      | ~ v1_relat_1(A_233)
      | ~ r2_hidden(C_234,k1_relat_1(A_233)) ) ),
    inference(resolution,[status(thm)],[c_529,c_20])).

tff(c_612,plain,(
    ! [A_216,B_217,C_218,D_219] :
      ( k7_relset_1(A_216,B_217,C_218,D_219) = k9_relat_1(C_218,D_219)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(A_216,B_217))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_620,plain,(
    ! [D_220] : k7_relset_1('#skF_5','#skF_6','#skF_7',D_220) = k9_relat_1('#skF_7',D_220) ),
    inference(resolution,[status(thm)],[c_32,c_612])).

tff(c_626,plain,(
    ! [D_220] :
      ( m1_subset_1(k9_relat_1('#skF_7',D_220),k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_620,c_24])).

tff(c_634,plain,(
    ! [D_221] : m1_subset_1(k9_relat_1('#skF_7',D_221),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_626])).

tff(c_640,plain,(
    ! [B_6] :
      ( m1_subset_1(k11_relat_1('#skF_7',B_6),k1_zfmisc_1('#skF_6'))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_634])).

tff(c_644,plain,(
    ! [B_222] : m1_subset_1(k11_relat_1('#skF_7',B_222),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_640])).

tff(c_647,plain,(
    ! [A_1,B_222] :
      ( m1_subset_1(A_1,'#skF_6')
      | ~ r2_hidden(A_1,k11_relat_1('#skF_7',B_222)) ) ),
    inference(resolution,[status(thm)],[c_644,c_2])).

tff(c_707,plain,(
    ! [C_234] :
      ( m1_subset_1('#skF_4'('#skF_7',k1_relat_1('#skF_7'),C_234),'#skF_6')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(C_234,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_703,c_647])).

tff(c_721,plain,(
    ! [C_235] :
      ( m1_subset_1('#skF_4'('#skF_7',k1_relat_1('#skF_7'),C_235),'#skF_6')
      | ~ r2_hidden(C_235,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_707])).

tff(c_473,plain,(
    ~ m1_subset_1('#skF_9','#skF_6') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,(
    ! [E_84] :
      ( ~ r2_hidden(k4_tarski('#skF_8',E_84),'#skF_7')
      | ~ m1_subset_1(E_84,'#skF_6')
      | m1_subset_1('#skF_9','#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_487,plain,(
    ! [E_84] :
      ( ~ r2_hidden(k4_tarski('#skF_8',E_84),'#skF_7')
      | ~ m1_subset_1(E_84,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_473,c_46])).

tff(c_543,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_7',k1_relat_1('#skF_7'),'#skF_8'),'#skF_6')
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_529,c_487])).

tff(c_552,plain,(
    ~ m1_subset_1('#skF_4'('#skF_7',k1_relat_1('#skF_7'),'#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_496,c_543])).

tff(c_724,plain,(
    ~ r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_721,c_552])).

tff(c_728,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_496,c_724])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:55:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.47  
% 2.97/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.47  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k11_relat_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1
% 2.97/1.47  
% 2.97/1.47  %Foreground sorts:
% 2.97/1.47  
% 2.97/1.47  
% 2.97/1.47  %Background operators:
% 2.97/1.47  
% 2.97/1.47  
% 2.97/1.47  %Foreground operators:
% 2.97/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.97/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.97/1.47  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.97/1.47  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.97/1.47  tff('#skF_7', type, '#skF_7': $i).
% 2.97/1.47  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.97/1.47  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.97/1.47  tff('#skF_5', type, '#skF_5': $i).
% 2.97/1.47  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.97/1.47  tff('#skF_6', type, '#skF_6': $i).
% 2.97/1.47  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.97/1.47  tff('#skF_9', type, '#skF_9': $i).
% 2.97/1.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.97/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.97/1.47  tff('#skF_8', type, '#skF_8': $i).
% 2.97/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.97/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.97/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.97/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.97/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.97/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.97/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.97/1.47  
% 3.03/1.49  tff(f_87, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (![D]: (m1_subset_1(D, A) => (r2_hidden(D, k1_relset_1(A, B, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(D, E), C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relset_1)).
% 3.03/1.49  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.03/1.49  tff(f_44, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 3.03/1.49  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.03/1.49  tff(f_50, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 3.03/1.49  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 3.03/1.49  tff(f_66, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.03/1.49  tff(f_58, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 3.03/1.49  tff(f_31, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.03/1.49  tff(c_32, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.03/1.49  tff(c_491, plain, (![A_189, B_190, C_191]: (k1_relset_1(A_189, B_190, C_191)=k1_relat_1(C_191) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.03/1.49  tff(c_495, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_32, c_491])).
% 3.03/1.49  tff(c_225, plain, (![A_134, B_135, C_136]: (k1_relset_1(A_134, B_135, C_136)=k1_relat_1(C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.03/1.49  tff(c_229, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_32, c_225])).
% 3.03/1.49  tff(c_48, plain, (r2_hidden('#skF_8', k1_relset_1('#skF_5', '#skF_6', '#skF_7')) | m1_subset_1('#skF_9', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.03/1.49  tff(c_55, plain, (m1_subset_1('#skF_9', '#skF_6')), inference(splitLeft, [status(thm)], [c_48])).
% 3.03/1.49  tff(c_44, plain, (r2_hidden('#skF_8', k1_relset_1('#skF_5', '#skF_6', '#skF_7')) | r2_hidden(k4_tarski('#skF_8', '#skF_9'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.03/1.49  tff(c_56, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_9'), '#skF_7')), inference(splitLeft, [status(thm)], [c_44])).
% 3.03/1.49  tff(c_8, plain, (![C_22, A_7, D_25]: (r2_hidden(C_22, k1_relat_1(A_7)) | ~r2_hidden(k4_tarski(C_22, D_25), A_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.03/1.49  tff(c_60, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_56, c_8])).
% 3.03/1.49  tff(c_76, plain, (![A_97, B_98, C_99]: (k1_relset_1(A_97, B_98, C_99)=k1_relat_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.03/1.49  tff(c_80, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_32, c_76])).
% 3.03/1.49  tff(c_38, plain, (![E_84]: (~r2_hidden(k4_tarski('#skF_8', E_84), '#skF_7') | ~m1_subset_1(E_84, '#skF_6') | ~r2_hidden('#skF_8', k1_relset_1('#skF_5', '#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.03/1.49  tff(c_186, plain, (![E_127]: (~r2_hidden(k4_tarski('#skF_8', E_127), '#skF_7') | ~m1_subset_1(E_127, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_80, c_38])).
% 3.03/1.49  tff(c_197, plain, (~m1_subset_1('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_56, c_186])).
% 3.03/1.49  tff(c_207, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_197])).
% 3.03/1.49  tff(c_208, plain, (r2_hidden('#skF_8', k1_relset_1('#skF_5', '#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_44])).
% 3.03/1.49  tff(c_230, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_208])).
% 3.03/1.49  tff(c_49, plain, (![C_85, A_86, B_87]: (v1_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.03/1.49  tff(c_53, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_32, c_49])).
% 3.03/1.49  tff(c_281, plain, (![C_150, A_151]: (r2_hidden(k4_tarski(C_150, '#skF_4'(A_151, k1_relat_1(A_151), C_150)), A_151) | ~r2_hidden(C_150, k1_relat_1(A_151)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.03/1.49  tff(c_20, plain, (![B_27, C_28, A_26]: (r2_hidden(B_27, k11_relat_1(C_28, A_26)) | ~r2_hidden(k4_tarski(A_26, B_27), C_28) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.03/1.49  tff(c_446, plain, (![A_179, C_180]: (r2_hidden('#skF_4'(A_179, k1_relat_1(A_179), C_180), k11_relat_1(A_179, C_180)) | ~v1_relat_1(A_179) | ~r2_hidden(C_180, k1_relat_1(A_179)))), inference(resolution, [status(thm)], [c_281, c_20])).
% 3.03/1.49  tff(c_4, plain, (![A_4, B_6]: (k9_relat_1(A_4, k1_tarski(B_6))=k11_relat_1(A_4, B_6) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.03/1.49  tff(c_354, plain, (![A_162, B_163, C_164, D_165]: (k7_relset_1(A_162, B_163, C_164, D_165)=k9_relat_1(C_164, D_165) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.03/1.49  tff(c_362, plain, (![D_166]: (k7_relset_1('#skF_5', '#skF_6', '#skF_7', D_166)=k9_relat_1('#skF_7', D_166))), inference(resolution, [status(thm)], [c_32, c_354])).
% 3.03/1.49  tff(c_24, plain, (![A_32, B_33, C_34, D_35]: (m1_subset_1(k7_relset_1(A_32, B_33, C_34, D_35), k1_zfmisc_1(B_33)) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.03/1.49  tff(c_368, plain, (![D_166]: (m1_subset_1(k9_relat_1('#skF_7', D_166), k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_362, c_24])).
% 3.03/1.49  tff(c_376, plain, (![D_167]: (m1_subset_1(k9_relat_1('#skF_7', D_167), k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_368])).
% 3.03/1.49  tff(c_382, plain, (![B_6]: (m1_subset_1(k11_relat_1('#skF_7', B_6), k1_zfmisc_1('#skF_6')) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_376])).
% 3.03/1.49  tff(c_387, plain, (![B_171]: (m1_subset_1(k11_relat_1('#skF_7', B_171), k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_382])).
% 3.03/1.49  tff(c_2, plain, (![A_1, C_3, B_2]: (m1_subset_1(A_1, C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.03/1.49  tff(c_390, plain, (![A_1, B_171]: (m1_subset_1(A_1, '#skF_6') | ~r2_hidden(A_1, k11_relat_1('#skF_7', B_171)))), inference(resolution, [status(thm)], [c_387, c_2])).
% 3.03/1.49  tff(c_450, plain, (![C_180]: (m1_subset_1('#skF_4'('#skF_7', k1_relat_1('#skF_7'), C_180), '#skF_6') | ~v1_relat_1('#skF_7') | ~r2_hidden(C_180, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_446, c_390])).
% 3.03/1.49  tff(c_464, plain, (![C_181]: (m1_subset_1('#skF_4'('#skF_7', k1_relat_1('#skF_7'), C_181), '#skF_6') | ~r2_hidden(C_181, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_450])).
% 3.03/1.49  tff(c_209, plain, (~r2_hidden(k4_tarski('#skF_8', '#skF_9'), '#skF_7')), inference(splitRight, [status(thm)], [c_44])).
% 3.03/1.49  tff(c_42, plain, (![E_84]: (~r2_hidden(k4_tarski('#skF_8', E_84), '#skF_7') | ~m1_subset_1(E_84, '#skF_6') | r2_hidden(k4_tarski('#skF_8', '#skF_9'), '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.03/1.49  tff(c_235, plain, (![E_84]: (~r2_hidden(k4_tarski('#skF_8', E_84), '#skF_7') | ~m1_subset_1(E_84, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_209, c_42])).
% 3.03/1.49  tff(c_295, plain, (~m1_subset_1('#skF_4'('#skF_7', k1_relat_1('#skF_7'), '#skF_8'), '#skF_6') | ~r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_281, c_235])).
% 3.03/1.49  tff(c_304, plain, (~m1_subset_1('#skF_4'('#skF_7', k1_relat_1('#skF_7'), '#skF_8'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_230, c_295])).
% 3.03/1.49  tff(c_467, plain, (~r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_464, c_304])).
% 3.03/1.49  tff(c_471, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_230, c_467])).
% 3.03/1.49  tff(c_472, plain, (r2_hidden('#skF_8', k1_relset_1('#skF_5', '#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_48])).
% 3.03/1.49  tff(c_496, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_495, c_472])).
% 3.03/1.49  tff(c_529, plain, (![C_202, A_203]: (r2_hidden(k4_tarski(C_202, '#skF_4'(A_203, k1_relat_1(A_203), C_202)), A_203) | ~r2_hidden(C_202, k1_relat_1(A_203)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.03/1.49  tff(c_703, plain, (![A_233, C_234]: (r2_hidden('#skF_4'(A_233, k1_relat_1(A_233), C_234), k11_relat_1(A_233, C_234)) | ~v1_relat_1(A_233) | ~r2_hidden(C_234, k1_relat_1(A_233)))), inference(resolution, [status(thm)], [c_529, c_20])).
% 3.03/1.49  tff(c_612, plain, (![A_216, B_217, C_218, D_219]: (k7_relset_1(A_216, B_217, C_218, D_219)=k9_relat_1(C_218, D_219) | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(A_216, B_217))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.03/1.49  tff(c_620, plain, (![D_220]: (k7_relset_1('#skF_5', '#skF_6', '#skF_7', D_220)=k9_relat_1('#skF_7', D_220))), inference(resolution, [status(thm)], [c_32, c_612])).
% 3.03/1.49  tff(c_626, plain, (![D_220]: (m1_subset_1(k9_relat_1('#skF_7', D_220), k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_620, c_24])).
% 3.03/1.49  tff(c_634, plain, (![D_221]: (m1_subset_1(k9_relat_1('#skF_7', D_221), k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_626])).
% 3.03/1.49  tff(c_640, plain, (![B_6]: (m1_subset_1(k11_relat_1('#skF_7', B_6), k1_zfmisc_1('#skF_6')) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_634])).
% 3.03/1.49  tff(c_644, plain, (![B_222]: (m1_subset_1(k11_relat_1('#skF_7', B_222), k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_640])).
% 3.03/1.49  tff(c_647, plain, (![A_1, B_222]: (m1_subset_1(A_1, '#skF_6') | ~r2_hidden(A_1, k11_relat_1('#skF_7', B_222)))), inference(resolution, [status(thm)], [c_644, c_2])).
% 3.03/1.49  tff(c_707, plain, (![C_234]: (m1_subset_1('#skF_4'('#skF_7', k1_relat_1('#skF_7'), C_234), '#skF_6') | ~v1_relat_1('#skF_7') | ~r2_hidden(C_234, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_703, c_647])).
% 3.03/1.49  tff(c_721, plain, (![C_235]: (m1_subset_1('#skF_4'('#skF_7', k1_relat_1('#skF_7'), C_235), '#skF_6') | ~r2_hidden(C_235, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_707])).
% 3.03/1.49  tff(c_473, plain, (~m1_subset_1('#skF_9', '#skF_6')), inference(splitRight, [status(thm)], [c_48])).
% 3.03/1.49  tff(c_46, plain, (![E_84]: (~r2_hidden(k4_tarski('#skF_8', E_84), '#skF_7') | ~m1_subset_1(E_84, '#skF_6') | m1_subset_1('#skF_9', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.03/1.49  tff(c_487, plain, (![E_84]: (~r2_hidden(k4_tarski('#skF_8', E_84), '#skF_7') | ~m1_subset_1(E_84, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_473, c_46])).
% 3.03/1.49  tff(c_543, plain, (~m1_subset_1('#skF_4'('#skF_7', k1_relat_1('#skF_7'), '#skF_8'), '#skF_6') | ~r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_529, c_487])).
% 3.03/1.49  tff(c_552, plain, (~m1_subset_1('#skF_4'('#skF_7', k1_relat_1('#skF_7'), '#skF_8'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_496, c_543])).
% 3.03/1.49  tff(c_724, plain, (~r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_721, c_552])).
% 3.03/1.49  tff(c_728, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_496, c_724])).
% 3.03/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.49  
% 3.03/1.49  Inference rules
% 3.03/1.49  ----------------------
% 3.03/1.49  #Ref     : 0
% 3.03/1.49  #Sup     : 130
% 3.03/1.49  #Fact    : 0
% 3.03/1.49  #Define  : 0
% 3.03/1.49  #Split   : 3
% 3.03/1.49  #Chain   : 0
% 3.03/1.49  #Close   : 0
% 3.03/1.49  
% 3.03/1.49  Ordering : KBO
% 3.03/1.49  
% 3.03/1.49  Simplification rules
% 3.03/1.49  ----------------------
% 3.03/1.49  #Subsume      : 18
% 3.03/1.49  #Demod        : 37
% 3.03/1.49  #Tautology    : 30
% 3.03/1.49  #SimpNegUnit  : 2
% 3.03/1.49  #BackRed      : 2
% 3.03/1.49  
% 3.03/1.49  #Partial instantiations: 0
% 3.03/1.49  #Strategies tried      : 1
% 3.03/1.49  
% 3.03/1.49  Timing (in seconds)
% 3.03/1.49  ----------------------
% 3.03/1.50  Preprocessing        : 0.34
% 3.03/1.50  Parsing              : 0.18
% 3.03/1.50  CNF conversion       : 0.03
% 3.03/1.50  Main loop            : 0.32
% 3.03/1.50  Inferencing          : 0.13
% 3.03/1.50  Reduction            : 0.08
% 3.03/1.50  Demodulation         : 0.06
% 3.03/1.50  BG Simplification    : 0.02
% 3.03/1.50  Subsumption          : 0.06
% 3.03/1.50  Abstraction          : 0.02
% 3.03/1.50  MUC search           : 0.00
% 3.03/1.50  Cooper               : 0.00
% 3.03/1.50  Total                : 0.70
% 3.03/1.50  Index Insertion      : 0.00
% 3.03/1.50  Index Deletion       : 0.00
% 3.03/1.50  Index Matching       : 0.00
% 3.03/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
