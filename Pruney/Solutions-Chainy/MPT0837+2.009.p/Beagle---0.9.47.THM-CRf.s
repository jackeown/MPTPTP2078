%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:06 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 272 expanded)
%              Number of leaves         :   33 ( 106 expanded)
%              Depth                    :   10
%              Number of atoms          :  139 ( 613 expanded)
%              Number of equality atoms :   13 (  59 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_91,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_490,plain,(
    ! [A_171,B_172,C_173] :
      ( k2_relset_1(A_171,B_172,C_173) = k2_relat_1(C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_494,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_490])).

tff(c_203,plain,(
    ! [A_115,B_116,C_117] :
      ( k2_relset_1(A_115,B_116,C_117) = k2_relat_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_207,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_203])).

tff(c_44,plain,
    ( m1_subset_1('#skF_6','#skF_3')
    | r2_hidden('#skF_7',k2_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_57,plain,(
    r2_hidden('#skF_7',k2_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_209,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_57])).

tff(c_46,plain,(
    ! [C_69,A_70,B_71] :
      ( v1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_50,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_46])).

tff(c_62,plain,(
    ! [C_77,A_78,B_79] :
      ( v4_relat_1(C_77,A_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_66,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_62])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( k7_relat_1(B_12,A_11) = B_12
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_69,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_14])).

tff(c_72,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_69])).

tff(c_77,plain,(
    ! [B_80,A_81] :
      ( k2_relat_1(k7_relat_1(B_80,A_81)) = k9_relat_1(B_80,A_81)
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_86,plain,
    ( k9_relat_1('#skF_4','#skF_3') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_77])).

tff(c_90,plain,(
    k9_relat_1('#skF_4','#skF_3') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_86])).

tff(c_339,plain,(
    ! [A_139,B_140,C_141] :
      ( r2_hidden('#skF_1'(A_139,B_140,C_141),B_140)
      | ~ r2_hidden(A_139,k9_relat_1(C_141,B_140))
      | ~ v1_relat_1(C_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_346,plain,(
    ! [A_143,B_144,C_145] :
      ( m1_subset_1('#skF_1'(A_143,B_144,C_145),B_144)
      | ~ r2_hidden(A_143,k9_relat_1(C_145,B_144))
      | ~ v1_relat_1(C_145) ) ),
    inference(resolution,[status(thm)],[c_339,c_2])).

tff(c_351,plain,(
    ! [A_143] :
      ( m1_subset_1('#skF_1'(A_143,'#skF_3','#skF_4'),'#skF_3')
      | ~ r2_hidden(A_143,k2_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_346])).

tff(c_355,plain,(
    ! [A_146] :
      ( m1_subset_1('#skF_1'(A_146,'#skF_3','#skF_4'),'#skF_3')
      | ~ r2_hidden(A_146,k2_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_351])).

tff(c_368,plain,(
    m1_subset_1('#skF_1'('#skF_7','#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_209,c_355])).

tff(c_375,plain,(
    ! [A_153,B_154,C_155] :
      ( r2_hidden(k4_tarski('#skF_1'(A_153,B_154,C_155),A_153),C_155)
      | ~ r2_hidden(A_153,k9_relat_1(C_155,B_154))
      | ~ v1_relat_1(C_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_34,plain,(
    ! [E_66] :
      ( ~ r2_hidden('#skF_5',k2_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ r2_hidden(k4_tarski(E_66,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(E_66,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_322,plain,(
    ! [E_66] :
      ( ~ r2_hidden('#skF_5',k2_relat_1('#skF_4'))
      | ~ r2_hidden(k4_tarski(E_66,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(E_66,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_34])).

tff(c_323,plain,(
    ~ r2_hidden('#skF_5',k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_322])).

tff(c_222,plain,(
    ! [A_119,B_120,C_121] :
      ( r2_hidden('#skF_1'(A_119,B_120,C_121),B_120)
      | ~ r2_hidden(A_119,k9_relat_1(C_121,B_120))
      | ~ v1_relat_1(C_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_228,plain,(
    ! [A_122,B_123,C_124] :
      ( m1_subset_1('#skF_1'(A_122,B_123,C_124),B_123)
      | ~ r2_hidden(A_122,k9_relat_1(C_124,B_123))
      | ~ v1_relat_1(C_124) ) ),
    inference(resolution,[status(thm)],[c_222,c_2])).

tff(c_233,plain,(
    ! [A_122] :
      ( m1_subset_1('#skF_1'(A_122,'#skF_3','#skF_4'),'#skF_3')
      | ~ r2_hidden(A_122,k2_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_228])).

tff(c_237,plain,(
    ! [A_125] :
      ( m1_subset_1('#skF_1'(A_125,'#skF_3','#skF_4'),'#skF_3')
      | ~ r2_hidden(A_125,k2_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_233])).

tff(c_246,plain,(
    m1_subset_1('#skF_1'('#skF_7','#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_209,c_237])).

tff(c_253,plain,(
    ! [A_132,B_133,C_134] :
      ( r2_hidden(k4_tarski('#skF_1'(A_132,B_133,C_134),A_132),C_134)
      | ~ r2_hidden(A_132,k9_relat_1(C_134,B_133))
      | ~ v1_relat_1(C_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_36,plain,(
    ! [E_66] :
      ( r2_hidden(k4_tarski('#skF_6','#skF_5'),'#skF_4')
      | ~ r2_hidden(k4_tarski(E_66,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(E_66,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_220,plain,(
    ! [E_66] :
      ( ~ r2_hidden(k4_tarski(E_66,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(E_66,'#skF_3') ) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_264,plain,(
    ! [B_133] :
      ( ~ m1_subset_1('#skF_1'('#skF_7',B_133,'#skF_4'),'#skF_3')
      | ~ r2_hidden('#skF_7',k9_relat_1('#skF_4',B_133))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_253,c_220])).

tff(c_298,plain,(
    ! [B_138] :
      ( ~ m1_subset_1('#skF_1'('#skF_7',B_138,'#skF_4'),'#skF_3')
      | ~ r2_hidden('#skF_7',k9_relat_1('#skF_4',B_138)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_264])).

tff(c_301,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_7','#skF_3','#skF_4'),'#skF_3')
    | ~ r2_hidden('#skF_7',k2_relat_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_298])).

tff(c_304,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_246,c_301])).

tff(c_305,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_16,plain,(
    ! [B_14,C_15,A_13] :
      ( r2_hidden(B_14,k2_relat_1(C_15))
      | ~ r2_hidden(k4_tarski(A_13,B_14),C_15)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_311,plain,
    ( r2_hidden('#skF_5',k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_305,c_16])).

tff(c_320,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_311])).

tff(c_328,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_323,c_320])).

tff(c_329,plain,(
    ! [E_66] :
      ( ~ r2_hidden(k4_tarski(E_66,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(E_66,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_322])).

tff(c_386,plain,(
    ! [B_154] :
      ( ~ m1_subset_1('#skF_1'('#skF_7',B_154,'#skF_4'),'#skF_3')
      | ~ r2_hidden('#skF_7',k9_relat_1('#skF_4',B_154))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_375,c_329])).

tff(c_420,plain,(
    ! [B_159] :
      ( ~ m1_subset_1('#skF_1'('#skF_7',B_159,'#skF_4'),'#skF_3')
      | ~ r2_hidden('#skF_7',k9_relat_1('#skF_4',B_159)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_386])).

tff(c_423,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_7','#skF_3','#skF_4'),'#skF_3')
    | ~ r2_hidden('#skF_7',k2_relat_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_420])).

tff(c_426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_368,c_423])).

tff(c_428,plain,(
    ~ r2_hidden('#skF_7',k2_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_495,plain,(
    ~ r2_hidden('#skF_7',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_428])).

tff(c_42,plain,
    ( r2_hidden(k4_tarski('#skF_6','#skF_5'),'#skF_4')
    | r2_hidden('#skF_7',k2_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_464,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_428,c_42])).

tff(c_467,plain,
    ( r2_hidden('#skF_5',k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_464,c_16])).

tff(c_473,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_467])).

tff(c_40,plain,
    ( ~ r2_hidden('#skF_5',k2_relset_1('#skF_3','#skF_2','#skF_4'))
    | r2_hidden('#skF_7',k2_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_501,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_473,c_494,c_40])).

tff(c_502,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_495,c_501])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:07:06 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.50  
% 2.72/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.50  %$ v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.72/1.50  
% 2.72/1.50  %Foreground sorts:
% 2.72/1.50  
% 2.72/1.50  
% 2.72/1.50  %Background operators:
% 2.72/1.50  
% 2.72/1.50  
% 2.72/1.50  %Foreground operators:
% 2.72/1.50  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.72/1.50  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.72/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.72/1.50  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.72/1.50  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.72/1.50  tff('#skF_7', type, '#skF_7': $i).
% 2.72/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.72/1.50  tff('#skF_5', type, '#skF_5': $i).
% 2.72/1.50  tff('#skF_6', type, '#skF_6': $i).
% 2.72/1.50  tff('#skF_2', type, '#skF_2': $i).
% 2.72/1.50  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.72/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.72/1.50  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.72/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.72/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.72/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.72/1.50  tff('#skF_4', type, '#skF_4': $i).
% 2.72/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.50  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.72/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.72/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.72/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.72/1.50  
% 2.88/1.52  tff(f_91, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (![D]: (r2_hidden(D, k2_relset_1(B, A, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(E, D), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relset_1)).
% 2.88/1.52  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.88/1.52  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.88/1.52  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.88/1.52  tff(f_50, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.88/1.52  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.88/1.52  tff(f_40, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 2.88/1.52  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.88/1.52  tff(f_58, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 2.88/1.52  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.88/1.52  tff(c_490, plain, (![A_171, B_172, C_173]: (k2_relset_1(A_171, B_172, C_173)=k2_relat_1(C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.88/1.52  tff(c_494, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_490])).
% 2.88/1.52  tff(c_203, plain, (![A_115, B_116, C_117]: (k2_relset_1(A_115, B_116, C_117)=k2_relat_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.88/1.52  tff(c_207, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_203])).
% 2.88/1.52  tff(c_44, plain, (m1_subset_1('#skF_6', '#skF_3') | r2_hidden('#skF_7', k2_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.88/1.52  tff(c_57, plain, (r2_hidden('#skF_7', k2_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_44])).
% 2.88/1.52  tff(c_209, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_207, c_57])).
% 2.88/1.52  tff(c_46, plain, (![C_69, A_70, B_71]: (v1_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.88/1.52  tff(c_50, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_46])).
% 2.88/1.52  tff(c_62, plain, (![C_77, A_78, B_79]: (v4_relat_1(C_77, A_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.88/1.52  tff(c_66, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_62])).
% 2.88/1.52  tff(c_14, plain, (![B_12, A_11]: (k7_relat_1(B_12, A_11)=B_12 | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.88/1.52  tff(c_69, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_14])).
% 2.88/1.52  tff(c_72, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_69])).
% 2.88/1.52  tff(c_77, plain, (![B_80, A_81]: (k2_relat_1(k7_relat_1(B_80, A_81))=k9_relat_1(B_80, A_81) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.88/1.52  tff(c_86, plain, (k9_relat_1('#skF_4', '#skF_3')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_72, c_77])).
% 2.88/1.52  tff(c_90, plain, (k9_relat_1('#skF_4', '#skF_3')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_86])).
% 2.88/1.52  tff(c_339, plain, (![A_139, B_140, C_141]: (r2_hidden('#skF_1'(A_139, B_140, C_141), B_140) | ~r2_hidden(A_139, k9_relat_1(C_141, B_140)) | ~v1_relat_1(C_141))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.88/1.52  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.88/1.52  tff(c_346, plain, (![A_143, B_144, C_145]: (m1_subset_1('#skF_1'(A_143, B_144, C_145), B_144) | ~r2_hidden(A_143, k9_relat_1(C_145, B_144)) | ~v1_relat_1(C_145))), inference(resolution, [status(thm)], [c_339, c_2])).
% 2.88/1.52  tff(c_351, plain, (![A_143]: (m1_subset_1('#skF_1'(A_143, '#skF_3', '#skF_4'), '#skF_3') | ~r2_hidden(A_143, k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_346])).
% 2.88/1.52  tff(c_355, plain, (![A_146]: (m1_subset_1('#skF_1'(A_146, '#skF_3', '#skF_4'), '#skF_3') | ~r2_hidden(A_146, k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_351])).
% 2.88/1.52  tff(c_368, plain, (m1_subset_1('#skF_1'('#skF_7', '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_209, c_355])).
% 2.88/1.52  tff(c_375, plain, (![A_153, B_154, C_155]: (r2_hidden(k4_tarski('#skF_1'(A_153, B_154, C_155), A_153), C_155) | ~r2_hidden(A_153, k9_relat_1(C_155, B_154)) | ~v1_relat_1(C_155))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.88/1.52  tff(c_34, plain, (![E_66]: (~r2_hidden('#skF_5', k2_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~r2_hidden(k4_tarski(E_66, '#skF_7'), '#skF_4') | ~m1_subset_1(E_66, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.88/1.52  tff(c_322, plain, (![E_66]: (~r2_hidden('#skF_5', k2_relat_1('#skF_4')) | ~r2_hidden(k4_tarski(E_66, '#skF_7'), '#skF_4') | ~m1_subset_1(E_66, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_207, c_34])).
% 2.88/1.52  tff(c_323, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_322])).
% 2.88/1.52  tff(c_222, plain, (![A_119, B_120, C_121]: (r2_hidden('#skF_1'(A_119, B_120, C_121), B_120) | ~r2_hidden(A_119, k9_relat_1(C_121, B_120)) | ~v1_relat_1(C_121))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.88/1.52  tff(c_228, plain, (![A_122, B_123, C_124]: (m1_subset_1('#skF_1'(A_122, B_123, C_124), B_123) | ~r2_hidden(A_122, k9_relat_1(C_124, B_123)) | ~v1_relat_1(C_124))), inference(resolution, [status(thm)], [c_222, c_2])).
% 2.88/1.52  tff(c_233, plain, (![A_122]: (m1_subset_1('#skF_1'(A_122, '#skF_3', '#skF_4'), '#skF_3') | ~r2_hidden(A_122, k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_228])).
% 2.88/1.52  tff(c_237, plain, (![A_125]: (m1_subset_1('#skF_1'(A_125, '#skF_3', '#skF_4'), '#skF_3') | ~r2_hidden(A_125, k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_233])).
% 2.88/1.52  tff(c_246, plain, (m1_subset_1('#skF_1'('#skF_7', '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_209, c_237])).
% 2.88/1.52  tff(c_253, plain, (![A_132, B_133, C_134]: (r2_hidden(k4_tarski('#skF_1'(A_132, B_133, C_134), A_132), C_134) | ~r2_hidden(A_132, k9_relat_1(C_134, B_133)) | ~v1_relat_1(C_134))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.88/1.52  tff(c_36, plain, (![E_66]: (r2_hidden(k4_tarski('#skF_6', '#skF_5'), '#skF_4') | ~r2_hidden(k4_tarski(E_66, '#skF_7'), '#skF_4') | ~m1_subset_1(E_66, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.88/1.52  tff(c_220, plain, (![E_66]: (~r2_hidden(k4_tarski(E_66, '#skF_7'), '#skF_4') | ~m1_subset_1(E_66, '#skF_3'))), inference(splitLeft, [status(thm)], [c_36])).
% 2.88/1.52  tff(c_264, plain, (![B_133]: (~m1_subset_1('#skF_1'('#skF_7', B_133, '#skF_4'), '#skF_3') | ~r2_hidden('#skF_7', k9_relat_1('#skF_4', B_133)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_253, c_220])).
% 2.88/1.52  tff(c_298, plain, (![B_138]: (~m1_subset_1('#skF_1'('#skF_7', B_138, '#skF_4'), '#skF_3') | ~r2_hidden('#skF_7', k9_relat_1('#skF_4', B_138)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_264])).
% 2.88/1.52  tff(c_301, plain, (~m1_subset_1('#skF_1'('#skF_7', '#skF_3', '#skF_4'), '#skF_3') | ~r2_hidden('#skF_7', k2_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_298])).
% 2.88/1.52  tff(c_304, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_209, c_246, c_301])).
% 2.88/1.52  tff(c_305, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_36])).
% 2.88/1.52  tff(c_16, plain, (![B_14, C_15, A_13]: (r2_hidden(B_14, k2_relat_1(C_15)) | ~r2_hidden(k4_tarski(A_13, B_14), C_15) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.88/1.52  tff(c_311, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_305, c_16])).
% 2.88/1.52  tff(c_320, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_311])).
% 2.88/1.52  tff(c_328, plain, $false, inference(negUnitSimplification, [status(thm)], [c_323, c_320])).
% 2.88/1.52  tff(c_329, plain, (![E_66]: (~r2_hidden(k4_tarski(E_66, '#skF_7'), '#skF_4') | ~m1_subset_1(E_66, '#skF_3'))), inference(splitRight, [status(thm)], [c_322])).
% 2.88/1.52  tff(c_386, plain, (![B_154]: (~m1_subset_1('#skF_1'('#skF_7', B_154, '#skF_4'), '#skF_3') | ~r2_hidden('#skF_7', k9_relat_1('#skF_4', B_154)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_375, c_329])).
% 2.88/1.52  tff(c_420, plain, (![B_159]: (~m1_subset_1('#skF_1'('#skF_7', B_159, '#skF_4'), '#skF_3') | ~r2_hidden('#skF_7', k9_relat_1('#skF_4', B_159)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_386])).
% 2.88/1.52  tff(c_423, plain, (~m1_subset_1('#skF_1'('#skF_7', '#skF_3', '#skF_4'), '#skF_3') | ~r2_hidden('#skF_7', k2_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_420])).
% 2.88/1.52  tff(c_426, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_209, c_368, c_423])).
% 2.88/1.52  tff(c_428, plain, (~r2_hidden('#skF_7', k2_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_44])).
% 2.88/1.52  tff(c_495, plain, (~r2_hidden('#skF_7', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_494, c_428])).
% 2.88/1.52  tff(c_42, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_5'), '#skF_4') | r2_hidden('#skF_7', k2_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.88/1.52  tff(c_464, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_428, c_42])).
% 2.88/1.52  tff(c_467, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_464, c_16])).
% 2.88/1.52  tff(c_473, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_467])).
% 2.88/1.52  tff(c_40, plain, (~r2_hidden('#skF_5', k2_relset_1('#skF_3', '#skF_2', '#skF_4')) | r2_hidden('#skF_7', k2_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.88/1.52  tff(c_501, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_494, c_473, c_494, c_40])).
% 2.88/1.52  tff(c_502, plain, $false, inference(negUnitSimplification, [status(thm)], [c_495, c_501])).
% 2.88/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.52  
% 2.88/1.52  Inference rules
% 2.88/1.52  ----------------------
% 2.88/1.52  #Ref     : 0
% 2.88/1.52  #Sup     : 92
% 2.88/1.52  #Fact    : 0
% 2.88/1.52  #Define  : 0
% 2.88/1.52  #Split   : 4
% 2.88/1.52  #Chain   : 0
% 2.88/1.52  #Close   : 0
% 2.88/1.52  
% 2.88/1.52  Ordering : KBO
% 2.88/1.52  
% 2.88/1.52  Simplification rules
% 2.88/1.52  ----------------------
% 2.88/1.52  #Subsume      : 6
% 2.88/1.52  #Demod        : 44
% 2.88/1.52  #Tautology    : 29
% 2.88/1.52  #SimpNegUnit  : 3
% 2.88/1.52  #BackRed      : 5
% 2.88/1.52  
% 2.88/1.52  #Partial instantiations: 0
% 2.88/1.52  #Strategies tried      : 1
% 2.88/1.52  
% 2.88/1.52  Timing (in seconds)
% 2.88/1.52  ----------------------
% 2.88/1.52  Preprocessing        : 0.37
% 2.88/1.52  Parsing              : 0.19
% 2.88/1.52  CNF conversion       : 0.03
% 2.88/1.52  Main loop            : 0.30
% 2.88/1.52  Inferencing          : 0.12
% 2.88/1.52  Reduction            : 0.08
% 2.88/1.52  Demodulation         : 0.06
% 2.88/1.52  BG Simplification    : 0.02
% 2.88/1.52  Subsumption          : 0.05
% 2.88/1.52  Abstraction          : 0.02
% 2.88/1.52  MUC search           : 0.00
% 2.88/1.52  Cooper               : 0.00
% 2.88/1.52  Total                : 0.71
% 2.88/1.52  Index Insertion      : 0.00
% 2.88/1.52  Index Deletion       : 0.00
% 2.88/1.52  Index Matching       : 0.00
% 2.88/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
