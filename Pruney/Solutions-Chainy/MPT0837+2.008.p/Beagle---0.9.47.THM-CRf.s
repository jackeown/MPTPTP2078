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
% DateTime   : Thu Dec  3 10:08:06 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 257 expanded)
%              Number of leaves         :   37 ( 104 expanded)
%              Depth                    :   10
%              Number of atoms          :  129 ( 562 expanded)
%              Number of equality atoms :   14 (  58 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_11 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

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

tff(c_36,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_665,plain,(
    ! [A_204,B_205,C_206] :
      ( k2_relset_1(A_204,B_205,C_206) = k2_relat_1(C_206)
      | ~ m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1(A_204,B_205))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_669,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_665])).

tff(c_313,plain,(
    ! [A_140,B_141,C_142] :
      ( k2_relset_1(A_140,B_141,C_142) = k2_relat_1(C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_317,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_313])).

tff(c_52,plain,
    ( m1_subset_1('#skF_10','#skF_7')
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_64,plain,(
    r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_319,plain,(
    r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_64])).

tff(c_54,plain,(
    ! [C_85,A_86,B_87] :
      ( v1_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_58,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_54])).

tff(c_81,plain,(
    ! [C_96,A_97,B_98] :
      ( v4_relat_1(C_96,A_97)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_85,plain,(
    v4_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_81])).

tff(c_86,plain,(
    ! [B_99,A_100] :
      ( k7_relat_1(B_99,A_100) = B_99
      | ~ v4_relat_1(B_99,A_100)
      | ~ v1_relat_1(B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_89,plain,
    ( k7_relat_1('#skF_8','#skF_7') = '#skF_8'
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_85,c_86])).

tff(c_92,plain,(
    k7_relat_1('#skF_8','#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_89])).

tff(c_24,plain,(
    ! [B_29,A_28] :
      ( k2_relat_1(k7_relat_1(B_29,A_28)) = k9_relat_1(B_29,A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_96,plain,
    ( k9_relat_1('#skF_8','#skF_7') = k2_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_24])).

tff(c_100,plain,(
    k9_relat_1('#skF_8','#skF_7') = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_96])).

tff(c_329,plain,(
    ! [A_143,B_144,C_145] :
      ( r2_hidden('#skF_5'(A_143,B_144,C_145),B_144)
      | ~ r2_hidden(A_143,k9_relat_1(C_145,B_144))
      | ~ v1_relat_1(C_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_509,plain,(
    ! [A_174,B_175,C_176] :
      ( m1_subset_1('#skF_5'(A_174,B_175,C_176),B_175)
      | ~ r2_hidden(A_174,k9_relat_1(C_176,B_175))
      | ~ v1_relat_1(C_176) ) ),
    inference(resolution,[status(thm)],[c_329,c_2])).

tff(c_520,plain,(
    ! [A_174] :
      ( m1_subset_1('#skF_5'(A_174,'#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_174,k2_relat_1('#skF_8'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_509])).

tff(c_526,plain,(
    ! [A_177] :
      ( m1_subset_1('#skF_5'(A_177,'#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_177,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_520])).

tff(c_549,plain,(
    m1_subset_1('#skF_5'('#skF_11','#skF_7','#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_319,c_526])).

tff(c_556,plain,(
    ! [A_184,B_185,C_186] :
      ( r2_hidden(k4_tarski('#skF_5'(A_184,B_185,C_186),A_184),C_186)
      | ~ r2_hidden(A_184,k9_relat_1(C_186,B_185))
      | ~ v1_relat_1(C_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_362,plain,(
    ! [A_153,B_154,C_155] :
      ( m1_subset_1('#skF_5'(A_153,B_154,C_155),B_154)
      | ~ r2_hidden(A_153,k9_relat_1(C_155,B_154))
      | ~ v1_relat_1(C_155) ) ),
    inference(resolution,[status(thm)],[c_329,c_2])).

tff(c_373,plain,(
    ! [A_153] :
      ( m1_subset_1('#skF_5'(A_153,'#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_153,k2_relat_1('#skF_8'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_362])).

tff(c_379,plain,(
    ! [A_156] :
      ( m1_subset_1('#skF_5'(A_156,'#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_156,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_373])).

tff(c_398,plain,(
    m1_subset_1('#skF_5'('#skF_11','#skF_7','#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_319,c_379])).

tff(c_429,plain,(
    ! [A_165,B_166,C_167] :
      ( r2_hidden(k4_tarski('#skF_5'(A_165,B_166,C_167),A_165),C_167)
      | ~ r2_hidden(A_165,k9_relat_1(C_167,B_166))
      | ~ v1_relat_1(C_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_44,plain,(
    ! [E_82] :
      ( r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8')
      | ~ r2_hidden(k4_tarski(E_82,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_82,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_351,plain,(
    ! [E_82] :
      ( ~ r2_hidden(k4_tarski(E_82,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_82,'#skF_7') ) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_440,plain,(
    ! [B_166] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_166,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_166))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_429,c_351])).

tff(c_454,plain,(
    ! [B_168] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_168,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_168)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_440])).

tff(c_457,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_11','#skF_7','#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_454])).

tff(c_460,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_398,c_457])).

tff(c_461,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_6,plain,(
    ! [C_18,A_3,D_21] :
      ( r2_hidden(C_18,k2_relat_1(A_3))
      | ~ r2_hidden(k4_tarski(D_21,C_18),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_468,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_461,c_6])).

tff(c_42,plain,(
    ! [E_82] :
      ( ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8'))
      | ~ r2_hidden(k4_tarski(E_82,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_82,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_476,plain,(
    ! [E_82] :
      ( ~ r2_hidden(k4_tarski(E_82,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_82,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_317,c_42])).

tff(c_567,plain,(
    ! [B_185] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_185,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_185))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_556,c_476])).

tff(c_608,plain,(
    ! [B_193] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_193,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_193)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_567])).

tff(c_611,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_11','#skF_7','#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_608])).

tff(c_614,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_549,c_611])).

tff(c_616,plain,(
    ~ r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_674,plain,(
    ~ r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_669,c_616])).

tff(c_50,plain,
    ( r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8')
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_617,plain,(
    r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_618,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_616,c_617])).

tff(c_619,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_642,plain,(
    ! [C_199,A_200,D_201] :
      ( r2_hidden(C_199,k2_relat_1(A_200))
      | ~ r2_hidden(k4_tarski(D_201,C_199),A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_646,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_619,c_642])).

tff(c_48,plain,
    ( ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8'))
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_680,plain,(
    r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_669,c_646,c_669,c_48])).

tff(c_681,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_674,c_680])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:59:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.50  
% 2.88/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.51  %$ v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_11 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1
% 2.88/1.51  
% 2.88/1.51  %Foreground sorts:
% 2.88/1.51  
% 2.88/1.51  
% 2.88/1.51  %Background operators:
% 2.88/1.51  
% 2.88/1.51  
% 2.88/1.51  %Foreground operators:
% 2.88/1.51  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.88/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.88/1.51  tff('#skF_11', type, '#skF_11': $i).
% 2.88/1.51  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.88/1.51  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.88/1.51  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.88/1.51  tff('#skF_7', type, '#skF_7': $i).
% 2.88/1.51  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.88/1.51  tff('#skF_10', type, '#skF_10': $i).
% 2.88/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.88/1.51  tff('#skF_6', type, '#skF_6': $i).
% 2.88/1.51  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.88/1.51  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.88/1.51  tff('#skF_9', type, '#skF_9': $i).
% 2.88/1.51  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.88/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.88/1.51  tff('#skF_8', type, '#skF_8': $i).
% 2.88/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.88/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.88/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.51  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.88/1.51  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.88/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.88/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.88/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.88/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.88/1.51  
% 2.88/1.52  tff(f_91, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (![D]: (r2_hidden(D, k2_relset_1(B, A, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(E, D), C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relset_1)).
% 2.88/1.52  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.88/1.52  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.88/1.52  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.88/1.52  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.88/1.52  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.88/1.52  tff(f_48, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 2.88/1.52  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.88/1.52  tff(f_37, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 2.88/1.52  tff(c_36, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.88/1.52  tff(c_665, plain, (![A_204, B_205, C_206]: (k2_relset_1(A_204, B_205, C_206)=k2_relat_1(C_206) | ~m1_subset_1(C_206, k1_zfmisc_1(k2_zfmisc_1(A_204, B_205))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.88/1.52  tff(c_669, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_36, c_665])).
% 2.88/1.52  tff(c_313, plain, (![A_140, B_141, C_142]: (k2_relset_1(A_140, B_141, C_142)=k2_relat_1(C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.88/1.52  tff(c_317, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_36, c_313])).
% 2.88/1.52  tff(c_52, plain, (m1_subset_1('#skF_10', '#skF_7') | r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.88/1.52  tff(c_64, plain, (r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_52])).
% 2.88/1.52  tff(c_319, plain, (r2_hidden('#skF_11', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_317, c_64])).
% 2.88/1.52  tff(c_54, plain, (![C_85, A_86, B_87]: (v1_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.88/1.52  tff(c_58, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_36, c_54])).
% 2.88/1.52  tff(c_81, plain, (![C_96, A_97, B_98]: (v4_relat_1(C_96, A_97) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.88/1.52  tff(c_85, plain, (v4_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_36, c_81])).
% 2.88/1.52  tff(c_86, plain, (![B_99, A_100]: (k7_relat_1(B_99, A_100)=B_99 | ~v4_relat_1(B_99, A_100) | ~v1_relat_1(B_99))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.88/1.52  tff(c_89, plain, (k7_relat_1('#skF_8', '#skF_7')='#skF_8' | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_85, c_86])).
% 2.88/1.52  tff(c_92, plain, (k7_relat_1('#skF_8', '#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_89])).
% 2.88/1.52  tff(c_24, plain, (![B_29, A_28]: (k2_relat_1(k7_relat_1(B_29, A_28))=k9_relat_1(B_29, A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.88/1.52  tff(c_96, plain, (k9_relat_1('#skF_8', '#skF_7')=k2_relat_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_92, c_24])).
% 2.88/1.52  tff(c_100, plain, (k9_relat_1('#skF_8', '#skF_7')=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_96])).
% 2.88/1.52  tff(c_329, plain, (![A_143, B_144, C_145]: (r2_hidden('#skF_5'(A_143, B_144, C_145), B_144) | ~r2_hidden(A_143, k9_relat_1(C_145, B_144)) | ~v1_relat_1(C_145))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.88/1.52  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.88/1.52  tff(c_509, plain, (![A_174, B_175, C_176]: (m1_subset_1('#skF_5'(A_174, B_175, C_176), B_175) | ~r2_hidden(A_174, k9_relat_1(C_176, B_175)) | ~v1_relat_1(C_176))), inference(resolution, [status(thm)], [c_329, c_2])).
% 2.88/1.52  tff(c_520, plain, (![A_174]: (m1_subset_1('#skF_5'(A_174, '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_174, k2_relat_1('#skF_8')) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_100, c_509])).
% 2.88/1.52  tff(c_526, plain, (![A_177]: (m1_subset_1('#skF_5'(A_177, '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_177, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_520])).
% 2.88/1.52  tff(c_549, plain, (m1_subset_1('#skF_5'('#skF_11', '#skF_7', '#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_319, c_526])).
% 2.88/1.52  tff(c_556, plain, (![A_184, B_185, C_186]: (r2_hidden(k4_tarski('#skF_5'(A_184, B_185, C_186), A_184), C_186) | ~r2_hidden(A_184, k9_relat_1(C_186, B_185)) | ~v1_relat_1(C_186))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.88/1.52  tff(c_362, plain, (![A_153, B_154, C_155]: (m1_subset_1('#skF_5'(A_153, B_154, C_155), B_154) | ~r2_hidden(A_153, k9_relat_1(C_155, B_154)) | ~v1_relat_1(C_155))), inference(resolution, [status(thm)], [c_329, c_2])).
% 2.88/1.52  tff(c_373, plain, (![A_153]: (m1_subset_1('#skF_5'(A_153, '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_153, k2_relat_1('#skF_8')) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_100, c_362])).
% 2.88/1.52  tff(c_379, plain, (![A_156]: (m1_subset_1('#skF_5'(A_156, '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_156, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_373])).
% 2.88/1.52  tff(c_398, plain, (m1_subset_1('#skF_5'('#skF_11', '#skF_7', '#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_319, c_379])).
% 2.88/1.52  tff(c_429, plain, (![A_165, B_166, C_167]: (r2_hidden(k4_tarski('#skF_5'(A_165, B_166, C_167), A_165), C_167) | ~r2_hidden(A_165, k9_relat_1(C_167, B_166)) | ~v1_relat_1(C_167))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.88/1.52  tff(c_44, plain, (![E_82]: (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8') | ~r2_hidden(k4_tarski(E_82, '#skF_11'), '#skF_8') | ~m1_subset_1(E_82, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.88/1.52  tff(c_351, plain, (![E_82]: (~r2_hidden(k4_tarski(E_82, '#skF_11'), '#skF_8') | ~m1_subset_1(E_82, '#skF_7'))), inference(splitLeft, [status(thm)], [c_44])).
% 2.88/1.52  tff(c_440, plain, (![B_166]: (~m1_subset_1('#skF_5'('#skF_11', B_166, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_166)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_429, c_351])).
% 2.88/1.52  tff(c_454, plain, (![B_168]: (~m1_subset_1('#skF_5'('#skF_11', B_168, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_168)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_440])).
% 2.88/1.52  tff(c_457, plain, (~m1_subset_1('#skF_5'('#skF_11', '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k2_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_100, c_454])).
% 2.88/1.52  tff(c_460, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_319, c_398, c_457])).
% 2.88/1.52  tff(c_461, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_44])).
% 2.88/1.52  tff(c_6, plain, (![C_18, A_3, D_21]: (r2_hidden(C_18, k2_relat_1(A_3)) | ~r2_hidden(k4_tarski(D_21, C_18), A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.88/1.52  tff(c_468, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_461, c_6])).
% 2.88/1.52  tff(c_42, plain, (![E_82]: (~r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_6', '#skF_8')) | ~r2_hidden(k4_tarski(E_82, '#skF_11'), '#skF_8') | ~m1_subset_1(E_82, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.88/1.52  tff(c_476, plain, (![E_82]: (~r2_hidden(k4_tarski(E_82, '#skF_11'), '#skF_8') | ~m1_subset_1(E_82, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_468, c_317, c_42])).
% 2.88/1.52  tff(c_567, plain, (![B_185]: (~m1_subset_1('#skF_5'('#skF_11', B_185, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_185)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_556, c_476])).
% 2.88/1.52  tff(c_608, plain, (![B_193]: (~m1_subset_1('#skF_5'('#skF_11', B_193, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_193)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_567])).
% 2.88/1.52  tff(c_611, plain, (~m1_subset_1('#skF_5'('#skF_11', '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k2_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_100, c_608])).
% 2.88/1.52  tff(c_614, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_319, c_549, c_611])).
% 2.88/1.52  tff(c_616, plain, (~r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_52])).
% 2.88/1.52  tff(c_674, plain, (~r2_hidden('#skF_11', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_669, c_616])).
% 2.88/1.52  tff(c_50, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8') | r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.88/1.52  tff(c_617, plain, (r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_50])).
% 2.88/1.52  tff(c_618, plain, $false, inference(negUnitSimplification, [status(thm)], [c_616, c_617])).
% 2.88/1.52  tff(c_619, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_50])).
% 2.88/1.52  tff(c_642, plain, (![C_199, A_200, D_201]: (r2_hidden(C_199, k2_relat_1(A_200)) | ~r2_hidden(k4_tarski(D_201, C_199), A_200))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.88/1.52  tff(c_646, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_619, c_642])).
% 2.88/1.52  tff(c_48, plain, (~r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_6', '#skF_8')) | r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.88/1.52  tff(c_680, plain, (r2_hidden('#skF_11', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_669, c_646, c_669, c_48])).
% 2.88/1.52  tff(c_681, plain, $false, inference(negUnitSimplification, [status(thm)], [c_674, c_680])).
% 2.88/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.52  
% 2.88/1.52  Inference rules
% 2.88/1.52  ----------------------
% 2.88/1.52  #Ref     : 0
% 2.88/1.52  #Sup     : 129
% 2.88/1.52  #Fact    : 0
% 2.88/1.52  #Define  : 0
% 2.88/1.52  #Split   : 6
% 2.88/1.52  #Chain   : 0
% 2.88/1.52  #Close   : 0
% 2.88/1.52  
% 2.88/1.52  Ordering : KBO
% 2.88/1.52  
% 2.88/1.52  Simplification rules
% 2.88/1.52  ----------------------
% 2.88/1.52  #Subsume      : 4
% 2.88/1.52  #Demod        : 40
% 2.88/1.52  #Tautology    : 29
% 2.88/1.52  #SimpNegUnit  : 2
% 2.88/1.52  #BackRed      : 5
% 2.88/1.52  
% 2.88/1.52  #Partial instantiations: 0
% 2.88/1.52  #Strategies tried      : 1
% 2.88/1.52  
% 2.88/1.52  Timing (in seconds)
% 2.88/1.52  ----------------------
% 3.19/1.53  Preprocessing        : 0.35
% 3.19/1.53  Parsing              : 0.17
% 3.19/1.53  CNF conversion       : 0.03
% 3.19/1.53  Main loop            : 0.38
% 3.19/1.53  Inferencing          : 0.14
% 3.19/1.53  Reduction            : 0.10
% 3.19/1.53  Demodulation         : 0.07
% 3.19/1.53  BG Simplification    : 0.02
% 3.19/1.53  Subsumption          : 0.07
% 3.19/1.53  Abstraction          : 0.02
% 3.19/1.53  MUC search           : 0.00
% 3.19/1.53  Cooper               : 0.00
% 3.19/1.53  Total                : 0.77
% 3.19/1.53  Index Insertion      : 0.00
% 3.19/1.53  Index Deletion       : 0.00
% 3.19/1.53  Index Matching       : 0.00
% 3.19/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
