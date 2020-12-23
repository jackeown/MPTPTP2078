%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:08 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 240 expanded)
%              Number of leaves         :   36 (  96 expanded)
%              Depth                    :   11
%              Number of atoms          :  152 ( 525 expanded)
%              Number of equality atoms :   11 (  37 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_11 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1

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

tff(f_94,negated_conjecture,(
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

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_292,plain,(
    ! [A_134,B_135,C_136] :
      ( k2_relset_1(A_134,B_135,C_136) = k2_relat_1(C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_296,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_292])).

tff(c_52,plain,
    ( m1_subset_1('#skF_10','#skF_7')
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_70,plain,(
    r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_297,plain,(
    r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_70])).

tff(c_18,plain,(
    ! [A_26,B_27] : v1_relat_1(k2_zfmisc_1(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_63,plain,(
    ! [B_89,A_90] :
      ( v1_relat_1(B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_90))
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_66,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_36,c_63])).

tff(c_69,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_66])).

tff(c_28,plain,(
    ! [A_34] :
      ( k9_relat_1(A_34,k1_relat_1(A_34)) = k2_relat_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_569,plain,(
    ! [A_183,B_184,C_185] :
      ( r2_hidden('#skF_5'(A_183,B_184,C_185),k1_relat_1(C_185))
      | ~ r2_hidden(A_183,k9_relat_1(C_185,B_184))
      | ~ v1_relat_1(C_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_302,plain,(
    ! [A_137,B_138,C_139] :
      ( k1_relset_1(A_137,B_138,C_139) = k1_relat_1(C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_306,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_302])).

tff(c_498,plain,(
    ! [A_172,B_173,C_174] :
      ( m1_subset_1(k1_relset_1(A_172,B_173,C_174),k1_zfmisc_1(A_172))
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_514,plain,
    ( m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_498])).

tff(c_520,plain,(
    m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_514])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( m1_subset_1(A_1,C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_526,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,'#skF_7')
      | ~ r2_hidden(A_1,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_520,c_2])).

tff(c_573,plain,(
    ! [A_183,B_184] :
      ( m1_subset_1('#skF_5'(A_183,B_184,'#skF_8'),'#skF_7')
      | ~ r2_hidden(A_183,k9_relat_1('#skF_8',B_184))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_569,c_526])).

tff(c_577,plain,(
    ! [A_186,B_187] :
      ( m1_subset_1('#skF_5'(A_186,B_187,'#skF_8'),'#skF_7')
      | ~ r2_hidden(A_186,k9_relat_1('#skF_8',B_187)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_573])).

tff(c_593,plain,(
    ! [A_186] :
      ( m1_subset_1('#skF_5'(A_186,k1_relat_1('#skF_8'),'#skF_8'),'#skF_7')
      | ~ r2_hidden(A_186,k2_relat_1('#skF_8'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_577])).

tff(c_598,plain,(
    ! [A_186] :
      ( m1_subset_1('#skF_5'(A_186,k1_relat_1('#skF_8'),'#skF_8'),'#skF_7')
      | ~ r2_hidden(A_186,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_593])).

tff(c_600,plain,(
    ! [A_189,B_190,C_191] :
      ( r2_hidden(k4_tarski('#skF_5'(A_189,B_190,C_191),A_189),C_191)
      | ~ r2_hidden(A_189,k9_relat_1(C_191,B_190))
      | ~ v1_relat_1(C_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_42,plain,(
    ! [E_85] :
      ( ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8'))
      | ~ r2_hidden(k4_tarski(E_85,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_85,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_480,plain,(
    ! [E_85] :
      ( ~ r2_hidden('#skF_9',k2_relat_1('#skF_8'))
      | ~ r2_hidden(k4_tarski(E_85,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_85,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_42])).

tff(c_481,plain,(
    ~ r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_480])).

tff(c_388,plain,(
    ! [A_155,B_156,C_157] :
      ( r2_hidden('#skF_5'(A_155,B_156,C_157),k1_relat_1(C_157))
      | ~ r2_hidden(A_155,k9_relat_1(C_157,B_156))
      | ~ v1_relat_1(C_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_330,plain,(
    ! [A_148,B_149,C_150] :
      ( m1_subset_1(k1_relset_1(A_148,B_149,C_150),k1_zfmisc_1(A_148))
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_346,plain,
    ( m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_330])).

tff(c_352,plain,(
    m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_346])).

tff(c_358,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,'#skF_7')
      | ~ r2_hidden(A_1,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_352,c_2])).

tff(c_392,plain,(
    ! [A_155,B_156] :
      ( m1_subset_1('#skF_5'(A_155,B_156,'#skF_8'),'#skF_7')
      | ~ r2_hidden(A_155,k9_relat_1('#skF_8',B_156))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_388,c_358])).

tff(c_396,plain,(
    ! [A_158,B_159] :
      ( m1_subset_1('#skF_5'(A_158,B_159,'#skF_8'),'#skF_7')
      | ~ r2_hidden(A_158,k9_relat_1('#skF_8',B_159)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_392])).

tff(c_412,plain,(
    ! [A_158] :
      ( m1_subset_1('#skF_5'(A_158,k1_relat_1('#skF_8'),'#skF_8'),'#skF_7')
      | ~ r2_hidden(A_158,k2_relat_1('#skF_8'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_396])).

tff(c_417,plain,(
    ! [A_158] :
      ( m1_subset_1('#skF_5'(A_158,k1_relat_1('#skF_8'),'#skF_8'),'#skF_7')
      | ~ r2_hidden(A_158,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_412])).

tff(c_419,plain,(
    ! [A_161,B_162,C_163] :
      ( r2_hidden(k4_tarski('#skF_5'(A_161,B_162,C_163),A_161),C_163)
      | ~ r2_hidden(A_161,k9_relat_1(C_163,B_162))
      | ~ v1_relat_1(C_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_44,plain,(
    ! [E_85] :
      ( r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8')
      | ~ r2_hidden(k4_tarski(E_85,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_85,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_312,plain,(
    ! [E_85] :
      ( ~ r2_hidden(k4_tarski(E_85,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_85,'#skF_7') ) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_431,plain,(
    ! [B_162] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_162,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_162))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_419,c_312])).

tff(c_465,plain,(
    ! [B_167] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_167,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_167)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_431])).

tff(c_469,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_11',k1_relat_1('#skF_8'),'#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_11',k2_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_465])).

tff(c_471,plain,(
    ~ m1_subset_1('#skF_5'('#skF_11',k1_relat_1('#skF_8'),'#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_297,c_469])).

tff(c_474,plain,(
    ~ r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_417,c_471])).

tff(c_478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_474])).

tff(c_479,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_8,plain,(
    ! [C_22,A_7,D_25] :
      ( r2_hidden(C_22,k2_relat_1(A_7))
      | ~ r2_hidden(k4_tarski(D_25,C_22),A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_484,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_479,c_8])).

tff(c_488,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_481,c_484])).

tff(c_489,plain,(
    ! [E_85] :
      ( ~ r2_hidden(k4_tarski(E_85,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_85,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_480])).

tff(c_612,plain,(
    ! [B_190] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_190,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_190))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_600,c_489])).

tff(c_622,plain,(
    ! [B_192] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_192,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_192)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_612])).

tff(c_626,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_11',k1_relat_1('#skF_8'),'#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_11',k2_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_622])).

tff(c_628,plain,(
    ~ m1_subset_1('#skF_5'('#skF_11',k1_relat_1('#skF_8'),'#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_297,c_626])).

tff(c_631,plain,(
    ~ r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_598,c_628])).

tff(c_635,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_631])).

tff(c_637,plain,(
    ~ r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,
    ( r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8')
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_643,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_637,c_50])).

tff(c_647,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_643,c_8])).

tff(c_651,plain,(
    ! [A_200,B_201,C_202] :
      ( k2_relset_1(A_200,B_201,C_202) = k2_relat_1(C_202)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_655,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_651])).

tff(c_48,plain,
    ( ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8'))
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_650,plain,(
    ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_637,c_48])).

tff(c_656,plain,(
    ~ r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_655,c_650])).

tff(c_660,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_647,c_656])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n003.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 16:03:57 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.43  
% 2.79/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.43  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_11 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1
% 2.79/1.43  
% 2.79/1.43  %Foreground sorts:
% 2.79/1.43  
% 2.79/1.43  
% 2.79/1.43  %Background operators:
% 2.79/1.43  
% 2.79/1.43  
% 2.79/1.43  %Foreground operators:
% 2.79/1.43  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.79/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.79/1.43  tff('#skF_11', type, '#skF_11': $i).
% 2.79/1.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.79/1.43  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.79/1.43  tff('#skF_7', type, '#skF_7': $i).
% 2.79/1.43  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.79/1.43  tff('#skF_10', type, '#skF_10': $i).
% 2.79/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.79/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.79/1.43  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.79/1.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.79/1.43  tff('#skF_9', type, '#skF_9': $i).
% 2.79/1.43  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.79/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.79/1.43  tff('#skF_8', type, '#skF_8': $i).
% 2.79/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.79/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.79/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.79/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.79/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.79/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.79/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.79/1.43  
% 2.79/1.45  tff(f_94, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (![D]: (r2_hidden(D, k2_relset_1(B, A, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(E, D), C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relset_1)).
% 2.79/1.45  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.79/1.45  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.79/1.45  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.79/1.45  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.79/1.45  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 2.79/1.45  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.79/1.45  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.79/1.45  tff(f_31, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.79/1.45  tff(f_46, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 2.79/1.45  tff(c_36, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.79/1.45  tff(c_292, plain, (![A_134, B_135, C_136]: (k2_relset_1(A_134, B_135, C_136)=k2_relat_1(C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.79/1.45  tff(c_296, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_36, c_292])).
% 2.79/1.45  tff(c_52, plain, (m1_subset_1('#skF_10', '#skF_7') | r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.79/1.45  tff(c_70, plain, (r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_52])).
% 2.79/1.45  tff(c_297, plain, (r2_hidden('#skF_11', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_296, c_70])).
% 2.79/1.45  tff(c_18, plain, (![A_26, B_27]: (v1_relat_1(k2_zfmisc_1(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.79/1.45  tff(c_63, plain, (![B_89, A_90]: (v1_relat_1(B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(A_90)) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.79/1.45  tff(c_66, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_36, c_63])).
% 2.79/1.45  tff(c_69, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_66])).
% 2.79/1.45  tff(c_28, plain, (![A_34]: (k9_relat_1(A_34, k1_relat_1(A_34))=k2_relat_1(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.79/1.45  tff(c_569, plain, (![A_183, B_184, C_185]: (r2_hidden('#skF_5'(A_183, B_184, C_185), k1_relat_1(C_185)) | ~r2_hidden(A_183, k9_relat_1(C_185, B_184)) | ~v1_relat_1(C_185))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.79/1.45  tff(c_302, plain, (![A_137, B_138, C_139]: (k1_relset_1(A_137, B_138, C_139)=k1_relat_1(C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.79/1.45  tff(c_306, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_36, c_302])).
% 2.79/1.45  tff(c_498, plain, (![A_172, B_173, C_174]: (m1_subset_1(k1_relset_1(A_172, B_173, C_174), k1_zfmisc_1(A_172)) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_172, B_173))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.79/1.45  tff(c_514, plain, (m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_306, c_498])).
% 2.79/1.45  tff(c_520, plain, (m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_514])).
% 2.79/1.45  tff(c_2, plain, (![A_1, C_3, B_2]: (m1_subset_1(A_1, C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.79/1.45  tff(c_526, plain, (![A_1]: (m1_subset_1(A_1, '#skF_7') | ~r2_hidden(A_1, k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_520, c_2])).
% 2.79/1.45  tff(c_573, plain, (![A_183, B_184]: (m1_subset_1('#skF_5'(A_183, B_184, '#skF_8'), '#skF_7') | ~r2_hidden(A_183, k9_relat_1('#skF_8', B_184)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_569, c_526])).
% 2.79/1.45  tff(c_577, plain, (![A_186, B_187]: (m1_subset_1('#skF_5'(A_186, B_187, '#skF_8'), '#skF_7') | ~r2_hidden(A_186, k9_relat_1('#skF_8', B_187)))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_573])).
% 2.79/1.45  tff(c_593, plain, (![A_186]: (m1_subset_1('#skF_5'(A_186, k1_relat_1('#skF_8'), '#skF_8'), '#skF_7') | ~r2_hidden(A_186, k2_relat_1('#skF_8')) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_577])).
% 2.79/1.45  tff(c_598, plain, (![A_186]: (m1_subset_1('#skF_5'(A_186, k1_relat_1('#skF_8'), '#skF_8'), '#skF_7') | ~r2_hidden(A_186, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_593])).
% 2.79/1.45  tff(c_600, plain, (![A_189, B_190, C_191]: (r2_hidden(k4_tarski('#skF_5'(A_189, B_190, C_191), A_189), C_191) | ~r2_hidden(A_189, k9_relat_1(C_191, B_190)) | ~v1_relat_1(C_191))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.79/1.45  tff(c_42, plain, (![E_85]: (~r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_6', '#skF_8')) | ~r2_hidden(k4_tarski(E_85, '#skF_11'), '#skF_8') | ~m1_subset_1(E_85, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.79/1.45  tff(c_480, plain, (![E_85]: (~r2_hidden('#skF_9', k2_relat_1('#skF_8')) | ~r2_hidden(k4_tarski(E_85, '#skF_11'), '#skF_8') | ~m1_subset_1(E_85, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_296, c_42])).
% 2.79/1.45  tff(c_481, plain, (~r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_480])).
% 2.79/1.45  tff(c_388, plain, (![A_155, B_156, C_157]: (r2_hidden('#skF_5'(A_155, B_156, C_157), k1_relat_1(C_157)) | ~r2_hidden(A_155, k9_relat_1(C_157, B_156)) | ~v1_relat_1(C_157))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.79/1.45  tff(c_330, plain, (![A_148, B_149, C_150]: (m1_subset_1(k1_relset_1(A_148, B_149, C_150), k1_zfmisc_1(A_148)) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.79/1.45  tff(c_346, plain, (m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_306, c_330])).
% 2.79/1.45  tff(c_352, plain, (m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_346])).
% 2.79/1.45  tff(c_358, plain, (![A_1]: (m1_subset_1(A_1, '#skF_7') | ~r2_hidden(A_1, k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_352, c_2])).
% 2.79/1.45  tff(c_392, plain, (![A_155, B_156]: (m1_subset_1('#skF_5'(A_155, B_156, '#skF_8'), '#skF_7') | ~r2_hidden(A_155, k9_relat_1('#skF_8', B_156)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_388, c_358])).
% 2.79/1.45  tff(c_396, plain, (![A_158, B_159]: (m1_subset_1('#skF_5'(A_158, B_159, '#skF_8'), '#skF_7') | ~r2_hidden(A_158, k9_relat_1('#skF_8', B_159)))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_392])).
% 2.79/1.45  tff(c_412, plain, (![A_158]: (m1_subset_1('#skF_5'(A_158, k1_relat_1('#skF_8'), '#skF_8'), '#skF_7') | ~r2_hidden(A_158, k2_relat_1('#skF_8')) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_396])).
% 2.79/1.45  tff(c_417, plain, (![A_158]: (m1_subset_1('#skF_5'(A_158, k1_relat_1('#skF_8'), '#skF_8'), '#skF_7') | ~r2_hidden(A_158, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_412])).
% 2.79/1.45  tff(c_419, plain, (![A_161, B_162, C_163]: (r2_hidden(k4_tarski('#skF_5'(A_161, B_162, C_163), A_161), C_163) | ~r2_hidden(A_161, k9_relat_1(C_163, B_162)) | ~v1_relat_1(C_163))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.79/1.45  tff(c_44, plain, (![E_85]: (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8') | ~r2_hidden(k4_tarski(E_85, '#skF_11'), '#skF_8') | ~m1_subset_1(E_85, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.79/1.45  tff(c_312, plain, (![E_85]: (~r2_hidden(k4_tarski(E_85, '#skF_11'), '#skF_8') | ~m1_subset_1(E_85, '#skF_7'))), inference(splitLeft, [status(thm)], [c_44])).
% 2.79/1.45  tff(c_431, plain, (![B_162]: (~m1_subset_1('#skF_5'('#skF_11', B_162, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_162)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_419, c_312])).
% 2.79/1.45  tff(c_465, plain, (![B_167]: (~m1_subset_1('#skF_5'('#skF_11', B_167, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_167)))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_431])).
% 2.79/1.45  tff(c_469, plain, (~m1_subset_1('#skF_5'('#skF_11', k1_relat_1('#skF_8'), '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k2_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_28, c_465])).
% 2.79/1.45  tff(c_471, plain, (~m1_subset_1('#skF_5'('#skF_11', k1_relat_1('#skF_8'), '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_297, c_469])).
% 2.79/1.45  tff(c_474, plain, (~r2_hidden('#skF_11', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_417, c_471])).
% 2.79/1.45  tff(c_478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_297, c_474])).
% 2.79/1.45  tff(c_479, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_44])).
% 2.79/1.45  tff(c_8, plain, (![C_22, A_7, D_25]: (r2_hidden(C_22, k2_relat_1(A_7)) | ~r2_hidden(k4_tarski(D_25, C_22), A_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.79/1.45  tff(c_484, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_479, c_8])).
% 2.79/1.45  tff(c_488, plain, $false, inference(negUnitSimplification, [status(thm)], [c_481, c_484])).
% 2.79/1.45  tff(c_489, plain, (![E_85]: (~r2_hidden(k4_tarski(E_85, '#skF_11'), '#skF_8') | ~m1_subset_1(E_85, '#skF_7'))), inference(splitRight, [status(thm)], [c_480])).
% 2.79/1.45  tff(c_612, plain, (![B_190]: (~m1_subset_1('#skF_5'('#skF_11', B_190, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_190)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_600, c_489])).
% 2.79/1.45  tff(c_622, plain, (![B_192]: (~m1_subset_1('#skF_5'('#skF_11', B_192, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_192)))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_612])).
% 2.79/1.45  tff(c_626, plain, (~m1_subset_1('#skF_5'('#skF_11', k1_relat_1('#skF_8'), '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k2_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_28, c_622])).
% 2.79/1.45  tff(c_628, plain, (~m1_subset_1('#skF_5'('#skF_11', k1_relat_1('#skF_8'), '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_297, c_626])).
% 2.79/1.45  tff(c_631, plain, (~r2_hidden('#skF_11', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_598, c_628])).
% 2.79/1.45  tff(c_635, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_297, c_631])).
% 2.79/1.45  tff(c_637, plain, (~r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_52])).
% 2.79/1.45  tff(c_50, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8') | r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.79/1.45  tff(c_643, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_637, c_50])).
% 2.79/1.45  tff(c_647, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_643, c_8])).
% 2.79/1.45  tff(c_651, plain, (![A_200, B_201, C_202]: (k2_relset_1(A_200, B_201, C_202)=k2_relat_1(C_202) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.79/1.45  tff(c_655, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_36, c_651])).
% 2.79/1.45  tff(c_48, plain, (~r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_6', '#skF_8')) | r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.79/1.45  tff(c_650, plain, (~r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_637, c_48])).
% 2.79/1.45  tff(c_656, plain, (~r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_655, c_650])).
% 2.79/1.45  tff(c_660, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_647, c_656])).
% 2.79/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.45  
% 2.79/1.45  Inference rules
% 2.79/1.45  ----------------------
% 2.79/1.45  #Ref     : 0
% 2.79/1.45  #Sup     : 111
% 2.79/1.45  #Fact    : 0
% 2.79/1.45  #Define  : 0
% 2.79/1.45  #Split   : 8
% 2.79/1.45  #Chain   : 0
% 2.79/1.45  #Close   : 0
% 2.79/1.45  
% 2.79/1.45  Ordering : KBO
% 2.79/1.45  
% 2.79/1.45  Simplification rules
% 2.79/1.45  ----------------------
% 2.79/1.45  #Subsume      : 5
% 2.79/1.45  #Demod        : 47
% 2.79/1.45  #Tautology    : 20
% 2.79/1.45  #SimpNegUnit  : 3
% 2.79/1.45  #BackRed      : 4
% 2.79/1.45  
% 2.79/1.45  #Partial instantiations: 0
% 2.79/1.45  #Strategies tried      : 1
% 2.79/1.45  
% 2.79/1.45  Timing (in seconds)
% 2.79/1.45  ----------------------
% 2.79/1.45  Preprocessing        : 0.32
% 2.79/1.45  Parsing              : 0.16
% 2.79/1.45  CNF conversion       : 0.03
% 2.79/1.45  Main loop            : 0.34
% 2.79/1.45  Inferencing          : 0.13
% 2.79/1.45  Reduction            : 0.10
% 2.79/1.45  Demodulation         : 0.07
% 2.79/1.45  BG Simplification    : 0.02
% 2.79/1.45  Subsumption          : 0.06
% 2.79/1.45  Abstraction          : 0.02
% 2.79/1.45  MUC search           : 0.00
% 2.79/1.45  Cooper               : 0.00
% 2.79/1.45  Total                : 0.70
% 2.79/1.45  Index Insertion      : 0.00
% 2.79/1.45  Index Deletion       : 0.00
% 2.79/1.45  Index Matching       : 0.00
% 2.79/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
