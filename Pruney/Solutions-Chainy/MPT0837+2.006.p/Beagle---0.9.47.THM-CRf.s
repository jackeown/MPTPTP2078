%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:06 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 289 expanded)
%              Number of leaves         :   36 ( 111 expanded)
%              Depth                    :   11
%              Number of atoms          :  177 ( 665 expanded)
%              Number of equality atoms :   13 (  53 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_103,negated_conjecture,(
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

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_52,axiom,(
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
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_63,plain,(
    ! [C_76,A_77,B_78] :
      ( v1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_72,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_63])).

tff(c_81,plain,(
    ! [C_84,A_85,B_86] :
      ( v4_relat_1(C_84,A_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_90,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_81])).

tff(c_481,plain,(
    ! [A_195,B_196,C_197] :
      ( k2_relset_1(A_195,B_196,C_197) = k2_relat_1(C_197)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_195,B_196))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_490,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_481])).

tff(c_52,plain,
    ( m1_subset_1('#skF_6','#skF_3')
    | r2_hidden('#skF_7',k2_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_79,plain,(
    r2_hidden('#skF_7',k2_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_492,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_79])).

tff(c_97,plain,(
    ! [B_90,A_91] :
      ( k7_relat_1(B_90,A_91) = B_90
      | ~ v4_relat_1(B_90,A_91)
      | ~ v1_relat_1(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_100,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_97])).

tff(c_103,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_100])).

tff(c_125,plain,(
    ! [B_98,A_99] :
      ( k2_relat_1(k7_relat_1(B_98,A_99)) = k9_relat_1(B_98,A_99)
      | ~ v1_relat_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_134,plain,
    ( k9_relat_1('#skF_4','#skF_3') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_125])).

tff(c_138,plain,(
    k9_relat_1('#skF_4','#skF_3') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_134])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_823,plain,(
    ! [A_258,B_259,C_260] :
      ( r2_hidden('#skF_1'(A_258,B_259,C_260),k1_relat_1(C_260))
      | ~ r2_hidden(A_258,k9_relat_1(C_260,B_259))
      | ~ v1_relat_1(C_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_163,plain,(
    ! [A_102,C_103,B_104] :
      ( m1_subset_1(A_102,C_103)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(C_103))
      | ~ r2_hidden(A_102,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_168,plain,(
    ! [A_102,B_2,A_1] :
      ( m1_subset_1(A_102,B_2)
      | ~ r2_hidden(A_102,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_163])).

tff(c_1187,plain,(
    ! [A_320,B_321,C_322,B_323] :
      ( m1_subset_1('#skF_1'(A_320,B_321,C_322),B_323)
      | ~ r1_tarski(k1_relat_1(C_322),B_323)
      | ~ r2_hidden(A_320,k9_relat_1(C_322,B_321))
      | ~ v1_relat_1(C_322) ) ),
    inference(resolution,[status(thm)],[c_823,c_168])).

tff(c_1191,plain,(
    ! [A_324,B_325,B_326,A_327] :
      ( m1_subset_1('#skF_1'(A_324,B_325,B_326),A_327)
      | ~ r2_hidden(A_324,k9_relat_1(B_326,B_325))
      | ~ v4_relat_1(B_326,A_327)
      | ~ v1_relat_1(B_326) ) ),
    inference(resolution,[status(thm)],[c_10,c_1187])).

tff(c_1201,plain,(
    ! [A_324,A_327] :
      ( m1_subset_1('#skF_1'(A_324,'#skF_3','#skF_4'),A_327)
      | ~ r2_hidden(A_324,k2_relat_1('#skF_4'))
      | ~ v4_relat_1('#skF_4',A_327)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_1191])).

tff(c_1261,plain,(
    ! [A_330,A_331] :
      ( m1_subset_1('#skF_1'(A_330,'#skF_3','#skF_4'),A_331)
      | ~ r2_hidden(A_330,k2_relat_1('#skF_4'))
      | ~ v4_relat_1('#skF_4',A_331) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1201])).

tff(c_1306,plain,(
    ! [A_333] :
      ( m1_subset_1('#skF_1'('#skF_7','#skF_3','#skF_4'),A_333)
      | ~ v4_relat_1('#skF_4',A_333) ) ),
    inference(resolution,[status(thm)],[c_492,c_1261])).

tff(c_896,plain,(
    ! [A_269,B_270,C_271] :
      ( r2_hidden(k4_tarski('#skF_1'(A_269,B_270,C_271),A_269),C_271)
      | ~ r2_hidden(A_269,k9_relat_1(C_271,B_270))
      | ~ v1_relat_1(C_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_42,plain,(
    ! [E_71] :
      ( ~ r2_hidden('#skF_5',k2_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ r2_hidden(k4_tarski(E_71,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(E_71,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_785,plain,(
    ! [E_71] :
      ( ~ r2_hidden('#skF_5',k2_relat_1('#skF_4'))
      | ~ r2_hidden(k4_tarski(E_71,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(E_71,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_42])).

tff(c_786,plain,(
    ~ r2_hidden('#skF_5',k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_785])).

tff(c_519,plain,(
    ! [A_206,B_207,C_208] :
      ( r2_hidden('#skF_1'(A_206,B_207,C_208),k1_relat_1(C_208))
      | ~ r2_hidden(A_206,k9_relat_1(C_208,B_207))
      | ~ v1_relat_1(C_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_711,plain,(
    ! [A_242,B_243,C_244,B_245] :
      ( m1_subset_1('#skF_1'(A_242,B_243,C_244),B_245)
      | ~ r1_tarski(k1_relat_1(C_244),B_245)
      | ~ r2_hidden(A_242,k9_relat_1(C_244,B_243))
      | ~ v1_relat_1(C_244) ) ),
    inference(resolution,[status(thm)],[c_519,c_168])).

tff(c_725,plain,(
    ! [A_251,B_252,B_253,A_254] :
      ( m1_subset_1('#skF_1'(A_251,B_252,B_253),A_254)
      | ~ r2_hidden(A_251,k9_relat_1(B_253,B_252))
      | ~ v4_relat_1(B_253,A_254)
      | ~ v1_relat_1(B_253) ) ),
    inference(resolution,[status(thm)],[c_10,c_711])).

tff(c_735,plain,(
    ! [A_251,A_254] :
      ( m1_subset_1('#skF_1'(A_251,'#skF_3','#skF_4'),A_254)
      | ~ r2_hidden(A_251,k2_relat_1('#skF_4'))
      | ~ v4_relat_1('#skF_4',A_254)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_725])).

tff(c_741,plain,(
    ! [A_255,A_256] :
      ( m1_subset_1('#skF_1'(A_255,'#skF_3','#skF_4'),A_256)
      | ~ r2_hidden(A_255,k2_relat_1('#skF_4'))
      | ~ v4_relat_1('#skF_4',A_256) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_735])).

tff(c_753,plain,(
    ! [A_257] :
      ( m1_subset_1('#skF_1'('#skF_7','#skF_3','#skF_4'),A_257)
      | ~ v4_relat_1('#skF_4',A_257) ) ),
    inference(resolution,[status(thm)],[c_492,c_741])).

tff(c_523,plain,(
    ! [A_209,B_210,C_211] :
      ( r2_hidden(k4_tarski('#skF_1'(A_209,B_210,C_211),A_209),C_211)
      | ~ r2_hidden(A_209,k9_relat_1(C_211,B_210))
      | ~ v1_relat_1(C_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_44,plain,(
    ! [E_71] :
      ( r2_hidden(k4_tarski('#skF_6','#skF_5'),'#skF_4')
      | ~ r2_hidden(k4_tarski(E_71,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(E_71,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_516,plain,(
    ! [E_71] :
      ( ~ r2_hidden(k4_tarski(E_71,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(E_71,'#skF_3') ) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_527,plain,(
    ! [B_210] :
      ( ~ m1_subset_1('#skF_1'('#skF_7',B_210,'#skF_4'),'#skF_3')
      | ~ r2_hidden('#skF_7',k9_relat_1('#skF_4',B_210))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_523,c_516])).

tff(c_558,plain,(
    ! [B_215] :
      ( ~ m1_subset_1('#skF_1'('#skF_7',B_215,'#skF_4'),'#skF_3')
      | ~ r2_hidden('#skF_7',k9_relat_1('#skF_4',B_215)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_527])).

tff(c_561,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_7','#skF_3','#skF_4'),'#skF_3')
    | ~ r2_hidden('#skF_7',k2_relat_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_558])).

tff(c_563,plain,(
    ~ m1_subset_1('#skF_1'('#skF_7','#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_561])).

tff(c_756,plain,(
    ~ v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_753,c_563])).

tff(c_783,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_756])).

tff(c_784,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_24,plain,(
    ! [B_19,C_20,A_18] :
      ( r2_hidden(B_19,k2_relat_1(C_20))
      | ~ r2_hidden(k4_tarski(A_18,B_19),C_20)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_789,plain,
    ( r2_hidden('#skF_5',k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_784,c_24])).

tff(c_797,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_789])).

tff(c_799,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_786,c_797])).

tff(c_800,plain,(
    ! [E_71] :
      ( ~ r2_hidden(k4_tarski(E_71,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(E_71,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_785])).

tff(c_900,plain,(
    ! [B_270] :
      ( ~ m1_subset_1('#skF_1'('#skF_7',B_270,'#skF_4'),'#skF_3')
      | ~ r2_hidden('#skF_7',k9_relat_1('#skF_4',B_270))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_896,c_800])).

tff(c_931,plain,(
    ! [B_275] :
      ( ~ m1_subset_1('#skF_1'('#skF_7',B_275,'#skF_4'),'#skF_3')
      | ~ r2_hidden('#skF_7',k9_relat_1('#skF_4',B_275)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_900])).

tff(c_934,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_7','#skF_3','#skF_4'),'#skF_3')
    | ~ r2_hidden('#skF_7',k2_relat_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_931])).

tff(c_936,plain,(
    ~ m1_subset_1('#skF_1'('#skF_7','#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_934])).

tff(c_1309,plain,(
    ~ v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1306,c_936])).

tff(c_1336,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_1309])).

tff(c_1338,plain,(
    ~ r2_hidden('#skF_7',k2_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,
    ( r2_hidden(k4_tarski('#skF_6','#skF_5'),'#skF_4')
    | r2_hidden('#skF_7',k2_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1356,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1338,c_50])).

tff(c_1504,plain,(
    ! [B_373,C_374,A_375] :
      ( r2_hidden(B_373,k2_relat_1(C_374))
      | ~ r2_hidden(k4_tarski(A_375,B_373),C_374)
      | ~ v1_relat_1(C_374) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1507,plain,
    ( r2_hidden('#skF_5',k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1356,c_1504])).

tff(c_1510,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1507])).

tff(c_1514,plain,(
    ! [A_376,B_377,C_378] :
      ( k2_relset_1(A_376,B_377,C_378) = k2_relat_1(C_378)
      | ~ m1_subset_1(C_378,k1_zfmisc_1(k2_zfmisc_1(A_376,B_377))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1528,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_1514])).

tff(c_48,plain,
    ( ~ r2_hidden('#skF_5',k2_relset_1('#skF_3','#skF_2','#skF_4'))
    | r2_hidden('#skF_7',k2_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1501,plain,(
    ~ r2_hidden('#skF_5',k2_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_1338,c_48])).

tff(c_1529,plain,(
    ~ r2_hidden('#skF_5',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1528,c_1501])).

tff(c_1533,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1510,c_1529])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:36:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.58  
% 3.49/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.58  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 3.49/1.58  
% 3.49/1.58  %Foreground sorts:
% 3.49/1.58  
% 3.49/1.58  
% 3.49/1.58  %Background operators:
% 3.49/1.58  
% 3.49/1.58  
% 3.49/1.58  %Foreground operators:
% 3.49/1.58  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.49/1.58  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.49/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.49/1.58  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.49/1.58  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.49/1.58  tff('#skF_7', type, '#skF_7': $i).
% 3.49/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.49/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.49/1.58  tff('#skF_5', type, '#skF_5': $i).
% 3.49/1.58  tff('#skF_6', type, '#skF_6': $i).
% 3.49/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.49/1.58  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.49/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.49/1.58  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.49/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.49/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.49/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.49/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.49/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.58  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.49/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.49/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.49/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.49/1.58  
% 3.49/1.60  tff(f_103, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (![D]: (r2_hidden(D, k2_relset_1(B, A, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(E, D), C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relset_1)).
% 3.49/1.60  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.49/1.60  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.49/1.60  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.49/1.60  tff(f_62, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.49/1.60  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.49/1.60  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.49/1.60  tff(f_52, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 3.49/1.60  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.49/1.60  tff(f_35, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.49/1.60  tff(f_70, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 3.49/1.60  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.49/1.60  tff(c_63, plain, (![C_76, A_77, B_78]: (v1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.49/1.60  tff(c_72, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_63])).
% 3.49/1.60  tff(c_81, plain, (![C_84, A_85, B_86]: (v4_relat_1(C_84, A_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.49/1.60  tff(c_90, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_81])).
% 3.49/1.60  tff(c_481, plain, (![A_195, B_196, C_197]: (k2_relset_1(A_195, B_196, C_197)=k2_relat_1(C_197) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_195, B_196))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.49/1.60  tff(c_490, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_481])).
% 3.49/1.60  tff(c_52, plain, (m1_subset_1('#skF_6', '#skF_3') | r2_hidden('#skF_7', k2_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.49/1.60  tff(c_79, plain, (r2_hidden('#skF_7', k2_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_52])).
% 3.49/1.60  tff(c_492, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_490, c_79])).
% 3.49/1.60  tff(c_97, plain, (![B_90, A_91]: (k7_relat_1(B_90, A_91)=B_90 | ~v4_relat_1(B_90, A_91) | ~v1_relat_1(B_90))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.49/1.60  tff(c_100, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_90, c_97])).
% 3.49/1.60  tff(c_103, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_100])).
% 3.49/1.60  tff(c_125, plain, (![B_98, A_99]: (k2_relat_1(k7_relat_1(B_98, A_99))=k9_relat_1(B_98, A_99) | ~v1_relat_1(B_98))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.49/1.60  tff(c_134, plain, (k9_relat_1('#skF_4', '#skF_3')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_103, c_125])).
% 3.49/1.60  tff(c_138, plain, (k9_relat_1('#skF_4', '#skF_3')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_134])).
% 3.49/1.60  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.49/1.60  tff(c_823, plain, (![A_258, B_259, C_260]: (r2_hidden('#skF_1'(A_258, B_259, C_260), k1_relat_1(C_260)) | ~r2_hidden(A_258, k9_relat_1(C_260, B_259)) | ~v1_relat_1(C_260))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.49/1.60  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.49/1.60  tff(c_163, plain, (![A_102, C_103, B_104]: (m1_subset_1(A_102, C_103) | ~m1_subset_1(B_104, k1_zfmisc_1(C_103)) | ~r2_hidden(A_102, B_104))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.49/1.60  tff(c_168, plain, (![A_102, B_2, A_1]: (m1_subset_1(A_102, B_2) | ~r2_hidden(A_102, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_163])).
% 3.49/1.60  tff(c_1187, plain, (![A_320, B_321, C_322, B_323]: (m1_subset_1('#skF_1'(A_320, B_321, C_322), B_323) | ~r1_tarski(k1_relat_1(C_322), B_323) | ~r2_hidden(A_320, k9_relat_1(C_322, B_321)) | ~v1_relat_1(C_322))), inference(resolution, [status(thm)], [c_823, c_168])).
% 3.49/1.60  tff(c_1191, plain, (![A_324, B_325, B_326, A_327]: (m1_subset_1('#skF_1'(A_324, B_325, B_326), A_327) | ~r2_hidden(A_324, k9_relat_1(B_326, B_325)) | ~v4_relat_1(B_326, A_327) | ~v1_relat_1(B_326))), inference(resolution, [status(thm)], [c_10, c_1187])).
% 3.49/1.60  tff(c_1201, plain, (![A_324, A_327]: (m1_subset_1('#skF_1'(A_324, '#skF_3', '#skF_4'), A_327) | ~r2_hidden(A_324, k2_relat_1('#skF_4')) | ~v4_relat_1('#skF_4', A_327) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_138, c_1191])).
% 3.49/1.60  tff(c_1261, plain, (![A_330, A_331]: (m1_subset_1('#skF_1'(A_330, '#skF_3', '#skF_4'), A_331) | ~r2_hidden(A_330, k2_relat_1('#skF_4')) | ~v4_relat_1('#skF_4', A_331))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1201])).
% 3.49/1.60  tff(c_1306, plain, (![A_333]: (m1_subset_1('#skF_1'('#skF_7', '#skF_3', '#skF_4'), A_333) | ~v4_relat_1('#skF_4', A_333))), inference(resolution, [status(thm)], [c_492, c_1261])).
% 3.49/1.60  tff(c_896, plain, (![A_269, B_270, C_271]: (r2_hidden(k4_tarski('#skF_1'(A_269, B_270, C_271), A_269), C_271) | ~r2_hidden(A_269, k9_relat_1(C_271, B_270)) | ~v1_relat_1(C_271))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.49/1.60  tff(c_42, plain, (![E_71]: (~r2_hidden('#skF_5', k2_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~r2_hidden(k4_tarski(E_71, '#skF_7'), '#skF_4') | ~m1_subset_1(E_71, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.49/1.60  tff(c_785, plain, (![E_71]: (~r2_hidden('#skF_5', k2_relat_1('#skF_4')) | ~r2_hidden(k4_tarski(E_71, '#skF_7'), '#skF_4') | ~m1_subset_1(E_71, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_490, c_42])).
% 3.49/1.60  tff(c_786, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_785])).
% 3.49/1.60  tff(c_519, plain, (![A_206, B_207, C_208]: (r2_hidden('#skF_1'(A_206, B_207, C_208), k1_relat_1(C_208)) | ~r2_hidden(A_206, k9_relat_1(C_208, B_207)) | ~v1_relat_1(C_208))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.49/1.60  tff(c_711, plain, (![A_242, B_243, C_244, B_245]: (m1_subset_1('#skF_1'(A_242, B_243, C_244), B_245) | ~r1_tarski(k1_relat_1(C_244), B_245) | ~r2_hidden(A_242, k9_relat_1(C_244, B_243)) | ~v1_relat_1(C_244))), inference(resolution, [status(thm)], [c_519, c_168])).
% 3.49/1.60  tff(c_725, plain, (![A_251, B_252, B_253, A_254]: (m1_subset_1('#skF_1'(A_251, B_252, B_253), A_254) | ~r2_hidden(A_251, k9_relat_1(B_253, B_252)) | ~v4_relat_1(B_253, A_254) | ~v1_relat_1(B_253))), inference(resolution, [status(thm)], [c_10, c_711])).
% 3.49/1.60  tff(c_735, plain, (![A_251, A_254]: (m1_subset_1('#skF_1'(A_251, '#skF_3', '#skF_4'), A_254) | ~r2_hidden(A_251, k2_relat_1('#skF_4')) | ~v4_relat_1('#skF_4', A_254) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_138, c_725])).
% 3.49/1.60  tff(c_741, plain, (![A_255, A_256]: (m1_subset_1('#skF_1'(A_255, '#skF_3', '#skF_4'), A_256) | ~r2_hidden(A_255, k2_relat_1('#skF_4')) | ~v4_relat_1('#skF_4', A_256))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_735])).
% 3.49/1.60  tff(c_753, plain, (![A_257]: (m1_subset_1('#skF_1'('#skF_7', '#skF_3', '#skF_4'), A_257) | ~v4_relat_1('#skF_4', A_257))), inference(resolution, [status(thm)], [c_492, c_741])).
% 3.49/1.60  tff(c_523, plain, (![A_209, B_210, C_211]: (r2_hidden(k4_tarski('#skF_1'(A_209, B_210, C_211), A_209), C_211) | ~r2_hidden(A_209, k9_relat_1(C_211, B_210)) | ~v1_relat_1(C_211))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.49/1.60  tff(c_44, plain, (![E_71]: (r2_hidden(k4_tarski('#skF_6', '#skF_5'), '#skF_4') | ~r2_hidden(k4_tarski(E_71, '#skF_7'), '#skF_4') | ~m1_subset_1(E_71, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.49/1.60  tff(c_516, plain, (![E_71]: (~r2_hidden(k4_tarski(E_71, '#skF_7'), '#skF_4') | ~m1_subset_1(E_71, '#skF_3'))), inference(splitLeft, [status(thm)], [c_44])).
% 3.49/1.60  tff(c_527, plain, (![B_210]: (~m1_subset_1('#skF_1'('#skF_7', B_210, '#skF_4'), '#skF_3') | ~r2_hidden('#skF_7', k9_relat_1('#skF_4', B_210)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_523, c_516])).
% 3.49/1.60  tff(c_558, plain, (![B_215]: (~m1_subset_1('#skF_1'('#skF_7', B_215, '#skF_4'), '#skF_3') | ~r2_hidden('#skF_7', k9_relat_1('#skF_4', B_215)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_527])).
% 3.49/1.60  tff(c_561, plain, (~m1_subset_1('#skF_1'('#skF_7', '#skF_3', '#skF_4'), '#skF_3') | ~r2_hidden('#skF_7', k2_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_138, c_558])).
% 3.49/1.60  tff(c_563, plain, (~m1_subset_1('#skF_1'('#skF_7', '#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_492, c_561])).
% 3.49/1.60  tff(c_756, plain, (~v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_753, c_563])).
% 3.49/1.60  tff(c_783, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_756])).
% 3.49/1.60  tff(c_784, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_44])).
% 3.49/1.60  tff(c_24, plain, (![B_19, C_20, A_18]: (r2_hidden(B_19, k2_relat_1(C_20)) | ~r2_hidden(k4_tarski(A_18, B_19), C_20) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.49/1.60  tff(c_789, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_784, c_24])).
% 3.49/1.60  tff(c_797, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_789])).
% 3.49/1.60  tff(c_799, plain, $false, inference(negUnitSimplification, [status(thm)], [c_786, c_797])).
% 3.49/1.60  tff(c_800, plain, (![E_71]: (~r2_hidden(k4_tarski(E_71, '#skF_7'), '#skF_4') | ~m1_subset_1(E_71, '#skF_3'))), inference(splitRight, [status(thm)], [c_785])).
% 3.49/1.60  tff(c_900, plain, (![B_270]: (~m1_subset_1('#skF_1'('#skF_7', B_270, '#skF_4'), '#skF_3') | ~r2_hidden('#skF_7', k9_relat_1('#skF_4', B_270)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_896, c_800])).
% 3.49/1.60  tff(c_931, plain, (![B_275]: (~m1_subset_1('#skF_1'('#skF_7', B_275, '#skF_4'), '#skF_3') | ~r2_hidden('#skF_7', k9_relat_1('#skF_4', B_275)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_900])).
% 3.49/1.60  tff(c_934, plain, (~m1_subset_1('#skF_1'('#skF_7', '#skF_3', '#skF_4'), '#skF_3') | ~r2_hidden('#skF_7', k2_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_138, c_931])).
% 3.49/1.60  tff(c_936, plain, (~m1_subset_1('#skF_1'('#skF_7', '#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_492, c_934])).
% 3.49/1.60  tff(c_1309, plain, (~v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1306, c_936])).
% 3.49/1.60  tff(c_1336, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_1309])).
% 3.49/1.60  tff(c_1338, plain, (~r2_hidden('#skF_7', k2_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_52])).
% 3.49/1.60  tff(c_50, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_5'), '#skF_4') | r2_hidden('#skF_7', k2_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.49/1.60  tff(c_1356, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1338, c_50])).
% 3.49/1.60  tff(c_1504, plain, (![B_373, C_374, A_375]: (r2_hidden(B_373, k2_relat_1(C_374)) | ~r2_hidden(k4_tarski(A_375, B_373), C_374) | ~v1_relat_1(C_374))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.49/1.60  tff(c_1507, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1356, c_1504])).
% 3.49/1.60  tff(c_1510, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1507])).
% 3.49/1.60  tff(c_1514, plain, (![A_376, B_377, C_378]: (k2_relset_1(A_376, B_377, C_378)=k2_relat_1(C_378) | ~m1_subset_1(C_378, k1_zfmisc_1(k2_zfmisc_1(A_376, B_377))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.49/1.60  tff(c_1528, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_1514])).
% 3.49/1.60  tff(c_48, plain, (~r2_hidden('#skF_5', k2_relset_1('#skF_3', '#skF_2', '#skF_4')) | r2_hidden('#skF_7', k2_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.49/1.60  tff(c_1501, plain, (~r2_hidden('#skF_5', k2_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1338, c_48])).
% 3.49/1.60  tff(c_1529, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1528, c_1501])).
% 3.49/1.60  tff(c_1533, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1510, c_1529])).
% 3.49/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.60  
% 3.49/1.60  Inference rules
% 3.49/1.60  ----------------------
% 3.49/1.60  #Ref     : 0
% 3.49/1.60  #Sup     : 311
% 3.49/1.60  #Fact    : 0
% 3.49/1.60  #Define  : 0
% 3.49/1.60  #Split   : 12
% 3.49/1.60  #Chain   : 0
% 3.49/1.60  #Close   : 0
% 3.49/1.60  
% 3.49/1.60  Ordering : KBO
% 3.49/1.60  
% 3.49/1.60  Simplification rules
% 3.49/1.60  ----------------------
% 3.49/1.60  #Subsume      : 43
% 3.49/1.60  #Demod        : 57
% 3.49/1.60  #Tautology    : 39
% 3.49/1.60  #SimpNegUnit  : 3
% 3.49/1.60  #BackRed      : 6
% 3.49/1.60  
% 3.49/1.60  #Partial instantiations: 0
% 3.49/1.60  #Strategies tried      : 1
% 3.49/1.60  
% 3.49/1.60  Timing (in seconds)
% 3.49/1.60  ----------------------
% 3.77/1.60  Preprocessing        : 0.31
% 3.77/1.60  Parsing              : 0.16
% 3.77/1.60  CNF conversion       : 0.02
% 3.77/1.60  Main loop            : 0.49
% 3.77/1.60  Inferencing          : 0.20
% 3.77/1.60  Reduction            : 0.13
% 3.77/1.60  Demodulation         : 0.09
% 3.77/1.60  BG Simplification    : 0.02
% 3.77/1.60  Subsumption          : 0.09
% 3.77/1.60  Abstraction          : 0.02
% 3.77/1.60  MUC search           : 0.00
% 3.77/1.60  Cooper               : 0.00
% 3.77/1.60  Total                : 0.84
% 3.77/1.60  Index Insertion      : 0.00
% 3.77/1.60  Index Deletion       : 0.00
% 3.77/1.60  Index Matching       : 0.00
% 3.77/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
