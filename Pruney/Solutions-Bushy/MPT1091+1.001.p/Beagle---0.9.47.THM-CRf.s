%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1091+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:23 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 285 expanded)
%              Number of leaves         :   21 (  95 expanded)
%              Depth                    :   10
%              Number of atoms          :  185 ( 632 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_finset_1 > #nlpp > k9_setfam_1 > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_finset_1(A)
          & ! [B] :
              ( r2_hidden(B,A)
             => v1_finset_1(B) ) )
      <=> v1_finset_1(k3_tarski(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_finset_1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v1_finset_1(A)
        & ! [B] :
            ( r2_hidden(B,A)
           => v1_finset_1(B) ) )
     => v1_finset_1(k3_tarski(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_finset_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_finset_1(A)
     => v1_finset_1(k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc17_finset_1)).

tff(f_48,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_finset_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_finset_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_finset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).

tff(c_20,plain,
    ( v1_finset_1(k3_tarski('#skF_2'))
    | ~ v1_finset_1(k3_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_49,plain,(
    ~ v1_finset_1(k3_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_32,plain,
    ( v1_finset_1(k3_tarski('#skF_2'))
    | v1_finset_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_47,plain,(
    v1_finset_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_59,plain,(
    ! [A_25] :
      ( ~ v1_finset_1('#skF_1'(A_25))
      | v1_finset_1(k3_tarski(A_25))
      | ~ v1_finset_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_62,plain,
    ( ~ v1_finset_1('#skF_1'('#skF_4'))
    | ~ v1_finset_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_59,c_49])).

tff(c_65,plain,(
    ~ v1_finset_1('#skF_1'('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_62])).

tff(c_184,plain,(
    ! [A_47] :
      ( r2_hidden('#skF_1'(A_47),A_47)
      | v1_finset_1(k3_tarski(A_47))
      | ~ v1_finset_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_1'(A_5),A_5)
      | v1_finset_1(k3_tarski(A_5))
      | ~ v1_finset_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_26,plain,(
    ! [B_15] :
      ( v1_finset_1(k3_tarski('#skF_2'))
      | v1_finset_1(B_15)
      | ~ r2_hidden(B_15,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_66,plain,(
    v1_finset_1(k3_tarski('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_4,plain,(
    ! [A_4] :
      ( v1_finset_1(k1_zfmisc_1(A_4))
      | ~ v1_finset_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_8] : r1_tarski(A_8,k1_zfmisc_1(k3_tarski(A_8))) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_67,plain,(
    ! [B_26,A_27] :
      ( v1_finset_1(B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_27))
      | ~ v1_finset_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    ! [A_28,B_29] :
      ( v1_finset_1(A_28)
      | ~ v1_finset_1(B_29)
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(resolution,[status(thm)],[c_16,c_67])).

tff(c_81,plain,(
    ! [A_30] :
      ( v1_finset_1(A_30)
      | ~ v1_finset_1(k1_zfmisc_1(k3_tarski(A_30))) ) ),
    inference(resolution,[status(thm)],[c_12,c_72])).

tff(c_86,plain,(
    ! [A_31] :
      ( v1_finset_1(A_31)
      | ~ v1_finset_1(k3_tarski(A_31)) ) ),
    inference(resolution,[status(thm)],[c_4,c_81])).

tff(c_93,plain,(
    v1_finset_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_86])).

tff(c_28,plain,(
    ! [B_15] :
      ( ~ v1_finset_1('#skF_3')
      | ~ v1_finset_1('#skF_2')
      | v1_finset_1(B_15)
      | ~ r2_hidden(B_15,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_112,plain,(
    ! [B_15] :
      ( ~ v1_finset_1('#skF_3')
      | v1_finset_1(B_15)
      | ~ r2_hidden(B_15,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_28])).

tff(c_113,plain,(
    ~ v1_finset_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_30,plain,(
    ! [B_15] :
      ( r2_hidden('#skF_3','#skF_2')
      | ~ v1_finset_1('#skF_2')
      | v1_finset_1(B_15)
      | ~ r2_hidden(B_15,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_115,plain,(
    ! [B_15] :
      ( r2_hidden('#skF_3','#skF_2')
      | v1_finset_1(B_15)
      | ~ r2_hidden(B_15,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_30])).

tff(c_116,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,k3_tarski(B_12))
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_95,plain,(
    ! [A_32,B_33] :
      ( v1_finset_1(A_32)
      | ~ v1_finset_1(k3_tarski(B_33))
      | ~ r2_hidden(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_18,c_72])).

tff(c_100,plain,(
    ! [A_32] :
      ( v1_finset_1(A_32)
      | ~ r2_hidden(A_32,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_66,c_95])).

tff(c_119,plain,(
    v1_finset_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_116,c_100])).

tff(c_123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_119])).

tff(c_126,plain,(
    ! [B_36] :
      ( v1_finset_1(B_36)
      | ~ r2_hidden(B_36,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_130,plain,
    ( v1_finset_1('#skF_1'('#skF_4'))
    | v1_finset_1(k3_tarski('#skF_4'))
    | ~ v1_finset_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_126])).

tff(c_133,plain,
    ( v1_finset_1('#skF_1'('#skF_4'))
    | v1_finset_1(k3_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_130])).

tff(c_135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_65,c_133])).

tff(c_138,plain,(
    ! [B_37] :
      ( v1_finset_1(B_37)
      | ~ r2_hidden(B_37,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_142,plain,
    ( v1_finset_1('#skF_1'('#skF_4'))
    | v1_finset_1(k3_tarski('#skF_4'))
    | ~ v1_finset_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_138])).

tff(c_145,plain,
    ( v1_finset_1('#skF_1'('#skF_4'))
    | v1_finset_1(k3_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_142])).

tff(c_147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_65,c_145])).

tff(c_148,plain,(
    ! [B_15] :
      ( v1_finset_1(B_15)
      | ~ r2_hidden(B_15,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_188,plain,
    ( v1_finset_1('#skF_1'('#skF_4'))
    | v1_finset_1(k3_tarski('#skF_4'))
    | ~ v1_finset_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_184,c_148])).

tff(c_191,plain,
    ( v1_finset_1('#skF_1'('#skF_4'))
    | v1_finset_1(k3_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_188])).

tff(c_193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_65,c_191])).

tff(c_195,plain,(
    v1_finset_1(k3_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_22,plain,
    ( ~ v1_finset_1('#skF_3')
    | ~ v1_finset_1('#skF_2')
    | ~ v1_finset_1(k3_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_198,plain,
    ( ~ v1_finset_1('#skF_3')
    | ~ v1_finset_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_22])).

tff(c_199,plain,(
    ~ v1_finset_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_198])).

tff(c_194,plain,(
    v1_finset_1(k3_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_208,plain,(
    ! [B_54,A_55] :
      ( v1_finset_1(B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_55))
      | ~ v1_finset_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_213,plain,(
    ! [A_56,B_57] :
      ( v1_finset_1(A_56)
      | ~ v1_finset_1(B_57)
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(resolution,[status(thm)],[c_16,c_208])).

tff(c_222,plain,(
    ! [A_58] :
      ( v1_finset_1(A_58)
      | ~ v1_finset_1(k1_zfmisc_1(k3_tarski(A_58))) ) ),
    inference(resolution,[status(thm)],[c_12,c_213])).

tff(c_227,plain,(
    ! [A_59] :
      ( v1_finset_1(A_59)
      | ~ v1_finset_1(k3_tarski(A_59)) ) ),
    inference(resolution,[status(thm)],[c_4,c_222])).

tff(c_233,plain,(
    v1_finset_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_194,c_227])).

tff(c_239,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_199,c_233])).

tff(c_240,plain,(
    ~ v1_finset_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_241,plain,(
    v1_finset_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_24,plain,
    ( r2_hidden('#skF_3','#skF_2')
    | ~ v1_finset_1('#skF_2')
    | ~ v1_finset_1(k3_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_252,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_241,c_24])).

tff(c_254,plain,(
    ! [B_67,A_68] :
      ( v1_finset_1(B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_68))
      | ~ v1_finset_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_261,plain,(
    ! [A_69,B_70] :
      ( v1_finset_1(A_69)
      | ~ v1_finset_1(B_70)
      | ~ r1_tarski(A_69,B_70) ) ),
    inference(resolution,[status(thm)],[c_16,c_254])).

tff(c_290,plain,(
    ! [A_73,B_74] :
      ( v1_finset_1(A_73)
      | ~ v1_finset_1(k3_tarski(B_74))
      | ~ r2_hidden(A_73,B_74) ) ),
    inference(resolution,[status(thm)],[c_18,c_261])).

tff(c_309,plain,(
    ! [A_77] :
      ( v1_finset_1(A_77)
      | ~ r2_hidden(A_77,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_194,c_290])).

tff(c_316,plain,(
    v1_finset_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_252,c_309])).

tff(c_323,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_316])).

tff(c_325,plain,(
    ~ v1_finset_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_34,plain,
    ( ~ v1_finset_1('#skF_3')
    | ~ v1_finset_1('#skF_2')
    | v1_finset_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_328,plain,
    ( ~ v1_finset_1('#skF_3')
    | ~ v1_finset_1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_325,c_34])).

tff(c_329,plain,(
    ~ v1_finset_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_328])).

tff(c_324,plain,(
    v1_finset_1(k3_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_338,plain,(
    ! [B_85,A_86] :
      ( v1_finset_1(B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_86))
      | ~ v1_finset_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_344,plain,(
    ! [A_87,B_88] :
      ( v1_finset_1(A_87)
      | ~ v1_finset_1(B_88)
      | ~ r1_tarski(A_87,B_88) ) ),
    inference(resolution,[status(thm)],[c_16,c_338])).

tff(c_353,plain,(
    ! [A_89] :
      ( v1_finset_1(A_89)
      | ~ v1_finset_1(k1_zfmisc_1(k3_tarski(A_89))) ) ),
    inference(resolution,[status(thm)],[c_12,c_344])).

tff(c_358,plain,(
    ! [A_90] :
      ( v1_finset_1(A_90)
      | ~ v1_finset_1(k3_tarski(A_90)) ) ),
    inference(resolution,[status(thm)],[c_4,c_353])).

tff(c_361,plain,(
    v1_finset_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_324,c_358])).

tff(c_365,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_329,c_361])).

tff(c_366,plain,(
    ~ v1_finset_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_328])).

tff(c_367,plain,(
    v1_finset_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_328])).

tff(c_36,plain,
    ( r2_hidden('#skF_3','#skF_2')
    | ~ v1_finset_1('#skF_2')
    | v1_finset_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_373,plain,
    ( r2_hidden('#skF_3','#skF_2')
    | v1_finset_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_36])).

tff(c_374,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_325,c_373])).

tff(c_382,plain,(
    ! [B_97,A_98] :
      ( v1_finset_1(B_97)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_98))
      | ~ v1_finset_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_387,plain,(
    ! [A_99,B_100] :
      ( v1_finset_1(A_99)
      | ~ v1_finset_1(B_100)
      | ~ r1_tarski(A_99,B_100) ) ),
    inference(resolution,[status(thm)],[c_16,c_382])).

tff(c_413,plain,(
    ! [A_104,B_105] :
      ( v1_finset_1(A_104)
      | ~ v1_finset_1(k3_tarski(B_105))
      | ~ r2_hidden(A_104,B_105) ) ),
    inference(resolution,[status(thm)],[c_18,c_387])).

tff(c_420,plain,(
    ! [A_106] :
      ( v1_finset_1(A_106)
      | ~ r2_hidden(A_106,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_324,c_413])).

tff(c_423,plain,(
    v1_finset_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_374,c_420])).

tff(c_427,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_366,c_423])).

%------------------------------------------------------------------------------
