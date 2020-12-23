%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:24 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 257 expanded)
%              Number of leaves         :   20 (  84 expanded)
%              Depth                    :    7
%              Number of atoms          :  199 ( 582 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_finset_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(f_65,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_finset_1(A)
          & ! [B] :
              ( r2_hidden(B,A)
             => v1_finset_1(B) ) )
      <=> v1_finset_1(k3_tarski(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_finset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_finset_1(A)
        & ! [B] :
            ( r2_hidden(B,A)
           => v1_finset_1(B) ) )
     => v1_finset_1(k3_tarski(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_finset_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_finset_1(A)
     => v1_finset_1(k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc17_finset_1)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_finset_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_finset_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_finset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(c_18,plain,
    ( v1_finset_1(k3_tarski('#skF_2'))
    | ~ v1_finset_1(k3_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_38,plain,(
    ~ v1_finset_1(k3_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_30,plain,
    ( v1_finset_1(k3_tarski('#skF_2'))
    | v1_finset_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_35,plain,(
    v1_finset_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_188,plain,(
    ! [A_45] :
      ( ~ v1_finset_1('#skF_1'(A_45))
      | v1_finset_1(k3_tarski(A_45))
      | ~ v1_finset_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_194,plain,
    ( ~ v1_finset_1('#skF_1'('#skF_4'))
    | ~ v1_finset_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_188,c_38])).

tff(c_198,plain,(
    ~ v1_finset_1('#skF_1'('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_194])).

tff(c_228,plain,(
    ! [A_54] :
      ( r2_hidden('#skF_1'(A_54),A_54)
      | v1_finset_1(k3_tarski(A_54))
      | ~ v1_finset_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_49,plain,(
    ! [A_23] :
      ( ~ v1_finset_1('#skF_1'(A_23))
      | v1_finset_1(k3_tarski(A_23))
      | ~ v1_finset_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_52,plain,
    ( ~ v1_finset_1('#skF_1'('#skF_4'))
    | ~ v1_finset_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_49,c_38])).

tff(c_55,plain,(
    ~ v1_finset_1('#skF_1'('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_52])).

tff(c_168,plain,(
    ! [A_43] :
      ( r2_hidden('#skF_1'(A_43),A_43)
      | v1_finset_1(k3_tarski(A_43))
      | ~ v1_finset_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_128,plain,(
    ! [A_37] :
      ( r2_hidden('#skF_1'(A_37),A_37)
      | v1_finset_1(k3_tarski(A_37))
      | ~ v1_finset_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [B_14] :
      ( ~ v1_finset_1('#skF_3')
      | ~ v1_finset_1('#skF_2')
      | v1_finset_1(B_14)
      | ~ r2_hidden(B_14,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_70,plain,(
    ~ v1_finset_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_24,plain,(
    ! [B_14] :
      ( v1_finset_1(k3_tarski('#skF_2'))
      | v1_finset_1(B_14)
      | ~ r2_hidden(B_14,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_48,plain,(
    v1_finset_1(k3_tarski('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_12,plain,(
    ! [A_9] :
      ( v1_finset_1(k1_zfmisc_1(A_9))
      | ~ v1_finset_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_3] : r1_tarski(A_3,k1_zfmisc_1(k3_tarski(A_3))) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_56,plain,(
    ! [B_24,A_25] :
      ( v1_finset_1(B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(A_25))
      | ~ v1_finset_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_61,plain,(
    ! [A_26,B_27] :
      ( v1_finset_1(A_26)
      | ~ v1_finset_1(B_27)
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(resolution,[status(thm)],[c_8,c_56])).

tff(c_71,plain,(
    ! [A_28] :
      ( v1_finset_1(A_28)
      | ~ v1_finset_1(k1_zfmisc_1(k3_tarski(A_28))) ) ),
    inference(resolution,[status(thm)],[c_4,c_61])).

tff(c_76,plain,(
    ! [A_29] :
      ( v1_finset_1(A_29)
      | ~ v1_finset_1(k3_tarski(A_29)) ) ),
    inference(resolution,[status(thm)],[c_12,c_71])).

tff(c_82,plain,(
    v1_finset_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_76])).

tff(c_87,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_82])).

tff(c_88,plain,(
    ! [B_14] :
      ( ~ v1_finset_1('#skF_3')
      | v1_finset_1(B_14)
      | ~ r2_hidden(B_14,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_95,plain,(
    ~ v1_finset_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_89,plain,(
    v1_finset_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_28,plain,(
    ! [B_14] :
      ( r2_hidden('#skF_3','#skF_2')
      | ~ v1_finset_1('#skF_2')
      | v1_finset_1(B_14)
      | ~ r2_hidden(B_14,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_114,plain,(
    ! [B_14] :
      ( r2_hidden('#skF_3','#skF_2')
      | v1_finset_1(B_14)
      | ~ r2_hidden(B_14,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_28])).

tff(c_115,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,k3_tarski(B_2))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_106,plain,(
    ! [A_32,B_33] :
      ( v1_finset_1(A_32)
      | ~ v1_finset_1(k3_tarski(B_33))
      | ~ r2_hidden(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_2,c_61])).

tff(c_116,plain,(
    ! [A_34] :
      ( v1_finset_1(A_34)
      | ~ r2_hidden(A_34,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_48,c_106])).

tff(c_119,plain,(
    v1_finset_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_115,c_116])).

tff(c_123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_119])).

tff(c_124,plain,(
    ! [B_14] :
      ( v1_finset_1(B_14)
      | ~ r2_hidden(B_14,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_136,plain,
    ( v1_finset_1('#skF_1'('#skF_4'))
    | v1_finset_1(k3_tarski('#skF_4'))
    | ~ v1_finset_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_128,c_124])).

tff(c_142,plain,
    ( v1_finset_1('#skF_1'('#skF_4'))
    | v1_finset_1(k3_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_136])).

tff(c_144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_55,c_142])).

tff(c_145,plain,(
    ! [B_14] :
      ( v1_finset_1(B_14)
      | ~ r2_hidden(B_14,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_176,plain,
    ( v1_finset_1('#skF_1'('#skF_4'))
    | v1_finset_1(k3_tarski('#skF_4'))
    | ~ v1_finset_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_168,c_145])).

tff(c_182,plain,
    ( v1_finset_1('#skF_1'('#skF_4'))
    | v1_finset_1(k3_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_176])).

tff(c_184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_55,c_182])).

tff(c_185,plain,(
    ! [B_14] :
      ( v1_finset_1(B_14)
      | ~ r2_hidden(B_14,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_232,plain,
    ( v1_finset_1('#skF_1'('#skF_4'))
    | v1_finset_1(k3_tarski('#skF_4'))
    | ~ v1_finset_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_228,c_185])).

tff(c_235,plain,
    ( v1_finset_1('#skF_1'('#skF_4'))
    | v1_finset_1(k3_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_232])).

tff(c_237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_198,c_235])).

tff(c_239,plain,(
    v1_finset_1(k3_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_20,plain,
    ( ~ v1_finset_1('#skF_3')
    | ~ v1_finset_1('#skF_2')
    | ~ v1_finset_1(k3_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_249,plain,
    ( ~ v1_finset_1('#skF_3')
    | ~ v1_finset_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_20])).

tff(c_250,plain,(
    ~ v1_finset_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_249])).

tff(c_238,plain,(
    v1_finset_1(k3_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_256,plain,(
    ! [B_62,A_63] :
      ( v1_finset_1(B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_63))
      | ~ v1_finset_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_261,plain,(
    ! [A_64,B_65] :
      ( v1_finset_1(A_64)
      | ~ v1_finset_1(B_65)
      | ~ r1_tarski(A_64,B_65) ) ),
    inference(resolution,[status(thm)],[c_8,c_256])).

tff(c_270,plain,(
    ! [A_66] :
      ( v1_finset_1(A_66)
      | ~ v1_finset_1(k1_zfmisc_1(k3_tarski(A_66))) ) ),
    inference(resolution,[status(thm)],[c_4,c_261])).

tff(c_275,plain,(
    ! [A_67] :
      ( v1_finset_1(A_67)
      | ~ v1_finset_1(k3_tarski(A_67)) ) ),
    inference(resolution,[status(thm)],[c_12,c_270])).

tff(c_284,plain,(
    v1_finset_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_238,c_275])).

tff(c_291,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_250,c_284])).

tff(c_292,plain,(
    ~ v1_finset_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_293,plain,(
    v1_finset_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_22,plain,
    ( r2_hidden('#skF_3','#skF_2')
    | ~ v1_finset_1('#skF_2')
    | ~ v1_finset_1(k3_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_296,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_293,c_22])).

tff(c_301,plain,(
    ! [B_71,A_72] :
      ( v1_finset_1(B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_72))
      | ~ v1_finset_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_306,plain,(
    ! [A_73,B_74] :
      ( v1_finset_1(A_73)
      | ~ v1_finset_1(B_74)
      | ~ r1_tarski(A_73,B_74) ) ),
    inference(resolution,[status(thm)],[c_8,c_301])).

tff(c_335,plain,(
    ! [A_77,B_78] :
      ( v1_finset_1(A_77)
      | ~ v1_finset_1(k3_tarski(B_78))
      | ~ r2_hidden(A_77,B_78) ) ),
    inference(resolution,[status(thm)],[c_2,c_306])).

tff(c_354,plain,(
    ! [A_81] :
      ( v1_finset_1(A_81)
      | ~ r2_hidden(A_81,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_238,c_335])).

tff(c_361,plain,(
    v1_finset_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_296,c_354])).

tff(c_368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_292,c_361])).

tff(c_370,plain,(
    ~ v1_finset_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_32,plain,
    ( ~ v1_finset_1('#skF_3')
    | ~ v1_finset_1('#skF_2')
    | v1_finset_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_374,plain,
    ( ~ v1_finset_1('#skF_3')
    | ~ v1_finset_1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_370,c_32])).

tff(c_375,plain,(
    ~ v1_finset_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_374])).

tff(c_369,plain,(
    v1_finset_1(k3_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_389,plain,(
    ! [B_91,A_92] :
      ( v1_finset_1(B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_92))
      | ~ v1_finset_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_394,plain,(
    ! [A_93,B_94] :
      ( v1_finset_1(A_93)
      | ~ v1_finset_1(B_94)
      | ~ r1_tarski(A_93,B_94) ) ),
    inference(resolution,[status(thm)],[c_8,c_389])).

tff(c_404,plain,(
    ! [A_95] :
      ( v1_finset_1(A_95)
      | ~ v1_finset_1(k1_zfmisc_1(k3_tarski(A_95))) ) ),
    inference(resolution,[status(thm)],[c_4,c_394])).

tff(c_409,plain,(
    ! [A_96] :
      ( v1_finset_1(A_96)
      | ~ v1_finset_1(k3_tarski(A_96)) ) ),
    inference(resolution,[status(thm)],[c_12,c_404])).

tff(c_415,plain,(
    v1_finset_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_369,c_409])).

tff(c_420,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_375,c_415])).

tff(c_421,plain,(
    ~ v1_finset_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_374])).

tff(c_422,plain,(
    v1_finset_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_374])).

tff(c_34,plain,
    ( r2_hidden('#skF_3','#skF_2')
    | ~ v1_finset_1('#skF_2')
    | v1_finset_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_423,plain,
    ( r2_hidden('#skF_3','#skF_2')
    | ~ v1_finset_1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_370,c_34])).

tff(c_424,plain,(
    ~ v1_finset_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_423])).

tff(c_426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_424])).

tff(c_427,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_423])).

tff(c_447,plain,(
    ! [B_104,A_105] :
      ( v1_finset_1(B_104)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_105))
      | ~ v1_finset_1(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_452,plain,(
    ! [A_106,B_107] :
      ( v1_finset_1(A_106)
      | ~ v1_finset_1(B_107)
      | ~ r1_tarski(A_106,B_107) ) ),
    inference(resolution,[status(thm)],[c_8,c_447])).

tff(c_478,plain,(
    ! [A_110,B_111] :
      ( v1_finset_1(A_110)
      | ~ v1_finset_1(k3_tarski(B_111))
      | ~ r2_hidden(A_110,B_111) ) ),
    inference(resolution,[status(thm)],[c_2,c_452])).

tff(c_485,plain,(
    ! [A_112] :
      ( v1_finset_1(A_112)
      | ~ r2_hidden(A_112,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_369,c_478])).

tff(c_488,plain,(
    v1_finset_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_427,c_485])).

tff(c_492,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_421,c_488])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:39:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.38  
% 2.23/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.39  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_finset_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.23/1.39  
% 2.23/1.39  %Foreground sorts:
% 2.23/1.39  
% 2.23/1.39  
% 2.23/1.39  %Background operators:
% 2.23/1.39  
% 2.23/1.39  
% 2.23/1.39  %Foreground operators:
% 2.23/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.23/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.23/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.23/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.39  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 2.23/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.23/1.39  
% 2.52/1.41  tff(f_65, negated_conjecture, ~(![A]: ((v1_finset_1(A) & (![B]: (r2_hidden(B, A) => v1_finset_1(B)))) <=> v1_finset_1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_finset_1)).
% 2.52/1.41  tff(f_55, axiom, (![A]: ((v1_finset_1(A) & (![B]: (r2_hidden(B, A) => v1_finset_1(B)))) => v1_finset_1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_finset_1)).
% 2.52/1.41  tff(f_46, axiom, (![A]: (v1_finset_1(A) => v1_finset_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc17_finset_1)).
% 2.52/1.41  tff(f_31, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 2.52/1.41  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.52/1.41  tff(f_42, axiom, (![A]: (v1_finset_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_finset_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_finset_1)).
% 2.52/1.41  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.52/1.41  tff(c_18, plain, (v1_finset_1(k3_tarski('#skF_2')) | ~v1_finset_1(k3_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.52/1.41  tff(c_38, plain, (~v1_finset_1(k3_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_18])).
% 2.52/1.41  tff(c_30, plain, (v1_finset_1(k3_tarski('#skF_2')) | v1_finset_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.52/1.41  tff(c_35, plain, (v1_finset_1('#skF_4')), inference(splitLeft, [status(thm)], [c_30])).
% 2.52/1.41  tff(c_188, plain, (![A_45]: (~v1_finset_1('#skF_1'(A_45)) | v1_finset_1(k3_tarski(A_45)) | ~v1_finset_1(A_45))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.52/1.41  tff(c_194, plain, (~v1_finset_1('#skF_1'('#skF_4')) | ~v1_finset_1('#skF_4')), inference(resolution, [status(thm)], [c_188, c_38])).
% 2.52/1.41  tff(c_198, plain, (~v1_finset_1('#skF_1'('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_194])).
% 2.52/1.41  tff(c_228, plain, (![A_54]: (r2_hidden('#skF_1'(A_54), A_54) | v1_finset_1(k3_tarski(A_54)) | ~v1_finset_1(A_54))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.52/1.41  tff(c_49, plain, (![A_23]: (~v1_finset_1('#skF_1'(A_23)) | v1_finset_1(k3_tarski(A_23)) | ~v1_finset_1(A_23))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.52/1.41  tff(c_52, plain, (~v1_finset_1('#skF_1'('#skF_4')) | ~v1_finset_1('#skF_4')), inference(resolution, [status(thm)], [c_49, c_38])).
% 2.52/1.41  tff(c_55, plain, (~v1_finset_1('#skF_1'('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_52])).
% 2.52/1.41  tff(c_168, plain, (![A_43]: (r2_hidden('#skF_1'(A_43), A_43) | v1_finset_1(k3_tarski(A_43)) | ~v1_finset_1(A_43))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.52/1.41  tff(c_128, plain, (![A_37]: (r2_hidden('#skF_1'(A_37), A_37) | v1_finset_1(k3_tarski(A_37)) | ~v1_finset_1(A_37))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.52/1.41  tff(c_26, plain, (![B_14]: (~v1_finset_1('#skF_3') | ~v1_finset_1('#skF_2') | v1_finset_1(B_14) | ~r2_hidden(B_14, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.52/1.41  tff(c_70, plain, (~v1_finset_1('#skF_2')), inference(splitLeft, [status(thm)], [c_26])).
% 2.52/1.41  tff(c_24, plain, (![B_14]: (v1_finset_1(k3_tarski('#skF_2')) | v1_finset_1(B_14) | ~r2_hidden(B_14, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.52/1.41  tff(c_48, plain, (v1_finset_1(k3_tarski('#skF_2'))), inference(splitLeft, [status(thm)], [c_24])).
% 2.52/1.41  tff(c_12, plain, (![A_9]: (v1_finset_1(k1_zfmisc_1(A_9)) | ~v1_finset_1(A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.52/1.41  tff(c_4, plain, (![A_3]: (r1_tarski(A_3, k1_zfmisc_1(k3_tarski(A_3))))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.52/1.41  tff(c_8, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.52/1.41  tff(c_56, plain, (![B_24, A_25]: (v1_finset_1(B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(A_25)) | ~v1_finset_1(A_25))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.52/1.41  tff(c_61, plain, (![A_26, B_27]: (v1_finset_1(A_26) | ~v1_finset_1(B_27) | ~r1_tarski(A_26, B_27))), inference(resolution, [status(thm)], [c_8, c_56])).
% 2.52/1.41  tff(c_71, plain, (![A_28]: (v1_finset_1(A_28) | ~v1_finset_1(k1_zfmisc_1(k3_tarski(A_28))))), inference(resolution, [status(thm)], [c_4, c_61])).
% 2.52/1.41  tff(c_76, plain, (![A_29]: (v1_finset_1(A_29) | ~v1_finset_1(k3_tarski(A_29)))), inference(resolution, [status(thm)], [c_12, c_71])).
% 2.52/1.41  tff(c_82, plain, (v1_finset_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_76])).
% 2.52/1.41  tff(c_87, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_82])).
% 2.52/1.41  tff(c_88, plain, (![B_14]: (~v1_finset_1('#skF_3') | v1_finset_1(B_14) | ~r2_hidden(B_14, '#skF_4'))), inference(splitRight, [status(thm)], [c_26])).
% 2.52/1.41  tff(c_95, plain, (~v1_finset_1('#skF_3')), inference(splitLeft, [status(thm)], [c_88])).
% 2.52/1.41  tff(c_89, plain, (v1_finset_1('#skF_2')), inference(splitRight, [status(thm)], [c_26])).
% 2.52/1.41  tff(c_28, plain, (![B_14]: (r2_hidden('#skF_3', '#skF_2') | ~v1_finset_1('#skF_2') | v1_finset_1(B_14) | ~r2_hidden(B_14, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.52/1.41  tff(c_114, plain, (![B_14]: (r2_hidden('#skF_3', '#skF_2') | v1_finset_1(B_14) | ~r2_hidden(B_14, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_28])).
% 2.52/1.41  tff(c_115, plain, (r2_hidden('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_114])).
% 2.52/1.41  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k3_tarski(B_2)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.52/1.41  tff(c_106, plain, (![A_32, B_33]: (v1_finset_1(A_32) | ~v1_finset_1(k3_tarski(B_33)) | ~r2_hidden(A_32, B_33))), inference(resolution, [status(thm)], [c_2, c_61])).
% 2.52/1.41  tff(c_116, plain, (![A_34]: (v1_finset_1(A_34) | ~r2_hidden(A_34, '#skF_2'))), inference(resolution, [status(thm)], [c_48, c_106])).
% 2.52/1.41  tff(c_119, plain, (v1_finset_1('#skF_3')), inference(resolution, [status(thm)], [c_115, c_116])).
% 2.52/1.41  tff(c_123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_119])).
% 2.52/1.41  tff(c_124, plain, (![B_14]: (v1_finset_1(B_14) | ~r2_hidden(B_14, '#skF_4'))), inference(splitRight, [status(thm)], [c_114])).
% 2.52/1.41  tff(c_136, plain, (v1_finset_1('#skF_1'('#skF_4')) | v1_finset_1(k3_tarski('#skF_4')) | ~v1_finset_1('#skF_4')), inference(resolution, [status(thm)], [c_128, c_124])).
% 2.52/1.41  tff(c_142, plain, (v1_finset_1('#skF_1'('#skF_4')) | v1_finset_1(k3_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_136])).
% 2.52/1.41  tff(c_144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_55, c_142])).
% 2.52/1.41  tff(c_145, plain, (![B_14]: (v1_finset_1(B_14) | ~r2_hidden(B_14, '#skF_4'))), inference(splitRight, [status(thm)], [c_88])).
% 2.52/1.41  tff(c_176, plain, (v1_finset_1('#skF_1'('#skF_4')) | v1_finset_1(k3_tarski('#skF_4')) | ~v1_finset_1('#skF_4')), inference(resolution, [status(thm)], [c_168, c_145])).
% 2.52/1.41  tff(c_182, plain, (v1_finset_1('#skF_1'('#skF_4')) | v1_finset_1(k3_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_176])).
% 2.52/1.41  tff(c_184, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_55, c_182])).
% 2.52/1.41  tff(c_185, plain, (![B_14]: (v1_finset_1(B_14) | ~r2_hidden(B_14, '#skF_4'))), inference(splitRight, [status(thm)], [c_24])).
% 2.52/1.41  tff(c_232, plain, (v1_finset_1('#skF_1'('#skF_4')) | v1_finset_1(k3_tarski('#skF_4')) | ~v1_finset_1('#skF_4')), inference(resolution, [status(thm)], [c_228, c_185])).
% 2.52/1.41  tff(c_235, plain, (v1_finset_1('#skF_1'('#skF_4')) | v1_finset_1(k3_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_232])).
% 2.52/1.41  tff(c_237, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_198, c_235])).
% 2.52/1.41  tff(c_239, plain, (v1_finset_1(k3_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_18])).
% 2.52/1.41  tff(c_20, plain, (~v1_finset_1('#skF_3') | ~v1_finset_1('#skF_2') | ~v1_finset_1(k3_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.52/1.41  tff(c_249, plain, (~v1_finset_1('#skF_3') | ~v1_finset_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_239, c_20])).
% 2.52/1.41  tff(c_250, plain, (~v1_finset_1('#skF_2')), inference(splitLeft, [status(thm)], [c_249])).
% 2.52/1.41  tff(c_238, plain, (v1_finset_1(k3_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_18])).
% 2.52/1.41  tff(c_256, plain, (![B_62, A_63]: (v1_finset_1(B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_63)) | ~v1_finset_1(A_63))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.52/1.41  tff(c_261, plain, (![A_64, B_65]: (v1_finset_1(A_64) | ~v1_finset_1(B_65) | ~r1_tarski(A_64, B_65))), inference(resolution, [status(thm)], [c_8, c_256])).
% 2.52/1.41  tff(c_270, plain, (![A_66]: (v1_finset_1(A_66) | ~v1_finset_1(k1_zfmisc_1(k3_tarski(A_66))))), inference(resolution, [status(thm)], [c_4, c_261])).
% 2.52/1.41  tff(c_275, plain, (![A_67]: (v1_finset_1(A_67) | ~v1_finset_1(k3_tarski(A_67)))), inference(resolution, [status(thm)], [c_12, c_270])).
% 2.52/1.41  tff(c_284, plain, (v1_finset_1('#skF_2')), inference(resolution, [status(thm)], [c_238, c_275])).
% 2.52/1.41  tff(c_291, plain, $false, inference(negUnitSimplification, [status(thm)], [c_250, c_284])).
% 2.52/1.41  tff(c_292, plain, (~v1_finset_1('#skF_3')), inference(splitRight, [status(thm)], [c_249])).
% 2.52/1.41  tff(c_293, plain, (v1_finset_1('#skF_2')), inference(splitRight, [status(thm)], [c_249])).
% 2.52/1.41  tff(c_22, plain, (r2_hidden('#skF_3', '#skF_2') | ~v1_finset_1('#skF_2') | ~v1_finset_1(k3_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.52/1.41  tff(c_296, plain, (r2_hidden('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_239, c_293, c_22])).
% 2.52/1.41  tff(c_301, plain, (![B_71, A_72]: (v1_finset_1(B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_72)) | ~v1_finset_1(A_72))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.52/1.41  tff(c_306, plain, (![A_73, B_74]: (v1_finset_1(A_73) | ~v1_finset_1(B_74) | ~r1_tarski(A_73, B_74))), inference(resolution, [status(thm)], [c_8, c_301])).
% 2.52/1.41  tff(c_335, plain, (![A_77, B_78]: (v1_finset_1(A_77) | ~v1_finset_1(k3_tarski(B_78)) | ~r2_hidden(A_77, B_78))), inference(resolution, [status(thm)], [c_2, c_306])).
% 2.52/1.41  tff(c_354, plain, (![A_81]: (v1_finset_1(A_81) | ~r2_hidden(A_81, '#skF_2'))), inference(resolution, [status(thm)], [c_238, c_335])).
% 2.52/1.41  tff(c_361, plain, (v1_finset_1('#skF_3')), inference(resolution, [status(thm)], [c_296, c_354])).
% 2.52/1.41  tff(c_368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_292, c_361])).
% 2.52/1.41  tff(c_370, plain, (~v1_finset_1('#skF_4')), inference(splitRight, [status(thm)], [c_30])).
% 2.52/1.41  tff(c_32, plain, (~v1_finset_1('#skF_3') | ~v1_finset_1('#skF_2') | v1_finset_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.52/1.41  tff(c_374, plain, (~v1_finset_1('#skF_3') | ~v1_finset_1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_370, c_32])).
% 2.52/1.41  tff(c_375, plain, (~v1_finset_1('#skF_2')), inference(splitLeft, [status(thm)], [c_374])).
% 2.52/1.41  tff(c_369, plain, (v1_finset_1(k3_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_30])).
% 2.52/1.41  tff(c_389, plain, (![B_91, A_92]: (v1_finset_1(B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(A_92)) | ~v1_finset_1(A_92))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.52/1.41  tff(c_394, plain, (![A_93, B_94]: (v1_finset_1(A_93) | ~v1_finset_1(B_94) | ~r1_tarski(A_93, B_94))), inference(resolution, [status(thm)], [c_8, c_389])).
% 2.52/1.41  tff(c_404, plain, (![A_95]: (v1_finset_1(A_95) | ~v1_finset_1(k1_zfmisc_1(k3_tarski(A_95))))), inference(resolution, [status(thm)], [c_4, c_394])).
% 2.52/1.41  tff(c_409, plain, (![A_96]: (v1_finset_1(A_96) | ~v1_finset_1(k3_tarski(A_96)))), inference(resolution, [status(thm)], [c_12, c_404])).
% 2.52/1.41  tff(c_415, plain, (v1_finset_1('#skF_2')), inference(resolution, [status(thm)], [c_369, c_409])).
% 2.52/1.41  tff(c_420, plain, $false, inference(negUnitSimplification, [status(thm)], [c_375, c_415])).
% 2.52/1.41  tff(c_421, plain, (~v1_finset_1('#skF_3')), inference(splitRight, [status(thm)], [c_374])).
% 2.52/1.41  tff(c_422, plain, (v1_finset_1('#skF_2')), inference(splitRight, [status(thm)], [c_374])).
% 2.52/1.41  tff(c_34, plain, (r2_hidden('#skF_3', '#skF_2') | ~v1_finset_1('#skF_2') | v1_finset_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.52/1.41  tff(c_423, plain, (r2_hidden('#skF_3', '#skF_2') | ~v1_finset_1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_370, c_34])).
% 2.52/1.41  tff(c_424, plain, (~v1_finset_1('#skF_2')), inference(splitLeft, [status(thm)], [c_423])).
% 2.52/1.41  tff(c_426, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_422, c_424])).
% 2.52/1.41  tff(c_427, plain, (r2_hidden('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_423])).
% 2.52/1.41  tff(c_447, plain, (![B_104, A_105]: (v1_finset_1(B_104) | ~m1_subset_1(B_104, k1_zfmisc_1(A_105)) | ~v1_finset_1(A_105))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.52/1.41  tff(c_452, plain, (![A_106, B_107]: (v1_finset_1(A_106) | ~v1_finset_1(B_107) | ~r1_tarski(A_106, B_107))), inference(resolution, [status(thm)], [c_8, c_447])).
% 2.52/1.41  tff(c_478, plain, (![A_110, B_111]: (v1_finset_1(A_110) | ~v1_finset_1(k3_tarski(B_111)) | ~r2_hidden(A_110, B_111))), inference(resolution, [status(thm)], [c_2, c_452])).
% 2.52/1.41  tff(c_485, plain, (![A_112]: (v1_finset_1(A_112) | ~r2_hidden(A_112, '#skF_2'))), inference(resolution, [status(thm)], [c_369, c_478])).
% 2.52/1.41  tff(c_488, plain, (v1_finset_1('#skF_3')), inference(resolution, [status(thm)], [c_427, c_485])).
% 2.52/1.41  tff(c_492, plain, $false, inference(negUnitSimplification, [status(thm)], [c_421, c_488])).
% 2.52/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.41  
% 2.52/1.41  Inference rules
% 2.52/1.41  ----------------------
% 2.52/1.41  #Ref     : 0
% 2.52/1.41  #Sup     : 71
% 2.52/1.41  #Fact    : 0
% 2.52/1.41  #Define  : 0
% 2.52/1.41  #Split   : 11
% 2.52/1.41  #Chain   : 0
% 2.52/1.41  #Close   : 0
% 2.52/1.41  
% 2.52/1.41  Ordering : KBO
% 2.52/1.41  
% 2.52/1.41  Simplification rules
% 2.52/1.41  ----------------------
% 2.52/1.41  #Subsume      : 15
% 2.52/1.41  #Demod        : 40
% 2.52/1.41  #Tautology    : 31
% 2.52/1.41  #SimpNegUnit  : 12
% 2.52/1.41  #BackRed      : 0
% 2.52/1.41  
% 2.52/1.41  #Partial instantiations: 0
% 2.52/1.41  #Strategies tried      : 1
% 2.52/1.41  
% 2.52/1.41  Timing (in seconds)
% 2.52/1.41  ----------------------
% 2.52/1.41  Preprocessing        : 0.29
% 2.52/1.41  Parsing              : 0.16
% 2.52/1.41  CNF conversion       : 0.02
% 2.52/1.41  Main loop            : 0.29
% 2.52/1.41  Inferencing          : 0.13
% 2.52/1.41  Reduction            : 0.07
% 2.52/1.41  Demodulation         : 0.05
% 2.52/1.41  BG Simplification    : 0.01
% 2.52/1.41  Subsumption          : 0.05
% 2.52/1.41  Abstraction          : 0.01
% 2.52/1.41  MUC search           : 0.00
% 2.52/1.41  Cooper               : 0.00
% 2.52/1.41  Total                : 0.63
% 2.52/1.41  Index Insertion      : 0.00
% 2.52/1.41  Index Deletion       : 0.00
% 2.52/1.41  Index Matching       : 0.00
% 2.52/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
