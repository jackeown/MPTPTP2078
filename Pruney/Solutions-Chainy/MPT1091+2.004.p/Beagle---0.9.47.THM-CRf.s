%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:25 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 245 expanded)
%              Number of leaves         :   20 (  82 expanded)
%              Depth                    :   11
%              Number of atoms          :  188 ( 548 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_finset_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_finset_1(A)
          & ! [B] :
              ( r2_hidden(B,A)
             => v1_finset_1(B) ) )
      <=> v1_finset_1(k3_tarski(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_finset_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_finset_1(A)
        & ! [B] :
            ( r2_hidden(B,A)
           => v1_finset_1(B) ) )
     => v1_finset_1(k3_tarski(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_finset_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_finset_1(A)
     => v1_finset_1(k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc17_finset_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,B)
        & v1_finset_1(B) )
     => v1_finset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_finset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(k3_tarski(A),B)
        & r2_hidden(C,A) )
     => r1_tarski(C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).

tff(c_20,plain,
    ( v1_finset_1(k3_tarski('#skF_3'))
    | ~ v1_finset_1(k3_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_40,plain,(
    ~ v1_finset_1(k3_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_32,plain,
    ( v1_finset_1(k3_tarski('#skF_3'))
    | v1_finset_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_37,plain,(
    v1_finset_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_55,plain,(
    ! [A_26] :
      ( ~ v1_finset_1('#skF_2'(A_26))
      | v1_finset_1(k3_tarski(A_26))
      | ~ v1_finset_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_61,plain,
    ( ~ v1_finset_1('#skF_2'('#skF_5'))
    | ~ v1_finset_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_55,c_40])).

tff(c_65,plain,(
    ~ v1_finset_1('#skF_2'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_61])).

tff(c_229,plain,(
    ! [A_54] :
      ( r2_hidden('#skF_2'(A_54),A_54)
      | v1_finset_1(k3_tarski(A_54))
      | ~ v1_finset_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_201,plain,(
    ! [A_48] :
      ( r2_hidden('#skF_2'(A_48),A_48)
      | v1_finset_1(k3_tarski(A_48))
      | ~ v1_finset_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_2'(A_11),A_11)
      | v1_finset_1(k3_tarski(A_11))
      | ~ v1_finset_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_28,plain,(
    ! [B_17] :
      ( ~ v1_finset_1('#skF_4')
      | ~ v1_finset_1('#skF_3')
      | v1_finset_1(B_17)
      | ~ r2_hidden(B_17,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_78,plain,(
    ~ v1_finset_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_26,plain,(
    ! [B_17] :
      ( v1_finset_1(k3_tarski('#skF_3'))
      | v1_finset_1(B_17)
      | ~ r2_hidden(B_17,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_77,plain,(
    v1_finset_1(k3_tarski('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_12,plain,(
    ! [A_10] :
      ( v1_finset_1(k1_zfmisc_1(A_10))
      | ~ v1_finset_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(A_6,k1_zfmisc_1(k3_tarski(A_6))) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_42,plain,(
    ! [A_20,B_21] :
      ( v1_finset_1(A_20)
      | ~ v1_finset_1(B_21)
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_47,plain,(
    ! [A_22] :
      ( v1_finset_1(A_22)
      | ~ v1_finset_1(k1_zfmisc_1(k3_tarski(A_22))) ) ),
    inference(resolution,[status(thm)],[c_8,c_42])).

tff(c_51,plain,(
    ! [A_22] :
      ( v1_finset_1(A_22)
      | ~ v1_finset_1(k3_tarski(A_22)) ) ),
    inference(resolution,[status(thm)],[c_12,c_47])).

tff(c_81,plain,(
    v1_finset_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_77,c_51])).

tff(c_85,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_81])).

tff(c_86,plain,(
    ! [B_17] :
      ( ~ v1_finset_1('#skF_4')
      | v1_finset_1(B_17)
      | ~ r2_hidden(B_17,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_93,plain,(
    ~ v1_finset_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_66,plain,(
    ! [A_27,B_28] :
      ( ~ r2_hidden('#skF_1'(A_27,B_28),B_28)
      | r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_71,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_66])).

tff(c_87,plain,(
    v1_finset_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_30,plain,(
    ! [B_17] :
      ( r2_hidden('#skF_4','#skF_3')
      | ~ v1_finset_1('#skF_3')
      | v1_finset_1(B_17)
      | ~ r2_hidden(B_17,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_103,plain,(
    ! [B_17] :
      ( r2_hidden('#skF_4','#skF_3')
      | v1_finset_1(B_17)
      | ~ r2_hidden(B_17,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_30])).

tff(c_104,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_123,plain,(
    ! [C_38,B_39,A_40] :
      ( r1_tarski(C_38,B_39)
      | ~ r2_hidden(C_38,A_40)
      | ~ r1_tarski(k3_tarski(A_40),B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_139,plain,(
    ! [B_41] :
      ( r1_tarski('#skF_4',B_41)
      | ~ r1_tarski(k3_tarski('#skF_3'),B_41) ) ),
    inference(resolution,[status(thm)],[c_104,c_123])).

tff(c_148,plain,(
    r1_tarski('#skF_4',k3_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_71,c_139])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( v1_finset_1(A_13)
      | ~ v1_finset_1(B_14)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_166,plain,
    ( v1_finset_1('#skF_4')
    | ~ v1_finset_1(k3_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_148,c_18])).

tff(c_170,plain,(
    v1_finset_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_166])).

tff(c_172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_170])).

tff(c_175,plain,(
    ! [B_45] :
      ( v1_finset_1(B_45)
      | ~ r2_hidden(B_45,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_179,plain,
    ( v1_finset_1('#skF_2'('#skF_5'))
    | v1_finset_1(k3_tarski('#skF_5'))
    | ~ v1_finset_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_175])).

tff(c_186,plain,
    ( v1_finset_1('#skF_2'('#skF_5'))
    | v1_finset_1(k3_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_179])).

tff(c_188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_65,c_186])).

tff(c_189,plain,(
    ! [B_17] :
      ( v1_finset_1(B_17)
      | ~ r2_hidden(B_17,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_205,plain,
    ( v1_finset_1('#skF_2'('#skF_5'))
    | v1_finset_1(k3_tarski('#skF_5'))
    | ~ v1_finset_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_201,c_189])).

tff(c_208,plain,
    ( v1_finset_1('#skF_2'('#skF_5'))
    | v1_finset_1(k3_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_205])).

tff(c_210,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_65,c_208])).

tff(c_211,plain,(
    ! [B_17] :
      ( v1_finset_1(B_17)
      | ~ r2_hidden(B_17,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_235,plain,
    ( v1_finset_1('#skF_2'('#skF_5'))
    | v1_finset_1(k3_tarski('#skF_5'))
    | ~ v1_finset_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_229,c_211])).

tff(c_239,plain,
    ( v1_finset_1('#skF_2'('#skF_5'))
    | v1_finset_1(k3_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_235])).

tff(c_241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_65,c_239])).

tff(c_243,plain,(
    v1_finset_1(k3_tarski('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_242,plain,(
    v1_finset_1(k3_tarski('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_245,plain,(
    ! [A_55,B_56] :
      ( v1_finset_1(A_55)
      | ~ v1_finset_1(B_56)
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_250,plain,(
    ! [A_57] :
      ( v1_finset_1(A_57)
      | ~ v1_finset_1(k1_zfmisc_1(k3_tarski(A_57))) ) ),
    inference(resolution,[status(thm)],[c_8,c_245])).

tff(c_255,plain,(
    ! [A_58] :
      ( v1_finset_1(A_58)
      | ~ v1_finset_1(k3_tarski(A_58)) ) ),
    inference(resolution,[status(thm)],[c_12,c_250])).

tff(c_264,plain,(
    v1_finset_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_242,c_255])).

tff(c_22,plain,
    ( ~ v1_finset_1('#skF_4')
    | ~ v1_finset_1('#skF_3')
    | ~ v1_finset_1(k3_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_267,plain,(
    ~ v1_finset_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_264,c_22])).

tff(c_274,plain,(
    ! [A_62,B_63] :
      ( ~ r2_hidden('#skF_1'(A_62,B_63),B_63)
      | r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_279,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_274])).

tff(c_24,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | ~ v1_finset_1('#skF_3')
    | ~ v1_finset_1(k3_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_287,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_264,c_24])).

tff(c_318,plain,(
    ! [C_73,B_74,A_75] :
      ( r1_tarski(C_73,B_74)
      | ~ r2_hidden(C_73,A_75)
      | ~ r1_tarski(k3_tarski(A_75),B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_334,plain,(
    ! [B_76] :
      ( r1_tarski('#skF_4',B_76)
      | ~ r1_tarski(k3_tarski('#skF_3'),B_76) ) ),
    inference(resolution,[status(thm)],[c_287,c_318])).

tff(c_343,plain,(
    r1_tarski('#skF_4',k3_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_279,c_334])).

tff(c_349,plain,
    ( v1_finset_1('#skF_4')
    | ~ v1_finset_1(k3_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_343,c_18])).

tff(c_353,plain,(
    v1_finset_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_349])).

tff(c_355,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_267,c_353])).

tff(c_357,plain,(
    ~ v1_finset_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_34,plain,
    ( ~ v1_finset_1('#skF_4')
    | ~ v1_finset_1('#skF_3')
    | v1_finset_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_361,plain,
    ( ~ v1_finset_1('#skF_4')
    | ~ v1_finset_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_357,c_34])).

tff(c_362,plain,(
    ~ v1_finset_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_361])).

tff(c_356,plain,(
    v1_finset_1(k3_tarski('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_364,plain,(
    ! [A_79,B_80] :
      ( v1_finset_1(A_79)
      | ~ v1_finset_1(B_80)
      | ~ r1_tarski(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_369,plain,(
    ! [A_81] :
      ( v1_finset_1(A_81)
      | ~ v1_finset_1(k1_zfmisc_1(k3_tarski(A_81))) ) ),
    inference(resolution,[status(thm)],[c_8,c_364])).

tff(c_374,plain,(
    ! [A_82] :
      ( v1_finset_1(A_82)
      | ~ v1_finset_1(k3_tarski(A_82)) ) ),
    inference(resolution,[status(thm)],[c_12,c_369])).

tff(c_377,plain,(
    v1_finset_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_356,c_374])).

tff(c_381,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_362,c_377])).

tff(c_382,plain,(
    ~ v1_finset_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_361])).

tff(c_407,plain,(
    ! [A_89,B_90] :
      ( r2_hidden('#skF_1'(A_89,B_90),A_89)
      | r1_tarski(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_412,plain,(
    ! [A_89] : r1_tarski(A_89,A_89) ),
    inference(resolution,[status(thm)],[c_407,c_4])).

tff(c_383,plain,(
    v1_finset_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_361])).

tff(c_36,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | ~ v1_finset_1('#skF_3')
    | v1_finset_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_403,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | v1_finset_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_36])).

tff(c_404,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_357,c_403])).

tff(c_459,plain,(
    ! [C_101,B_102,A_103] :
      ( r1_tarski(C_101,B_102)
      | ~ r2_hidden(C_101,A_103)
      | ~ r1_tarski(k3_tarski(A_103),B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_475,plain,(
    ! [B_104] :
      ( r1_tarski('#skF_4',B_104)
      | ~ r1_tarski(k3_tarski('#skF_3'),B_104) ) ),
    inference(resolution,[status(thm)],[c_404,c_459])).

tff(c_484,plain,(
    r1_tarski('#skF_4',k3_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_412,c_475])).

tff(c_490,plain,
    ( v1_finset_1('#skF_4')
    | ~ v1_finset_1(k3_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_484,c_18])).

tff(c_494,plain,(
    v1_finset_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_490])).

tff(c_496,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_382,c_494])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:06:50 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.31  
% 2.24/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.31  %$ r2_hidden > r1_tarski > v1_finset_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.24/1.31  
% 2.24/1.31  %Foreground sorts:
% 2.24/1.31  
% 2.24/1.31  
% 2.24/1.31  %Background operators:
% 2.24/1.31  
% 2.24/1.31  
% 2.24/1.31  %Foreground operators:
% 2.24/1.31  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.24/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.24/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.24/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.24/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.24/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.24/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.24/1.31  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 2.24/1.31  
% 2.24/1.33  tff(f_69, negated_conjecture, ~(![A]: ((v1_finset_1(A) & (![B]: (r2_hidden(B, A) => v1_finset_1(B)))) <=> v1_finset_1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_finset_1)).
% 2.24/1.33  tff(f_53, axiom, (![A]: ((v1_finset_1(A) & (![B]: (r2_hidden(B, A) => v1_finset_1(B)))) => v1_finset_1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_finset_1)).
% 2.24/1.33  tff(f_44, axiom, (![A]: (v1_finset_1(A) => v1_finset_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc17_finset_1)).
% 2.24/1.33  tff(f_34, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 2.24/1.33  tff(f_59, axiom, (![A, B]: ((r1_tarski(A, B) & v1_finset_1(B)) => v1_finset_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_finset_1)).
% 2.24/1.33  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.24/1.33  tff(f_40, axiom, (![A, B, C]: ((r1_tarski(k3_tarski(A), B) & r2_hidden(C, A)) => r1_tarski(C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_setfam_1)).
% 2.24/1.33  tff(c_20, plain, (v1_finset_1(k3_tarski('#skF_3')) | ~v1_finset_1(k3_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.24/1.33  tff(c_40, plain, (~v1_finset_1(k3_tarski('#skF_5'))), inference(splitLeft, [status(thm)], [c_20])).
% 2.24/1.33  tff(c_32, plain, (v1_finset_1(k3_tarski('#skF_3')) | v1_finset_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.24/1.33  tff(c_37, plain, (v1_finset_1('#skF_5')), inference(splitLeft, [status(thm)], [c_32])).
% 2.24/1.33  tff(c_55, plain, (![A_26]: (~v1_finset_1('#skF_2'(A_26)) | v1_finset_1(k3_tarski(A_26)) | ~v1_finset_1(A_26))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.24/1.33  tff(c_61, plain, (~v1_finset_1('#skF_2'('#skF_5')) | ~v1_finset_1('#skF_5')), inference(resolution, [status(thm)], [c_55, c_40])).
% 2.24/1.33  tff(c_65, plain, (~v1_finset_1('#skF_2'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_61])).
% 2.24/1.33  tff(c_229, plain, (![A_54]: (r2_hidden('#skF_2'(A_54), A_54) | v1_finset_1(k3_tarski(A_54)) | ~v1_finset_1(A_54))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.24/1.33  tff(c_201, plain, (![A_48]: (r2_hidden('#skF_2'(A_48), A_48) | v1_finset_1(k3_tarski(A_48)) | ~v1_finset_1(A_48))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.24/1.33  tff(c_16, plain, (![A_11]: (r2_hidden('#skF_2'(A_11), A_11) | v1_finset_1(k3_tarski(A_11)) | ~v1_finset_1(A_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.24/1.33  tff(c_28, plain, (![B_17]: (~v1_finset_1('#skF_4') | ~v1_finset_1('#skF_3') | v1_finset_1(B_17) | ~r2_hidden(B_17, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.24/1.33  tff(c_78, plain, (~v1_finset_1('#skF_3')), inference(splitLeft, [status(thm)], [c_28])).
% 2.24/1.33  tff(c_26, plain, (![B_17]: (v1_finset_1(k3_tarski('#skF_3')) | v1_finset_1(B_17) | ~r2_hidden(B_17, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.24/1.33  tff(c_77, plain, (v1_finset_1(k3_tarski('#skF_3'))), inference(splitLeft, [status(thm)], [c_26])).
% 2.24/1.33  tff(c_12, plain, (![A_10]: (v1_finset_1(k1_zfmisc_1(A_10)) | ~v1_finset_1(A_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.24/1.33  tff(c_8, plain, (![A_6]: (r1_tarski(A_6, k1_zfmisc_1(k3_tarski(A_6))))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.24/1.33  tff(c_42, plain, (![A_20, B_21]: (v1_finset_1(A_20) | ~v1_finset_1(B_21) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.24/1.33  tff(c_47, plain, (![A_22]: (v1_finset_1(A_22) | ~v1_finset_1(k1_zfmisc_1(k3_tarski(A_22))))), inference(resolution, [status(thm)], [c_8, c_42])).
% 2.24/1.33  tff(c_51, plain, (![A_22]: (v1_finset_1(A_22) | ~v1_finset_1(k3_tarski(A_22)))), inference(resolution, [status(thm)], [c_12, c_47])).
% 2.24/1.33  tff(c_81, plain, (v1_finset_1('#skF_3')), inference(resolution, [status(thm)], [c_77, c_51])).
% 2.24/1.33  tff(c_85, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_81])).
% 2.24/1.33  tff(c_86, plain, (![B_17]: (~v1_finset_1('#skF_4') | v1_finset_1(B_17) | ~r2_hidden(B_17, '#skF_5'))), inference(splitRight, [status(thm)], [c_28])).
% 2.24/1.33  tff(c_93, plain, (~v1_finset_1('#skF_4')), inference(splitLeft, [status(thm)], [c_86])).
% 2.24/1.33  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.24/1.33  tff(c_66, plain, (![A_27, B_28]: (~r2_hidden('#skF_1'(A_27, B_28), B_28) | r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.24/1.33  tff(c_71, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_66])).
% 2.24/1.33  tff(c_87, plain, (v1_finset_1('#skF_3')), inference(splitRight, [status(thm)], [c_28])).
% 2.24/1.33  tff(c_30, plain, (![B_17]: (r2_hidden('#skF_4', '#skF_3') | ~v1_finset_1('#skF_3') | v1_finset_1(B_17) | ~r2_hidden(B_17, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.24/1.33  tff(c_103, plain, (![B_17]: (r2_hidden('#skF_4', '#skF_3') | v1_finset_1(B_17) | ~r2_hidden(B_17, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_30])).
% 2.24/1.33  tff(c_104, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_103])).
% 2.24/1.33  tff(c_123, plain, (![C_38, B_39, A_40]: (r1_tarski(C_38, B_39) | ~r2_hidden(C_38, A_40) | ~r1_tarski(k3_tarski(A_40), B_39))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.24/1.33  tff(c_139, plain, (![B_41]: (r1_tarski('#skF_4', B_41) | ~r1_tarski(k3_tarski('#skF_3'), B_41))), inference(resolution, [status(thm)], [c_104, c_123])).
% 2.24/1.33  tff(c_148, plain, (r1_tarski('#skF_4', k3_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_71, c_139])).
% 2.24/1.33  tff(c_18, plain, (![A_13, B_14]: (v1_finset_1(A_13) | ~v1_finset_1(B_14) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.24/1.33  tff(c_166, plain, (v1_finset_1('#skF_4') | ~v1_finset_1(k3_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_148, c_18])).
% 2.24/1.33  tff(c_170, plain, (v1_finset_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_166])).
% 2.24/1.33  tff(c_172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_170])).
% 2.24/1.33  tff(c_175, plain, (![B_45]: (v1_finset_1(B_45) | ~r2_hidden(B_45, '#skF_5'))), inference(splitRight, [status(thm)], [c_103])).
% 2.24/1.33  tff(c_179, plain, (v1_finset_1('#skF_2'('#skF_5')) | v1_finset_1(k3_tarski('#skF_5')) | ~v1_finset_1('#skF_5')), inference(resolution, [status(thm)], [c_16, c_175])).
% 2.24/1.33  tff(c_186, plain, (v1_finset_1('#skF_2'('#skF_5')) | v1_finset_1(k3_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_179])).
% 2.24/1.33  tff(c_188, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_65, c_186])).
% 2.24/1.33  tff(c_189, plain, (![B_17]: (v1_finset_1(B_17) | ~r2_hidden(B_17, '#skF_5'))), inference(splitRight, [status(thm)], [c_86])).
% 2.24/1.33  tff(c_205, plain, (v1_finset_1('#skF_2'('#skF_5')) | v1_finset_1(k3_tarski('#skF_5')) | ~v1_finset_1('#skF_5')), inference(resolution, [status(thm)], [c_201, c_189])).
% 2.24/1.33  tff(c_208, plain, (v1_finset_1('#skF_2'('#skF_5')) | v1_finset_1(k3_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_205])).
% 2.24/1.33  tff(c_210, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_65, c_208])).
% 2.24/1.33  tff(c_211, plain, (![B_17]: (v1_finset_1(B_17) | ~r2_hidden(B_17, '#skF_5'))), inference(splitRight, [status(thm)], [c_26])).
% 2.24/1.33  tff(c_235, plain, (v1_finset_1('#skF_2'('#skF_5')) | v1_finset_1(k3_tarski('#skF_5')) | ~v1_finset_1('#skF_5')), inference(resolution, [status(thm)], [c_229, c_211])).
% 2.24/1.33  tff(c_239, plain, (v1_finset_1('#skF_2'('#skF_5')) | v1_finset_1(k3_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_235])).
% 2.24/1.33  tff(c_241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_65, c_239])).
% 2.24/1.33  tff(c_243, plain, (v1_finset_1(k3_tarski('#skF_5'))), inference(splitRight, [status(thm)], [c_20])).
% 2.24/1.33  tff(c_242, plain, (v1_finset_1(k3_tarski('#skF_3'))), inference(splitRight, [status(thm)], [c_20])).
% 2.24/1.33  tff(c_245, plain, (![A_55, B_56]: (v1_finset_1(A_55) | ~v1_finset_1(B_56) | ~r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.24/1.33  tff(c_250, plain, (![A_57]: (v1_finset_1(A_57) | ~v1_finset_1(k1_zfmisc_1(k3_tarski(A_57))))), inference(resolution, [status(thm)], [c_8, c_245])).
% 2.24/1.33  tff(c_255, plain, (![A_58]: (v1_finset_1(A_58) | ~v1_finset_1(k3_tarski(A_58)))), inference(resolution, [status(thm)], [c_12, c_250])).
% 2.24/1.33  tff(c_264, plain, (v1_finset_1('#skF_3')), inference(resolution, [status(thm)], [c_242, c_255])).
% 2.24/1.33  tff(c_22, plain, (~v1_finset_1('#skF_4') | ~v1_finset_1('#skF_3') | ~v1_finset_1(k3_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.24/1.33  tff(c_267, plain, (~v1_finset_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_243, c_264, c_22])).
% 2.24/1.33  tff(c_274, plain, (![A_62, B_63]: (~r2_hidden('#skF_1'(A_62, B_63), B_63) | r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.24/1.33  tff(c_279, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_274])).
% 2.24/1.33  tff(c_24, plain, (r2_hidden('#skF_4', '#skF_3') | ~v1_finset_1('#skF_3') | ~v1_finset_1(k3_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.24/1.33  tff(c_287, plain, (r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_243, c_264, c_24])).
% 2.24/1.33  tff(c_318, plain, (![C_73, B_74, A_75]: (r1_tarski(C_73, B_74) | ~r2_hidden(C_73, A_75) | ~r1_tarski(k3_tarski(A_75), B_74))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.24/1.33  tff(c_334, plain, (![B_76]: (r1_tarski('#skF_4', B_76) | ~r1_tarski(k3_tarski('#skF_3'), B_76))), inference(resolution, [status(thm)], [c_287, c_318])).
% 2.24/1.33  tff(c_343, plain, (r1_tarski('#skF_4', k3_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_279, c_334])).
% 2.24/1.33  tff(c_349, plain, (v1_finset_1('#skF_4') | ~v1_finset_1(k3_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_343, c_18])).
% 2.24/1.33  tff(c_353, plain, (v1_finset_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_242, c_349])).
% 2.24/1.33  tff(c_355, plain, $false, inference(negUnitSimplification, [status(thm)], [c_267, c_353])).
% 2.24/1.33  tff(c_357, plain, (~v1_finset_1('#skF_5')), inference(splitRight, [status(thm)], [c_32])).
% 2.24/1.33  tff(c_34, plain, (~v1_finset_1('#skF_4') | ~v1_finset_1('#skF_3') | v1_finset_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.24/1.33  tff(c_361, plain, (~v1_finset_1('#skF_4') | ~v1_finset_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_357, c_34])).
% 2.24/1.33  tff(c_362, plain, (~v1_finset_1('#skF_3')), inference(splitLeft, [status(thm)], [c_361])).
% 2.24/1.33  tff(c_356, plain, (v1_finset_1(k3_tarski('#skF_3'))), inference(splitRight, [status(thm)], [c_32])).
% 2.24/1.33  tff(c_364, plain, (![A_79, B_80]: (v1_finset_1(A_79) | ~v1_finset_1(B_80) | ~r1_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.24/1.33  tff(c_369, plain, (![A_81]: (v1_finset_1(A_81) | ~v1_finset_1(k1_zfmisc_1(k3_tarski(A_81))))), inference(resolution, [status(thm)], [c_8, c_364])).
% 2.24/1.33  tff(c_374, plain, (![A_82]: (v1_finset_1(A_82) | ~v1_finset_1(k3_tarski(A_82)))), inference(resolution, [status(thm)], [c_12, c_369])).
% 2.24/1.33  tff(c_377, plain, (v1_finset_1('#skF_3')), inference(resolution, [status(thm)], [c_356, c_374])).
% 2.24/1.33  tff(c_381, plain, $false, inference(negUnitSimplification, [status(thm)], [c_362, c_377])).
% 2.24/1.33  tff(c_382, plain, (~v1_finset_1('#skF_4')), inference(splitRight, [status(thm)], [c_361])).
% 2.24/1.33  tff(c_407, plain, (![A_89, B_90]: (r2_hidden('#skF_1'(A_89, B_90), A_89) | r1_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.24/1.33  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.24/1.33  tff(c_412, plain, (![A_89]: (r1_tarski(A_89, A_89))), inference(resolution, [status(thm)], [c_407, c_4])).
% 2.24/1.33  tff(c_383, plain, (v1_finset_1('#skF_3')), inference(splitRight, [status(thm)], [c_361])).
% 2.24/1.33  tff(c_36, plain, (r2_hidden('#skF_4', '#skF_3') | ~v1_finset_1('#skF_3') | v1_finset_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.24/1.33  tff(c_403, plain, (r2_hidden('#skF_4', '#skF_3') | v1_finset_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_383, c_36])).
% 2.24/1.33  tff(c_404, plain, (r2_hidden('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_357, c_403])).
% 2.24/1.33  tff(c_459, plain, (![C_101, B_102, A_103]: (r1_tarski(C_101, B_102) | ~r2_hidden(C_101, A_103) | ~r1_tarski(k3_tarski(A_103), B_102))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.24/1.33  tff(c_475, plain, (![B_104]: (r1_tarski('#skF_4', B_104) | ~r1_tarski(k3_tarski('#skF_3'), B_104))), inference(resolution, [status(thm)], [c_404, c_459])).
% 2.24/1.33  tff(c_484, plain, (r1_tarski('#skF_4', k3_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_412, c_475])).
% 2.24/1.33  tff(c_490, plain, (v1_finset_1('#skF_4') | ~v1_finset_1(k3_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_484, c_18])).
% 2.24/1.33  tff(c_494, plain, (v1_finset_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_356, c_490])).
% 2.24/1.33  tff(c_496, plain, $false, inference(negUnitSimplification, [status(thm)], [c_382, c_494])).
% 2.24/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.33  
% 2.24/1.33  Inference rules
% 2.24/1.33  ----------------------
% 2.24/1.33  #Ref     : 0
% 2.24/1.33  #Sup     : 85
% 2.24/1.33  #Fact    : 0
% 2.24/1.33  #Define  : 0
% 2.24/1.33  #Split   : 10
% 2.24/1.33  #Chain   : 0
% 2.24/1.33  #Close   : 0
% 2.24/1.33  
% 2.24/1.33  Ordering : KBO
% 2.24/1.33  
% 2.24/1.33  Simplification rules
% 2.24/1.33  ----------------------
% 2.24/1.33  #Subsume      : 14
% 2.24/1.33  #Demod        : 32
% 2.24/1.33  #Tautology    : 18
% 2.24/1.33  #SimpNegUnit  : 11
% 2.24/1.33  #BackRed      : 0
% 2.24/1.33  
% 2.24/1.33  #Partial instantiations: 0
% 2.24/1.33  #Strategies tried      : 1
% 2.24/1.33  
% 2.24/1.33  Timing (in seconds)
% 2.24/1.33  ----------------------
% 2.24/1.33  Preprocessing        : 0.27
% 2.24/1.33  Parsing              : 0.15
% 2.24/1.33  CNF conversion       : 0.02
% 2.24/1.33  Main loop            : 0.29
% 2.24/1.33  Inferencing          : 0.12
% 2.24/1.33  Reduction            : 0.07
% 2.24/1.33  Demodulation         : 0.05
% 2.24/1.33  BG Simplification    : 0.01
% 2.24/1.33  Subsumption          : 0.06
% 2.24/1.33  Abstraction          : 0.01
% 2.24/1.33  MUC search           : 0.00
% 2.24/1.33  Cooper               : 0.00
% 2.24/1.33  Total                : 0.60
% 2.24/1.33  Index Insertion      : 0.00
% 2.24/1.33  Index Deletion       : 0.00
% 2.24/1.33  Index Matching       : 0.00
% 2.24/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
