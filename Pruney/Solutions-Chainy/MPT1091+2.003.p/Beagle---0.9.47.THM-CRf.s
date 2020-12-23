%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:24 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 249 expanded)
%              Number of leaves         :   24 (  86 expanded)
%              Depth                    :   12
%              Number of atoms          :  186 ( 554 expanded)
%              Number of equality atoms :    1 (   3 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_finset_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_finset_1(A)
          & ! [B] :
              ( r2_hidden(B,A)
             => v1_finset_1(B) ) )
      <=> v1_finset_1(k3_tarski(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_finset_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ( v1_finset_1(A)
        & ! [B] :
            ( r2_hidden(B,A)
           => v1_finset_1(B) ) )
     => v1_finset_1(k3_tarski(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_finset_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_finset_1(A)
     => v1_finset_1(k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc17_finset_1)).

tff(f_44,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_63,axiom,(
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

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(c_36,plain,
    ( v1_finset_1(k3_tarski('#skF_7'))
    | ~ v1_finset_1(k3_tarski('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_56,plain,(
    ~ v1_finset_1(k3_tarski('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_48,plain,
    ( v1_finset_1(k3_tarski('#skF_7'))
    | v1_finset_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_53,plain,(
    v1_finset_1('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_82,plain,(
    ! [A_45] :
      ( ~ v1_finset_1('#skF_6'(A_45))
      | v1_finset_1(k3_tarski(A_45))
      | ~ v1_finset_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_88,plain,
    ( ~ v1_finset_1('#skF_6'('#skF_9'))
    | ~ v1_finset_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_82,c_56])).

tff(c_92,plain,(
    ~ v1_finset_1('#skF_6'('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_88])).

tff(c_276,plain,(
    ! [A_74] :
      ( r2_hidden('#skF_6'(A_74),A_74)
      | v1_finset_1(k3_tarski(A_74))
      | ~ v1_finset_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_248,plain,(
    ! [A_68] :
      ( r2_hidden('#skF_6'(A_68),A_68)
      | v1_finset_1(k3_tarski(A_68))
      | ~ v1_finset_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,(
    ! [A_27] :
      ( r2_hidden('#skF_6'(A_27),A_27)
      | v1_finset_1(k3_tarski(A_27))
      | ~ v1_finset_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_44,plain,(
    ! [B_33] :
      ( ~ v1_finset_1('#skF_8')
      | ~ v1_finset_1('#skF_7')
      | v1_finset_1(B_33)
      | ~ r2_hidden(B_33,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_94,plain,(
    ~ v1_finset_1('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_42,plain,(
    ! [B_33] :
      ( v1_finset_1(k3_tarski('#skF_7'))
      | v1_finset_1(B_33)
      | ~ r2_hidden(B_33,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_93,plain,(
    v1_finset_1(k3_tarski('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_28,plain,(
    ! [A_26] :
      ( v1_finset_1(k1_zfmisc_1(A_26))
      | ~ v1_finset_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_26,plain,(
    ! [A_25] : r1_tarski(A_25,k1_zfmisc_1(k3_tarski(A_25))) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_58,plain,(
    ! [A_36,B_37] :
      ( v1_finset_1(A_36)
      | ~ v1_finset_1(B_37)
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_63,plain,(
    ! [A_38] :
      ( v1_finset_1(A_38)
      | ~ v1_finset_1(k1_zfmisc_1(k3_tarski(A_38))) ) ),
    inference(resolution,[status(thm)],[c_26,c_58])).

tff(c_67,plain,(
    ! [A_38] :
      ( v1_finset_1(A_38)
      | ~ v1_finset_1(k3_tarski(A_38)) ) ),
    inference(resolution,[status(thm)],[c_28,c_63])).

tff(c_97,plain,(
    v1_finset_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_93,c_67])).

tff(c_101,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_97])).

tff(c_102,plain,(
    ! [B_33] :
      ( ~ v1_finset_1('#skF_8')
      | v1_finset_1(B_33)
      | ~ r2_hidden(B_33,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_109,plain,(
    ~ v1_finset_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_103,plain,(
    v1_finset_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_46,plain,(
    ! [B_33] :
      ( r2_hidden('#skF_8','#skF_7')
      | ~ v1_finset_1('#skF_7')
      | v1_finset_1(B_33)
      | ~ r2_hidden(B_33,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_126,plain,(
    ! [B_33] :
      ( r2_hidden('#skF_8','#skF_7')
      | v1_finset_1(B_33)
      | ~ r2_hidden(B_33,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_46])).

tff(c_127,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_8,plain,(
    ! [C_21,A_6,D_24] :
      ( r2_hidden(C_21,k3_tarski(A_6))
      | ~ r2_hidden(D_24,A_6)
      | ~ r2_hidden(C_21,D_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_141,plain,(
    ! [C_54] :
      ( r2_hidden(C_54,k3_tarski('#skF_7'))
      | ~ r2_hidden(C_54,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_127,c_8])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_207,plain,(
    ! [A_65] :
      ( r1_tarski(A_65,k3_tarski('#skF_7'))
      | ~ r2_hidden('#skF_1'(A_65,k3_tarski('#skF_7')),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_141,c_4])).

tff(c_212,plain,(
    r1_tarski('#skF_8',k3_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_6,c_207])).

tff(c_34,plain,(
    ! [A_29,B_30] :
      ( v1_finset_1(A_29)
      | ~ v1_finset_1(B_30)
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_217,plain,
    ( v1_finset_1('#skF_8')
    | ~ v1_finset_1(k3_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_212,c_34])).

tff(c_221,plain,(
    v1_finset_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_217])).

tff(c_223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_221])).

tff(c_226,plain,(
    ! [B_66] :
      ( v1_finset_1(B_66)
      | ~ r2_hidden(B_66,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_230,plain,
    ( v1_finset_1('#skF_6'('#skF_9'))
    | v1_finset_1(k3_tarski('#skF_9'))
    | ~ v1_finset_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_32,c_226])).

tff(c_237,plain,
    ( v1_finset_1('#skF_6'('#skF_9'))
    | v1_finset_1(k3_tarski('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_230])).

tff(c_239,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_92,c_237])).

tff(c_240,plain,(
    ! [B_33] :
      ( v1_finset_1(B_33)
      | ~ r2_hidden(B_33,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_252,plain,
    ( v1_finset_1('#skF_6'('#skF_9'))
    | v1_finset_1(k3_tarski('#skF_9'))
    | ~ v1_finset_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_248,c_240])).

tff(c_255,plain,
    ( v1_finset_1('#skF_6'('#skF_9'))
    | v1_finset_1(k3_tarski('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_252])).

tff(c_257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_92,c_255])).

tff(c_258,plain,(
    ! [B_33] :
      ( v1_finset_1(B_33)
      | ~ r2_hidden(B_33,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_282,plain,
    ( v1_finset_1('#skF_6'('#skF_9'))
    | v1_finset_1(k3_tarski('#skF_9'))
    | ~ v1_finset_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_276,c_258])).

tff(c_286,plain,
    ( v1_finset_1('#skF_6'('#skF_9'))
    | v1_finset_1(k3_tarski('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_282])).

tff(c_288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_92,c_286])).

tff(c_290,plain,(
    v1_finset_1(k3_tarski('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_289,plain,(
    v1_finset_1(k3_tarski('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_292,plain,(
    ! [A_75,B_76] :
      ( v1_finset_1(A_75)
      | ~ v1_finset_1(B_76)
      | ~ r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_297,plain,(
    ! [A_77] :
      ( v1_finset_1(A_77)
      | ~ v1_finset_1(k1_zfmisc_1(k3_tarski(A_77))) ) ),
    inference(resolution,[status(thm)],[c_26,c_292])).

tff(c_303,plain,(
    ! [A_78] :
      ( v1_finset_1(A_78)
      | ~ v1_finset_1(k3_tarski(A_78)) ) ),
    inference(resolution,[status(thm)],[c_28,c_297])).

tff(c_312,plain,(
    v1_finset_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_289,c_303])).

tff(c_38,plain,
    ( ~ v1_finset_1('#skF_8')
    | ~ v1_finset_1('#skF_7')
    | ~ v1_finset_1(k3_tarski('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_314,plain,(
    ~ v1_finset_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_312,c_38])).

tff(c_40,plain,
    ( r2_hidden('#skF_8','#skF_7')
    | ~ v1_finset_1('#skF_7')
    | ~ v1_finset_1(k3_tarski('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_333,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_312,c_40])).

tff(c_363,plain,(
    ! [C_93,A_94,D_95] :
      ( r2_hidden(C_93,k3_tarski(A_94))
      | ~ r2_hidden(D_95,A_94)
      | ~ r2_hidden(C_93,D_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_379,plain,(
    ! [C_96] :
      ( r2_hidden(C_96,k3_tarski('#skF_7'))
      | ~ r2_hidden(C_96,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_333,c_363])).

tff(c_402,plain,(
    ! [A_99] :
      ( r1_tarski(A_99,k3_tarski('#skF_7'))
      | ~ r2_hidden('#skF_1'(A_99,k3_tarski('#skF_7')),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_379,c_4])).

tff(c_407,plain,(
    r1_tarski('#skF_8',k3_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_6,c_402])).

tff(c_412,plain,
    ( v1_finset_1('#skF_8')
    | ~ v1_finset_1(k3_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_407,c_34])).

tff(c_416,plain,(
    v1_finset_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_412])).

tff(c_418,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_314,c_416])).

tff(c_420,plain,(
    ~ v1_finset_1('#skF_9') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_50,plain,
    ( ~ v1_finset_1('#skF_8')
    | ~ v1_finset_1('#skF_7')
    | v1_finset_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_424,plain,
    ( ~ v1_finset_1('#skF_8')
    | ~ v1_finset_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_420,c_50])).

tff(c_425,plain,(
    ~ v1_finset_1('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_424])).

tff(c_419,plain,(
    v1_finset_1(k3_tarski('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_426,plain,(
    ! [A_102,B_103] :
      ( v1_finset_1(A_102)
      | ~ v1_finset_1(B_103)
      | ~ r1_tarski(A_102,B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_431,plain,(
    ! [A_104] :
      ( v1_finset_1(A_104)
      | ~ v1_finset_1(k1_zfmisc_1(k3_tarski(A_104))) ) ),
    inference(resolution,[status(thm)],[c_26,c_426])).

tff(c_436,plain,(
    ! [A_105] :
      ( v1_finset_1(A_105)
      | ~ v1_finset_1(k3_tarski(A_105)) ) ),
    inference(resolution,[status(thm)],[c_28,c_431])).

tff(c_439,plain,(
    v1_finset_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_419,c_436])).

tff(c_443,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_425,c_439])).

tff(c_444,plain,(
    ~ v1_finset_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_424])).

tff(c_445,plain,(
    v1_finset_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_424])).

tff(c_52,plain,
    ( r2_hidden('#skF_8','#skF_7')
    | ~ v1_finset_1('#skF_7')
    | v1_finset_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_447,plain,
    ( r2_hidden('#skF_8','#skF_7')
    | v1_finset_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_52])).

tff(c_448,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_420,c_447])).

tff(c_517,plain,(
    ! [C_124,A_125,D_126] :
      ( r2_hidden(C_124,k3_tarski(A_125))
      | ~ r2_hidden(D_126,A_125)
      | ~ r2_hidden(C_124,D_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_533,plain,(
    ! [C_127] :
      ( r2_hidden(C_127,k3_tarski('#skF_7'))
      | ~ r2_hidden(C_127,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_448,c_517])).

tff(c_585,plain,(
    ! [A_135] :
      ( r1_tarski(A_135,k3_tarski('#skF_7'))
      | ~ r2_hidden('#skF_1'(A_135,k3_tarski('#skF_7')),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_533,c_4])).

tff(c_590,plain,(
    r1_tarski('#skF_8',k3_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_6,c_585])).

tff(c_623,plain,
    ( v1_finset_1('#skF_8')
    | ~ v1_finset_1(k3_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_590,c_34])).

tff(c_627,plain,(
    v1_finset_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_623])).

tff(c_629,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_444,c_627])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:36:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.31  
% 2.63/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.31  %$ r2_hidden > r1_tarski > v1_finset_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_6 > #skF_4
% 2.63/1.31  
% 2.63/1.31  %Foreground sorts:
% 2.63/1.31  
% 2.63/1.31  
% 2.63/1.31  %Background operators:
% 2.63/1.31  
% 2.63/1.31  
% 2.63/1.31  %Foreground operators:
% 2.63/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.63/1.31  tff('#skF_7', type, '#skF_7': $i).
% 2.63/1.31  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.63/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.31  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.63/1.31  tff('#skF_9', type, '#skF_9': $i).
% 2.63/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.63/1.31  tff('#skF_8', type, '#skF_8': $i).
% 2.63/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.63/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.63/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.63/1.31  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 2.63/1.31  tff('#skF_6', type, '#skF_6': $i > $i).
% 2.63/1.31  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.63/1.31  
% 2.63/1.33  tff(f_73, negated_conjecture, ~(![A]: ((v1_finset_1(A) & (![B]: (r2_hidden(B, A) => v1_finset_1(B)))) <=> v1_finset_1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_finset_1)).
% 2.63/1.33  tff(f_57, axiom, (![A]: ((v1_finset_1(A) & (![B]: (r2_hidden(B, A) => v1_finset_1(B)))) => v1_finset_1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_finset_1)).
% 2.63/1.33  tff(f_48, axiom, (![A]: (v1_finset_1(A) => v1_finset_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc17_finset_1)).
% 2.63/1.33  tff(f_44, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 2.63/1.33  tff(f_63, axiom, (![A, B]: ((r1_tarski(A, B) & v1_finset_1(B)) => v1_finset_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_finset_1)).
% 2.63/1.33  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.63/1.33  tff(f_42, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 2.63/1.33  tff(c_36, plain, (v1_finset_1(k3_tarski('#skF_7')) | ~v1_finset_1(k3_tarski('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.63/1.33  tff(c_56, plain, (~v1_finset_1(k3_tarski('#skF_9'))), inference(splitLeft, [status(thm)], [c_36])).
% 2.63/1.33  tff(c_48, plain, (v1_finset_1(k3_tarski('#skF_7')) | v1_finset_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.63/1.33  tff(c_53, plain, (v1_finset_1('#skF_9')), inference(splitLeft, [status(thm)], [c_48])).
% 2.63/1.33  tff(c_82, plain, (![A_45]: (~v1_finset_1('#skF_6'(A_45)) | v1_finset_1(k3_tarski(A_45)) | ~v1_finset_1(A_45))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.63/1.33  tff(c_88, plain, (~v1_finset_1('#skF_6'('#skF_9')) | ~v1_finset_1('#skF_9')), inference(resolution, [status(thm)], [c_82, c_56])).
% 2.63/1.33  tff(c_92, plain, (~v1_finset_1('#skF_6'('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_88])).
% 2.63/1.33  tff(c_276, plain, (![A_74]: (r2_hidden('#skF_6'(A_74), A_74) | v1_finset_1(k3_tarski(A_74)) | ~v1_finset_1(A_74))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.63/1.33  tff(c_248, plain, (![A_68]: (r2_hidden('#skF_6'(A_68), A_68) | v1_finset_1(k3_tarski(A_68)) | ~v1_finset_1(A_68))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.63/1.33  tff(c_32, plain, (![A_27]: (r2_hidden('#skF_6'(A_27), A_27) | v1_finset_1(k3_tarski(A_27)) | ~v1_finset_1(A_27))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.63/1.33  tff(c_44, plain, (![B_33]: (~v1_finset_1('#skF_8') | ~v1_finset_1('#skF_7') | v1_finset_1(B_33) | ~r2_hidden(B_33, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.63/1.33  tff(c_94, plain, (~v1_finset_1('#skF_7')), inference(splitLeft, [status(thm)], [c_44])).
% 2.63/1.33  tff(c_42, plain, (![B_33]: (v1_finset_1(k3_tarski('#skF_7')) | v1_finset_1(B_33) | ~r2_hidden(B_33, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.63/1.33  tff(c_93, plain, (v1_finset_1(k3_tarski('#skF_7'))), inference(splitLeft, [status(thm)], [c_42])).
% 2.63/1.33  tff(c_28, plain, (![A_26]: (v1_finset_1(k1_zfmisc_1(A_26)) | ~v1_finset_1(A_26))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.63/1.33  tff(c_26, plain, (![A_25]: (r1_tarski(A_25, k1_zfmisc_1(k3_tarski(A_25))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.63/1.33  tff(c_58, plain, (![A_36, B_37]: (v1_finset_1(A_36) | ~v1_finset_1(B_37) | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.63/1.33  tff(c_63, plain, (![A_38]: (v1_finset_1(A_38) | ~v1_finset_1(k1_zfmisc_1(k3_tarski(A_38))))), inference(resolution, [status(thm)], [c_26, c_58])).
% 2.63/1.33  tff(c_67, plain, (![A_38]: (v1_finset_1(A_38) | ~v1_finset_1(k3_tarski(A_38)))), inference(resolution, [status(thm)], [c_28, c_63])).
% 2.63/1.33  tff(c_97, plain, (v1_finset_1('#skF_7')), inference(resolution, [status(thm)], [c_93, c_67])).
% 2.63/1.33  tff(c_101, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_97])).
% 2.63/1.33  tff(c_102, plain, (![B_33]: (~v1_finset_1('#skF_8') | v1_finset_1(B_33) | ~r2_hidden(B_33, '#skF_9'))), inference(splitRight, [status(thm)], [c_44])).
% 2.63/1.33  tff(c_109, plain, (~v1_finset_1('#skF_8')), inference(splitLeft, [status(thm)], [c_102])).
% 2.63/1.33  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.63/1.33  tff(c_103, plain, (v1_finset_1('#skF_7')), inference(splitRight, [status(thm)], [c_44])).
% 2.63/1.33  tff(c_46, plain, (![B_33]: (r2_hidden('#skF_8', '#skF_7') | ~v1_finset_1('#skF_7') | v1_finset_1(B_33) | ~r2_hidden(B_33, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.63/1.33  tff(c_126, plain, (![B_33]: (r2_hidden('#skF_8', '#skF_7') | v1_finset_1(B_33) | ~r2_hidden(B_33, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_46])).
% 2.63/1.33  tff(c_127, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitLeft, [status(thm)], [c_126])).
% 2.63/1.33  tff(c_8, plain, (![C_21, A_6, D_24]: (r2_hidden(C_21, k3_tarski(A_6)) | ~r2_hidden(D_24, A_6) | ~r2_hidden(C_21, D_24))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.63/1.33  tff(c_141, plain, (![C_54]: (r2_hidden(C_54, k3_tarski('#skF_7')) | ~r2_hidden(C_54, '#skF_8'))), inference(resolution, [status(thm)], [c_127, c_8])).
% 2.63/1.33  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.63/1.33  tff(c_207, plain, (![A_65]: (r1_tarski(A_65, k3_tarski('#skF_7')) | ~r2_hidden('#skF_1'(A_65, k3_tarski('#skF_7')), '#skF_8'))), inference(resolution, [status(thm)], [c_141, c_4])).
% 2.63/1.33  tff(c_212, plain, (r1_tarski('#skF_8', k3_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_6, c_207])).
% 2.63/1.33  tff(c_34, plain, (![A_29, B_30]: (v1_finset_1(A_29) | ~v1_finset_1(B_30) | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.63/1.33  tff(c_217, plain, (v1_finset_1('#skF_8') | ~v1_finset_1(k3_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_212, c_34])).
% 2.63/1.33  tff(c_221, plain, (v1_finset_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_217])).
% 2.63/1.33  tff(c_223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_221])).
% 2.63/1.33  tff(c_226, plain, (![B_66]: (v1_finset_1(B_66) | ~r2_hidden(B_66, '#skF_9'))), inference(splitRight, [status(thm)], [c_126])).
% 2.63/1.33  tff(c_230, plain, (v1_finset_1('#skF_6'('#skF_9')) | v1_finset_1(k3_tarski('#skF_9')) | ~v1_finset_1('#skF_9')), inference(resolution, [status(thm)], [c_32, c_226])).
% 2.63/1.33  tff(c_237, plain, (v1_finset_1('#skF_6'('#skF_9')) | v1_finset_1(k3_tarski('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_230])).
% 2.63/1.33  tff(c_239, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_92, c_237])).
% 2.63/1.33  tff(c_240, plain, (![B_33]: (v1_finset_1(B_33) | ~r2_hidden(B_33, '#skF_9'))), inference(splitRight, [status(thm)], [c_102])).
% 2.63/1.33  tff(c_252, plain, (v1_finset_1('#skF_6'('#skF_9')) | v1_finset_1(k3_tarski('#skF_9')) | ~v1_finset_1('#skF_9')), inference(resolution, [status(thm)], [c_248, c_240])).
% 2.63/1.33  tff(c_255, plain, (v1_finset_1('#skF_6'('#skF_9')) | v1_finset_1(k3_tarski('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_252])).
% 2.63/1.33  tff(c_257, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_92, c_255])).
% 2.63/1.33  tff(c_258, plain, (![B_33]: (v1_finset_1(B_33) | ~r2_hidden(B_33, '#skF_9'))), inference(splitRight, [status(thm)], [c_42])).
% 2.63/1.33  tff(c_282, plain, (v1_finset_1('#skF_6'('#skF_9')) | v1_finset_1(k3_tarski('#skF_9')) | ~v1_finset_1('#skF_9')), inference(resolution, [status(thm)], [c_276, c_258])).
% 2.63/1.33  tff(c_286, plain, (v1_finset_1('#skF_6'('#skF_9')) | v1_finset_1(k3_tarski('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_282])).
% 2.63/1.33  tff(c_288, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_92, c_286])).
% 2.63/1.33  tff(c_290, plain, (v1_finset_1(k3_tarski('#skF_9'))), inference(splitRight, [status(thm)], [c_36])).
% 2.63/1.33  tff(c_289, plain, (v1_finset_1(k3_tarski('#skF_7'))), inference(splitRight, [status(thm)], [c_36])).
% 2.63/1.33  tff(c_292, plain, (![A_75, B_76]: (v1_finset_1(A_75) | ~v1_finset_1(B_76) | ~r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.63/1.33  tff(c_297, plain, (![A_77]: (v1_finset_1(A_77) | ~v1_finset_1(k1_zfmisc_1(k3_tarski(A_77))))), inference(resolution, [status(thm)], [c_26, c_292])).
% 2.63/1.33  tff(c_303, plain, (![A_78]: (v1_finset_1(A_78) | ~v1_finset_1(k3_tarski(A_78)))), inference(resolution, [status(thm)], [c_28, c_297])).
% 2.63/1.33  tff(c_312, plain, (v1_finset_1('#skF_7')), inference(resolution, [status(thm)], [c_289, c_303])).
% 2.63/1.33  tff(c_38, plain, (~v1_finset_1('#skF_8') | ~v1_finset_1('#skF_7') | ~v1_finset_1(k3_tarski('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.63/1.33  tff(c_314, plain, (~v1_finset_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_290, c_312, c_38])).
% 2.63/1.33  tff(c_40, plain, (r2_hidden('#skF_8', '#skF_7') | ~v1_finset_1('#skF_7') | ~v1_finset_1(k3_tarski('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.63/1.33  tff(c_333, plain, (r2_hidden('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_290, c_312, c_40])).
% 2.63/1.33  tff(c_363, plain, (![C_93, A_94, D_95]: (r2_hidden(C_93, k3_tarski(A_94)) | ~r2_hidden(D_95, A_94) | ~r2_hidden(C_93, D_95))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.63/1.33  tff(c_379, plain, (![C_96]: (r2_hidden(C_96, k3_tarski('#skF_7')) | ~r2_hidden(C_96, '#skF_8'))), inference(resolution, [status(thm)], [c_333, c_363])).
% 2.63/1.33  tff(c_402, plain, (![A_99]: (r1_tarski(A_99, k3_tarski('#skF_7')) | ~r2_hidden('#skF_1'(A_99, k3_tarski('#skF_7')), '#skF_8'))), inference(resolution, [status(thm)], [c_379, c_4])).
% 2.63/1.33  tff(c_407, plain, (r1_tarski('#skF_8', k3_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_6, c_402])).
% 2.63/1.33  tff(c_412, plain, (v1_finset_1('#skF_8') | ~v1_finset_1(k3_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_407, c_34])).
% 2.63/1.33  tff(c_416, plain, (v1_finset_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_289, c_412])).
% 2.63/1.33  tff(c_418, plain, $false, inference(negUnitSimplification, [status(thm)], [c_314, c_416])).
% 2.63/1.33  tff(c_420, plain, (~v1_finset_1('#skF_9')), inference(splitRight, [status(thm)], [c_48])).
% 2.63/1.33  tff(c_50, plain, (~v1_finset_1('#skF_8') | ~v1_finset_1('#skF_7') | v1_finset_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.63/1.33  tff(c_424, plain, (~v1_finset_1('#skF_8') | ~v1_finset_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_420, c_50])).
% 2.63/1.33  tff(c_425, plain, (~v1_finset_1('#skF_7')), inference(splitLeft, [status(thm)], [c_424])).
% 2.63/1.33  tff(c_419, plain, (v1_finset_1(k3_tarski('#skF_7'))), inference(splitRight, [status(thm)], [c_48])).
% 2.63/1.33  tff(c_426, plain, (![A_102, B_103]: (v1_finset_1(A_102) | ~v1_finset_1(B_103) | ~r1_tarski(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.63/1.33  tff(c_431, plain, (![A_104]: (v1_finset_1(A_104) | ~v1_finset_1(k1_zfmisc_1(k3_tarski(A_104))))), inference(resolution, [status(thm)], [c_26, c_426])).
% 2.63/1.33  tff(c_436, plain, (![A_105]: (v1_finset_1(A_105) | ~v1_finset_1(k3_tarski(A_105)))), inference(resolution, [status(thm)], [c_28, c_431])).
% 2.63/1.33  tff(c_439, plain, (v1_finset_1('#skF_7')), inference(resolution, [status(thm)], [c_419, c_436])).
% 2.63/1.33  tff(c_443, plain, $false, inference(negUnitSimplification, [status(thm)], [c_425, c_439])).
% 2.63/1.33  tff(c_444, plain, (~v1_finset_1('#skF_8')), inference(splitRight, [status(thm)], [c_424])).
% 2.63/1.33  tff(c_445, plain, (v1_finset_1('#skF_7')), inference(splitRight, [status(thm)], [c_424])).
% 2.63/1.33  tff(c_52, plain, (r2_hidden('#skF_8', '#skF_7') | ~v1_finset_1('#skF_7') | v1_finset_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.63/1.33  tff(c_447, plain, (r2_hidden('#skF_8', '#skF_7') | v1_finset_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_445, c_52])).
% 2.63/1.33  tff(c_448, plain, (r2_hidden('#skF_8', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_420, c_447])).
% 2.63/1.33  tff(c_517, plain, (![C_124, A_125, D_126]: (r2_hidden(C_124, k3_tarski(A_125)) | ~r2_hidden(D_126, A_125) | ~r2_hidden(C_124, D_126))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.63/1.33  tff(c_533, plain, (![C_127]: (r2_hidden(C_127, k3_tarski('#skF_7')) | ~r2_hidden(C_127, '#skF_8'))), inference(resolution, [status(thm)], [c_448, c_517])).
% 2.63/1.33  tff(c_585, plain, (![A_135]: (r1_tarski(A_135, k3_tarski('#skF_7')) | ~r2_hidden('#skF_1'(A_135, k3_tarski('#skF_7')), '#skF_8'))), inference(resolution, [status(thm)], [c_533, c_4])).
% 2.63/1.33  tff(c_590, plain, (r1_tarski('#skF_8', k3_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_6, c_585])).
% 2.63/1.33  tff(c_623, plain, (v1_finset_1('#skF_8') | ~v1_finset_1(k3_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_590, c_34])).
% 2.63/1.33  tff(c_627, plain, (v1_finset_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_419, c_623])).
% 2.63/1.33  tff(c_629, plain, $false, inference(negUnitSimplification, [status(thm)], [c_444, c_627])).
% 2.63/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.33  
% 2.63/1.33  Inference rules
% 2.63/1.33  ----------------------
% 2.63/1.33  #Ref     : 0
% 2.63/1.33  #Sup     : 118
% 2.63/1.33  #Fact    : 0
% 2.63/1.33  #Define  : 0
% 2.63/1.33  #Split   : 8
% 2.63/1.33  #Chain   : 0
% 2.63/1.33  #Close   : 0
% 2.63/1.33  
% 2.63/1.33  Ordering : KBO
% 2.63/1.33  
% 2.63/1.33  Simplification rules
% 2.63/1.33  ----------------------
% 2.63/1.33  #Subsume      : 13
% 2.63/1.33  #Demod        : 32
% 2.63/1.33  #Tautology    : 19
% 2.63/1.33  #SimpNegUnit  : 10
% 2.63/1.33  #BackRed      : 0
% 2.63/1.33  
% 2.63/1.33  #Partial instantiations: 0
% 2.63/1.33  #Strategies tried      : 1
% 2.63/1.33  
% 2.63/1.33  Timing (in seconds)
% 2.63/1.33  ----------------------
% 2.63/1.33  Preprocessing        : 0.30
% 2.63/1.33  Parsing              : 0.17
% 2.63/1.33  CNF conversion       : 0.02
% 2.63/1.33  Main loop            : 0.32
% 2.63/1.33  Inferencing          : 0.12
% 2.63/1.33  Reduction            : 0.08
% 2.63/1.33  Demodulation         : 0.05
% 2.63/1.33  BG Simplification    : 0.02
% 2.63/1.33  Subsumption          : 0.07
% 2.63/1.33  Abstraction          : 0.01
% 2.63/1.33  MUC search           : 0.00
% 2.63/1.33  Cooper               : 0.00
% 2.63/1.33  Total                : 0.66
% 2.63/1.33  Index Insertion      : 0.00
% 2.63/1.33  Index Deletion       : 0.00
% 2.63/1.33  Index Matching       : 0.00
% 2.63/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
