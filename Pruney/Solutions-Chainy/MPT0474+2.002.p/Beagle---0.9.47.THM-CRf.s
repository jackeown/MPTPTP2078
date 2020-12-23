%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:27 EST 2020

% Result     : Theorem 5.15s
% Output     : CNFRefutation 5.52s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 951 expanded)
%              Number of leaves         :   29 ( 326 expanded)
%              Depth                    :   27
%              Number of atoms          :  259 (3073 expanded)
%              Number of equality atoms :   24 ( 106 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_tarski > #nlpp > k4_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_10 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( B = k4_relat_1(A)
          <=> ! [C,D] :
                ( r2_hidden(k4_tarski(C,D),B)
              <=> r2_hidden(k4_tarski(D,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_1)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( A = B
          <=> ! [C,D] :
                ( r2_hidden(k4_tarski(C,D),A)
              <=> r2_hidden(k4_tarski(C,D),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_relat_1)).

tff(c_42,plain,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_44,plain,(
    ! [A_57] :
      ( v1_relat_1(A_57)
      | ~ v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_48,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_44])).

tff(c_38,plain,(
    ! [A_54] :
      ( v1_relat_1(k4_relat_1(A_54))
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_40,plain,(
    ! [A_55] :
      ( k4_relat_1(k4_relat_1(A_55)) = A_55
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,(
    ! [A_20,B_30] :
      ( r2_hidden(k4_tarski('#skF_5'(A_20,B_30),'#skF_6'(A_20,B_30)),A_20)
      | r1_tarski(A_20,B_30)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_94,plain,(
    ! [D_72,C_73,A_74] :
      ( r2_hidden(k4_tarski(D_72,C_73),A_74)
      | ~ r2_hidden(k4_tarski(C_73,D_72),k4_relat_1(A_74))
      | ~ v1_relat_1(k4_relat_1(A_74))
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_145,plain,(
    ! [A_84,B_85] :
      ( r2_hidden(k4_tarski('#skF_6'(k4_relat_1(A_84),B_85),'#skF_5'(k4_relat_1(A_84),B_85)),A_84)
      | ~ v1_relat_1(A_84)
      | r1_tarski(k4_relat_1(A_84),B_85)
      | ~ v1_relat_1(k4_relat_1(A_84)) ) ),
    inference(resolution,[status(thm)],[c_24,c_94])).

tff(c_20,plain,(
    ! [C_35,D_36,B_30,A_20] :
      ( r2_hidden(k4_tarski(C_35,D_36),B_30)
      | ~ r2_hidden(k4_tarski(C_35,D_36),A_20)
      | ~ r1_tarski(A_20,B_30)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_245,plain,(
    ! [A_104,B_105,B_106] :
      ( r2_hidden(k4_tarski('#skF_6'(k4_relat_1(A_104),B_105),'#skF_5'(k4_relat_1(A_104),B_105)),B_106)
      | ~ r1_tarski(A_104,B_106)
      | ~ v1_relat_1(A_104)
      | r1_tarski(k4_relat_1(A_104),B_105)
      | ~ v1_relat_1(k4_relat_1(A_104)) ) ),
    inference(resolution,[status(thm)],[c_145,c_20])).

tff(c_82,plain,(
    ! [C_69,D_70,A_71] :
      ( r2_hidden(k4_tarski(C_69,D_70),k4_relat_1(A_71))
      | ~ r2_hidden(k4_tarski(D_70,C_69),A_71)
      | ~ v1_relat_1(k4_relat_1(A_71))
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22,plain,(
    ! [A_20,B_30] :
      ( ~ r2_hidden(k4_tarski('#skF_5'(A_20,B_30),'#skF_6'(A_20,B_30)),B_30)
      | r1_tarski(A_20,B_30)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_93,plain,(
    ! [A_20,A_71] :
      ( r1_tarski(A_20,k4_relat_1(A_71))
      | ~ v1_relat_1(A_20)
      | ~ r2_hidden(k4_tarski('#skF_6'(A_20,k4_relat_1(A_71)),'#skF_5'(A_20,k4_relat_1(A_71))),A_71)
      | ~ v1_relat_1(k4_relat_1(A_71))
      | ~ v1_relat_1(A_71) ) ),
    inference(resolution,[status(thm)],[c_82,c_22])).

tff(c_265,plain,(
    ! [B_107,A_108] :
      ( ~ v1_relat_1(k4_relat_1(B_107))
      | ~ v1_relat_1(B_107)
      | ~ r1_tarski(A_108,B_107)
      | ~ v1_relat_1(A_108)
      | r1_tarski(k4_relat_1(A_108),k4_relat_1(B_107))
      | ~ v1_relat_1(k4_relat_1(A_108)) ) ),
    inference(resolution,[status(thm)],[c_245,c_93])).

tff(c_321,plain,(
    ! [A_114,A_115] :
      ( ~ v1_relat_1(k4_relat_1(k4_relat_1(A_114)))
      | ~ v1_relat_1(k4_relat_1(A_114))
      | ~ r1_tarski(A_115,k4_relat_1(A_114))
      | ~ v1_relat_1(A_115)
      | r1_tarski(k4_relat_1(A_115),A_114)
      | ~ v1_relat_1(k4_relat_1(A_115))
      | ~ v1_relat_1(A_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_265])).

tff(c_330,plain,(
    ! [A_116,A_117] :
      ( ~ r1_tarski(A_116,k4_relat_1(A_117))
      | ~ v1_relat_1(A_116)
      | r1_tarski(k4_relat_1(A_116),A_117)
      | ~ v1_relat_1(k4_relat_1(A_116))
      | ~ v1_relat_1(A_117)
      | ~ v1_relat_1(k4_relat_1(A_117)) ) ),
    inference(resolution,[status(thm)],[c_38,c_321])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_77,plain,(
    ! [C_64,D_65,B_66,A_67] :
      ( r2_hidden(k4_tarski(C_64,D_65),B_66)
      | ~ r2_hidden(k4_tarski(C_64,D_65),A_67)
      | ~ r1_tarski(A_67,B_66)
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_107,plain,(
    ! [A_75,B_76,B_77] :
      ( r2_hidden(k4_tarski('#skF_5'(A_75,B_76),'#skF_6'(A_75,B_76)),B_77)
      | ~ r1_tarski(A_75,B_77)
      | r1_tarski(A_75,B_76)
      | ~ v1_relat_1(A_75) ) ),
    inference(resolution,[status(thm)],[c_24,c_77])).

tff(c_189,plain,(
    ! [A_90,B_91,B_92,B_93] :
      ( r2_hidden(k4_tarski('#skF_5'(A_90,B_91),'#skF_6'(A_90,B_91)),B_92)
      | ~ r1_tarski(B_93,B_92)
      | ~ v1_relat_1(B_93)
      | ~ r1_tarski(A_90,B_93)
      | r1_tarski(A_90,B_91)
      | ~ v1_relat_1(A_90) ) ),
    inference(resolution,[status(thm)],[c_107,c_20])).

tff(c_193,plain,(
    ! [A_90,B_91,A_1] :
      ( r2_hidden(k4_tarski('#skF_5'(A_90,B_91),'#skF_6'(A_90,B_91)),A_1)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ r1_tarski(A_90,k1_xboole_0)
      | r1_tarski(A_90,B_91)
      | ~ v1_relat_1(A_90) ) ),
    inference(resolution,[status(thm)],[c_4,c_189])).

tff(c_198,plain,(
    ! [A_94,B_95,A_96] :
      ( r2_hidden(k4_tarski('#skF_5'(A_94,B_95),'#skF_6'(A_94,B_95)),A_96)
      | ~ r1_tarski(A_94,k1_xboole_0)
      | r1_tarski(A_94,B_95)
      | ~ v1_relat_1(A_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_193])).

tff(c_211,plain,(
    ! [A_94,A_96] :
      ( ~ r1_tarski(A_94,k1_xboole_0)
      | r1_tarski(A_94,A_96)
      | ~ v1_relat_1(A_94) ) ),
    inference(resolution,[status(thm)],[c_198,c_22])).

tff(c_335,plain,(
    ! [A_116,A_96] :
      ( r1_tarski(k4_relat_1(A_116),A_96)
      | ~ r1_tarski(A_116,k4_relat_1(k1_xboole_0))
      | ~ v1_relat_1(A_116)
      | ~ v1_relat_1(k4_relat_1(A_116))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_330,c_211])).

tff(c_346,plain,(
    ! [A_116,A_96] :
      ( r1_tarski(k4_relat_1(A_116),A_96)
      | ~ r1_tarski(A_116,k4_relat_1(k1_xboole_0))
      | ~ v1_relat_1(A_116)
      | ~ v1_relat_1(k4_relat_1(A_116))
      | ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_335])).

tff(c_349,plain,(
    ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_346])).

tff(c_352,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_38,c_349])).

tff(c_356,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_352])).

tff(c_358,plain,(
    v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_346])).

tff(c_71,plain,(
    ! [A_62,B_63] :
      ( r2_hidden(k4_tarski('#skF_5'(A_62,B_63),'#skF_6'(A_62,B_63)),A_62)
      | r1_tarski(A_62,B_63)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_76,plain,(
    ! [A_62] :
      ( r1_tarski(A_62,A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(resolution,[status(thm)],[c_71,c_22])).

tff(c_357,plain,(
    ! [A_116,A_96] :
      ( r1_tarski(k4_relat_1(A_116),A_96)
      | ~ r1_tarski(A_116,k4_relat_1(k1_xboole_0))
      | ~ v1_relat_1(A_116)
      | ~ v1_relat_1(k4_relat_1(A_116)) ) ),
    inference(splitRight,[status(thm)],[c_346])).

tff(c_376,plain,(
    ! [A_120,A_121] :
      ( r1_tarski(k4_relat_1(A_120),A_121)
      | ~ r1_tarski(A_120,k4_relat_1(k1_xboole_0))
      | ~ v1_relat_1(A_120)
      | ~ v1_relat_1(k4_relat_1(A_120)) ) ),
    inference(splitRight,[status(thm)],[c_346])).

tff(c_393,plain,(
    ! [A_122,A_123] :
      ( r1_tarski(A_122,A_123)
      | ~ r1_tarski(k4_relat_1(A_122),k4_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k4_relat_1(A_122))
      | ~ v1_relat_1(k4_relat_1(k4_relat_1(A_122)))
      | ~ v1_relat_1(A_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_376])).

tff(c_423,plain,(
    ! [A_126,A_127] :
      ( r1_tarski(A_126,A_127)
      | ~ v1_relat_1(k4_relat_1(k4_relat_1(A_126)))
      | ~ r1_tarski(A_126,k4_relat_1(k1_xboole_0))
      | ~ v1_relat_1(A_126)
      | ~ v1_relat_1(k4_relat_1(A_126)) ) ),
    inference(resolution,[status(thm)],[c_357,c_393])).

tff(c_432,plain,(
    ! [A_128,A_129] :
      ( r1_tarski(A_128,A_129)
      | ~ r1_tarski(A_128,k4_relat_1(k1_xboole_0))
      | ~ v1_relat_1(A_128)
      | ~ v1_relat_1(k4_relat_1(A_128)) ) ),
    inference(resolution,[status(thm)],[c_38,c_423])).

tff(c_444,plain,(
    ! [A_129] :
      ( r1_tarski(k4_relat_1(k1_xboole_0),A_129)
      | ~ v1_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0)))
      | ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_76,c_432])).

tff(c_457,plain,(
    ! [A_129] :
      ( r1_tarski(k4_relat_1(k1_xboole_0),A_129)
      | ~ v1_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_444])).

tff(c_461,plain,(
    ~ v1_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0))) ),
    inference(splitLeft,[status(thm)],[c_457])).

tff(c_464,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_461])).

tff(c_470,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_464])).

tff(c_471,plain,(
    ! [A_129] : r1_tarski(k4_relat_1(k1_xboole_0),A_129) ),
    inference(splitRight,[status(thm)],[c_457])).

tff(c_128,plain,(
    ! [A_82,B_83] :
      ( r2_hidden(k4_tarski('#skF_1'(A_82,B_83),'#skF_2'(A_82,B_83)),B_83)
      | r2_hidden(k4_tarski('#skF_3'(A_82,B_83),'#skF_4'(A_82,B_83)),A_82)
      | B_83 = A_82
      | ~ v1_relat_1(B_83)
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_647,plain,(
    ! [A_146,B_147,B_148] :
      ( r2_hidden(k4_tarski('#skF_3'(A_146,B_147),'#skF_4'(A_146,B_147)),B_148)
      | ~ r1_tarski(A_146,B_148)
      | r2_hidden(k4_tarski('#skF_1'(A_146,B_147),'#skF_2'(A_146,B_147)),B_147)
      | B_147 = A_146
      | ~ v1_relat_1(B_147)
      | ~ v1_relat_1(A_146) ) ),
    inference(resolution,[status(thm)],[c_128,c_20])).

tff(c_10,plain,(
    ! [A_3,B_13] :
      ( r2_hidden(k4_tarski('#skF_1'(A_3,B_13),'#skF_2'(A_3,B_13)),B_13)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_3,B_13),'#skF_4'(A_3,B_13)),B_13)
      | B_13 = A_3
      | ~ v1_relat_1(B_13)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_678,plain,(
    ! [A_149,B_150] :
      ( ~ r1_tarski(A_149,B_150)
      | r2_hidden(k4_tarski('#skF_1'(A_149,B_150),'#skF_2'(A_149,B_150)),B_150)
      | B_150 = A_149
      | ~ v1_relat_1(B_150)
      | ~ v1_relat_1(A_149) ) ),
    inference(resolution,[status(thm)],[c_647,c_10])).

tff(c_473,plain,(
    ! [A_130] : r1_tarski(k4_relat_1(k1_xboole_0),A_130) ),
    inference(splitRight,[status(thm)],[c_457])).

tff(c_92,plain,(
    ! [C_69,D_70,B_30,A_71] :
      ( r2_hidden(k4_tarski(C_69,D_70),B_30)
      | ~ r1_tarski(k4_relat_1(A_71),B_30)
      | ~ r2_hidden(k4_tarski(D_70,C_69),A_71)
      | ~ v1_relat_1(k4_relat_1(A_71))
      | ~ v1_relat_1(A_71) ) ),
    inference(resolution,[status(thm)],[c_82,c_20])).

tff(c_488,plain,(
    ! [C_69,D_70,A_130] :
      ( r2_hidden(k4_tarski(C_69,D_70),A_130)
      | ~ r2_hidden(k4_tarski(D_70,C_69),k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_473,c_92])).

tff(c_506,plain,(
    ! [C_69,D_70,A_130] :
      ( r2_hidden(k4_tarski(C_69,D_70),A_130)
      | ~ r2_hidden(k4_tarski(D_70,C_69),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_358,c_488])).

tff(c_681,plain,(
    ! [A_149,A_130] :
      ( r2_hidden(k4_tarski('#skF_2'(A_149,k1_xboole_0),'#skF_1'(A_149,k1_xboole_0)),A_130)
      | ~ r1_tarski(A_149,k1_xboole_0)
      | k1_xboole_0 = A_149
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_149) ) ),
    inference(resolution,[status(thm)],[c_678,c_506])).

tff(c_698,plain,(
    ! [A_151,A_152] :
      ( r2_hidden(k4_tarski('#skF_2'(A_151,k1_xboole_0),'#skF_1'(A_151,k1_xboole_0)),A_152)
      | ~ r1_tarski(A_151,k1_xboole_0)
      | k1_xboole_0 = A_151
      | ~ v1_relat_1(A_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_681])).

tff(c_708,plain,(
    ! [A_151,A_130] :
      ( r2_hidden(k4_tarski('#skF_1'(A_151,k1_xboole_0),'#skF_2'(A_151,k1_xboole_0)),A_130)
      | ~ r1_tarski(A_151,k1_xboole_0)
      | k1_xboole_0 = A_151
      | ~ v1_relat_1(A_151) ) ),
    inference(resolution,[status(thm)],[c_698,c_506])).

tff(c_288,plain,(
    ! [A_111,B_112] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_111,B_112),'#skF_2'(A_111,B_112)),A_111)
      | r2_hidden(k4_tarski('#skF_3'(A_111,B_112),'#skF_4'(A_111,B_112)),A_111)
      | B_112 = A_111
      | ~ v1_relat_1(B_112)
      | ~ v1_relat_1(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1256,plain,(
    ! [A_179,B_180,B_181] :
      ( r2_hidden(k4_tarski('#skF_3'(A_179,B_180),'#skF_4'(A_179,B_180)),B_181)
      | ~ r1_tarski(A_179,B_181)
      | ~ r2_hidden(k4_tarski('#skF_1'(A_179,B_180),'#skF_2'(A_179,B_180)),A_179)
      | B_180 = A_179
      | ~ v1_relat_1(B_180)
      | ~ v1_relat_1(A_179) ) ),
    inference(resolution,[status(thm)],[c_288,c_20])).

tff(c_1260,plain,(
    ! [A_130,B_181] :
      ( r2_hidden(k4_tarski('#skF_3'(A_130,k1_xboole_0),'#skF_4'(A_130,k1_xboole_0)),B_181)
      | ~ r1_tarski(A_130,B_181)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ r1_tarski(A_130,k1_xboole_0)
      | k1_xboole_0 = A_130
      | ~ v1_relat_1(A_130) ) ),
    inference(resolution,[status(thm)],[c_708,c_1256])).

tff(c_3039,plain,(
    ! [A_230,B_231] :
      ( r2_hidden(k4_tarski('#skF_3'(A_230,k1_xboole_0),'#skF_4'(A_230,k1_xboole_0)),B_231)
      | ~ r1_tarski(A_230,B_231)
      | ~ r1_tarski(A_230,k1_xboole_0)
      | k1_xboole_0 = A_230
      | ~ v1_relat_1(A_230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1260])).

tff(c_711,plain,(
    ! [A_153,B_154,B_155] :
      ( r2_hidden(k4_tarski('#skF_1'(A_153,B_154),'#skF_2'(A_153,B_154)),B_155)
      | ~ r1_tarski(B_154,B_155)
      | ~ r1_tarski(A_153,B_154)
      | B_154 = A_153
      | ~ v1_relat_1(B_154)
      | ~ v1_relat_1(A_153) ) ),
    inference(resolution,[status(thm)],[c_678,c_20])).

tff(c_8,plain,(
    ! [A_3,B_13] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_3,B_13),'#skF_2'(A_3,B_13)),A_3)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_3,B_13),'#skF_4'(A_3,B_13)),B_13)
      | B_13 = A_3
      | ~ v1_relat_1(B_13)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_725,plain,(
    ! [B_155,B_154] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(B_155,B_154),'#skF_4'(B_155,B_154)),B_154)
      | ~ r1_tarski(B_154,B_155)
      | ~ r1_tarski(B_155,B_154)
      | B_155 = B_154
      | ~ v1_relat_1(B_154)
      | ~ v1_relat_1(B_155) ) ),
    inference(resolution,[status(thm)],[c_711,c_8])).

tff(c_3077,plain,(
    ! [A_230] :
      ( ~ r1_tarski(k1_xboole_0,A_230)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ r1_tarski(A_230,k1_xboole_0)
      | k1_xboole_0 = A_230
      | ~ v1_relat_1(A_230) ) ),
    inference(resolution,[status(thm)],[c_3039,c_725])).

tff(c_3117,plain,(
    ! [A_232] :
      ( ~ r1_tarski(A_232,k1_xboole_0)
      | k1_xboole_0 = A_232
      | ~ v1_relat_1(A_232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4,c_3077])).

tff(c_3153,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_471,c_3117])).

tff(c_3190,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_3153])).

tff(c_3192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_3190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n008.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 12:57:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.15/2.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.15/2.05  
% 5.15/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.15/2.06  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_tarski > #nlpp > k4_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_10 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_4
% 5.15/2.06  
% 5.15/2.06  %Foreground sorts:
% 5.15/2.06  
% 5.15/2.06  
% 5.15/2.06  %Background operators:
% 5.15/2.06  
% 5.15/2.06  
% 5.15/2.06  %Foreground operators:
% 5.15/2.06  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.15/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.15/2.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.15/2.06  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.15/2.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.15/2.06  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.15/2.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.15/2.06  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 5.15/2.06  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 5.15/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.15/2.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.15/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.15/2.06  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.15/2.06  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 5.15/2.06  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.15/2.06  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.15/2.06  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 5.15/2.06  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.15/2.06  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 5.15/2.06  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.15/2.06  
% 5.52/2.07  tff(f_76, negated_conjecture, ~(k4_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_relat_1)).
% 5.52/2.07  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.52/2.07  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 5.52/2.07  tff(f_70, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 5.52/2.07  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 5.52/2.07  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 5.52/2.07  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => ((B = k4_relat_1(A)) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), B) <=> r2_hidden(k4_tarski(D, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_relat_1)).
% 5.52/2.07  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.52/2.07  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => ((A = B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) <=> r2_hidden(k4_tarski(C, D), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_relat_1)).
% 5.52/2.07  tff(c_42, plain, (k4_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.52/2.07  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.52/2.07  tff(c_44, plain, (![A_57]: (v1_relat_1(A_57) | ~v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.52/2.07  tff(c_48, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_44])).
% 5.52/2.07  tff(c_38, plain, (![A_54]: (v1_relat_1(k4_relat_1(A_54)) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.52/2.08  tff(c_40, plain, (![A_55]: (k4_relat_1(k4_relat_1(A_55))=A_55 | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.52/2.08  tff(c_24, plain, (![A_20, B_30]: (r2_hidden(k4_tarski('#skF_5'(A_20, B_30), '#skF_6'(A_20, B_30)), A_20) | r1_tarski(A_20, B_30) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.52/2.08  tff(c_94, plain, (![D_72, C_73, A_74]: (r2_hidden(k4_tarski(D_72, C_73), A_74) | ~r2_hidden(k4_tarski(C_73, D_72), k4_relat_1(A_74)) | ~v1_relat_1(k4_relat_1(A_74)) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.52/2.08  tff(c_145, plain, (![A_84, B_85]: (r2_hidden(k4_tarski('#skF_6'(k4_relat_1(A_84), B_85), '#skF_5'(k4_relat_1(A_84), B_85)), A_84) | ~v1_relat_1(A_84) | r1_tarski(k4_relat_1(A_84), B_85) | ~v1_relat_1(k4_relat_1(A_84)))), inference(resolution, [status(thm)], [c_24, c_94])).
% 5.52/2.08  tff(c_20, plain, (![C_35, D_36, B_30, A_20]: (r2_hidden(k4_tarski(C_35, D_36), B_30) | ~r2_hidden(k4_tarski(C_35, D_36), A_20) | ~r1_tarski(A_20, B_30) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.52/2.08  tff(c_245, plain, (![A_104, B_105, B_106]: (r2_hidden(k4_tarski('#skF_6'(k4_relat_1(A_104), B_105), '#skF_5'(k4_relat_1(A_104), B_105)), B_106) | ~r1_tarski(A_104, B_106) | ~v1_relat_1(A_104) | r1_tarski(k4_relat_1(A_104), B_105) | ~v1_relat_1(k4_relat_1(A_104)))), inference(resolution, [status(thm)], [c_145, c_20])).
% 5.52/2.08  tff(c_82, plain, (![C_69, D_70, A_71]: (r2_hidden(k4_tarski(C_69, D_70), k4_relat_1(A_71)) | ~r2_hidden(k4_tarski(D_70, C_69), A_71) | ~v1_relat_1(k4_relat_1(A_71)) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.52/2.08  tff(c_22, plain, (![A_20, B_30]: (~r2_hidden(k4_tarski('#skF_5'(A_20, B_30), '#skF_6'(A_20, B_30)), B_30) | r1_tarski(A_20, B_30) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.52/2.08  tff(c_93, plain, (![A_20, A_71]: (r1_tarski(A_20, k4_relat_1(A_71)) | ~v1_relat_1(A_20) | ~r2_hidden(k4_tarski('#skF_6'(A_20, k4_relat_1(A_71)), '#skF_5'(A_20, k4_relat_1(A_71))), A_71) | ~v1_relat_1(k4_relat_1(A_71)) | ~v1_relat_1(A_71))), inference(resolution, [status(thm)], [c_82, c_22])).
% 5.52/2.08  tff(c_265, plain, (![B_107, A_108]: (~v1_relat_1(k4_relat_1(B_107)) | ~v1_relat_1(B_107) | ~r1_tarski(A_108, B_107) | ~v1_relat_1(A_108) | r1_tarski(k4_relat_1(A_108), k4_relat_1(B_107)) | ~v1_relat_1(k4_relat_1(A_108)))), inference(resolution, [status(thm)], [c_245, c_93])).
% 5.52/2.08  tff(c_321, plain, (![A_114, A_115]: (~v1_relat_1(k4_relat_1(k4_relat_1(A_114))) | ~v1_relat_1(k4_relat_1(A_114)) | ~r1_tarski(A_115, k4_relat_1(A_114)) | ~v1_relat_1(A_115) | r1_tarski(k4_relat_1(A_115), A_114) | ~v1_relat_1(k4_relat_1(A_115)) | ~v1_relat_1(A_114))), inference(superposition, [status(thm), theory('equality')], [c_40, c_265])).
% 5.52/2.08  tff(c_330, plain, (![A_116, A_117]: (~r1_tarski(A_116, k4_relat_1(A_117)) | ~v1_relat_1(A_116) | r1_tarski(k4_relat_1(A_116), A_117) | ~v1_relat_1(k4_relat_1(A_116)) | ~v1_relat_1(A_117) | ~v1_relat_1(k4_relat_1(A_117)))), inference(resolution, [status(thm)], [c_38, c_321])).
% 5.52/2.08  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 5.52/2.08  tff(c_77, plain, (![C_64, D_65, B_66, A_67]: (r2_hidden(k4_tarski(C_64, D_65), B_66) | ~r2_hidden(k4_tarski(C_64, D_65), A_67) | ~r1_tarski(A_67, B_66) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.52/2.08  tff(c_107, plain, (![A_75, B_76, B_77]: (r2_hidden(k4_tarski('#skF_5'(A_75, B_76), '#skF_6'(A_75, B_76)), B_77) | ~r1_tarski(A_75, B_77) | r1_tarski(A_75, B_76) | ~v1_relat_1(A_75))), inference(resolution, [status(thm)], [c_24, c_77])).
% 5.52/2.08  tff(c_189, plain, (![A_90, B_91, B_92, B_93]: (r2_hidden(k4_tarski('#skF_5'(A_90, B_91), '#skF_6'(A_90, B_91)), B_92) | ~r1_tarski(B_93, B_92) | ~v1_relat_1(B_93) | ~r1_tarski(A_90, B_93) | r1_tarski(A_90, B_91) | ~v1_relat_1(A_90))), inference(resolution, [status(thm)], [c_107, c_20])).
% 5.52/2.08  tff(c_193, plain, (![A_90, B_91, A_1]: (r2_hidden(k4_tarski('#skF_5'(A_90, B_91), '#skF_6'(A_90, B_91)), A_1) | ~v1_relat_1(k1_xboole_0) | ~r1_tarski(A_90, k1_xboole_0) | r1_tarski(A_90, B_91) | ~v1_relat_1(A_90))), inference(resolution, [status(thm)], [c_4, c_189])).
% 5.52/2.08  tff(c_198, plain, (![A_94, B_95, A_96]: (r2_hidden(k4_tarski('#skF_5'(A_94, B_95), '#skF_6'(A_94, B_95)), A_96) | ~r1_tarski(A_94, k1_xboole_0) | r1_tarski(A_94, B_95) | ~v1_relat_1(A_94))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_193])).
% 5.52/2.08  tff(c_211, plain, (![A_94, A_96]: (~r1_tarski(A_94, k1_xboole_0) | r1_tarski(A_94, A_96) | ~v1_relat_1(A_94))), inference(resolution, [status(thm)], [c_198, c_22])).
% 5.52/2.08  tff(c_335, plain, (![A_116, A_96]: (r1_tarski(k4_relat_1(A_116), A_96) | ~r1_tarski(A_116, k4_relat_1(k1_xboole_0)) | ~v1_relat_1(A_116) | ~v1_relat_1(k4_relat_1(A_116)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_330, c_211])).
% 5.52/2.08  tff(c_346, plain, (![A_116, A_96]: (r1_tarski(k4_relat_1(A_116), A_96) | ~r1_tarski(A_116, k4_relat_1(k1_xboole_0)) | ~v1_relat_1(A_116) | ~v1_relat_1(k4_relat_1(A_116)) | ~v1_relat_1(k4_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_335])).
% 5.52/2.08  tff(c_349, plain, (~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_346])).
% 5.52/2.08  tff(c_352, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_349])).
% 5.52/2.08  tff(c_356, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_352])).
% 5.52/2.08  tff(c_358, plain, (v1_relat_1(k4_relat_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_346])).
% 5.52/2.08  tff(c_71, plain, (![A_62, B_63]: (r2_hidden(k4_tarski('#skF_5'(A_62, B_63), '#skF_6'(A_62, B_63)), A_62) | r1_tarski(A_62, B_63) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.52/2.08  tff(c_76, plain, (![A_62]: (r1_tarski(A_62, A_62) | ~v1_relat_1(A_62))), inference(resolution, [status(thm)], [c_71, c_22])).
% 5.52/2.08  tff(c_357, plain, (![A_116, A_96]: (r1_tarski(k4_relat_1(A_116), A_96) | ~r1_tarski(A_116, k4_relat_1(k1_xboole_0)) | ~v1_relat_1(A_116) | ~v1_relat_1(k4_relat_1(A_116)))), inference(splitRight, [status(thm)], [c_346])).
% 5.52/2.08  tff(c_376, plain, (![A_120, A_121]: (r1_tarski(k4_relat_1(A_120), A_121) | ~r1_tarski(A_120, k4_relat_1(k1_xboole_0)) | ~v1_relat_1(A_120) | ~v1_relat_1(k4_relat_1(A_120)))), inference(splitRight, [status(thm)], [c_346])).
% 5.52/2.08  tff(c_393, plain, (![A_122, A_123]: (r1_tarski(A_122, A_123) | ~r1_tarski(k4_relat_1(A_122), k4_relat_1(k1_xboole_0)) | ~v1_relat_1(k4_relat_1(A_122)) | ~v1_relat_1(k4_relat_1(k4_relat_1(A_122))) | ~v1_relat_1(A_122))), inference(superposition, [status(thm), theory('equality')], [c_40, c_376])).
% 5.52/2.08  tff(c_423, plain, (![A_126, A_127]: (r1_tarski(A_126, A_127) | ~v1_relat_1(k4_relat_1(k4_relat_1(A_126))) | ~r1_tarski(A_126, k4_relat_1(k1_xboole_0)) | ~v1_relat_1(A_126) | ~v1_relat_1(k4_relat_1(A_126)))), inference(resolution, [status(thm)], [c_357, c_393])).
% 5.52/2.08  tff(c_432, plain, (![A_128, A_129]: (r1_tarski(A_128, A_129) | ~r1_tarski(A_128, k4_relat_1(k1_xboole_0)) | ~v1_relat_1(A_128) | ~v1_relat_1(k4_relat_1(A_128)))), inference(resolution, [status(thm)], [c_38, c_423])).
% 5.52/2.08  tff(c_444, plain, (![A_129]: (r1_tarski(k4_relat_1(k1_xboole_0), A_129) | ~v1_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0))) | ~v1_relat_1(k4_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_76, c_432])).
% 5.52/2.08  tff(c_457, plain, (![A_129]: (r1_tarski(k4_relat_1(k1_xboole_0), A_129) | ~v1_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0))))), inference(demodulation, [status(thm), theory('equality')], [c_358, c_444])).
% 5.52/2.08  tff(c_461, plain, (~v1_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0)))), inference(splitLeft, [status(thm)], [c_457])).
% 5.52/2.08  tff(c_464, plain, (~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40, c_461])).
% 5.52/2.08  tff(c_470, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_464])).
% 5.52/2.08  tff(c_471, plain, (![A_129]: (r1_tarski(k4_relat_1(k1_xboole_0), A_129))), inference(splitRight, [status(thm)], [c_457])).
% 5.52/2.08  tff(c_128, plain, (![A_82, B_83]: (r2_hidden(k4_tarski('#skF_1'(A_82, B_83), '#skF_2'(A_82, B_83)), B_83) | r2_hidden(k4_tarski('#skF_3'(A_82, B_83), '#skF_4'(A_82, B_83)), A_82) | B_83=A_82 | ~v1_relat_1(B_83) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.52/2.08  tff(c_647, plain, (![A_146, B_147, B_148]: (r2_hidden(k4_tarski('#skF_3'(A_146, B_147), '#skF_4'(A_146, B_147)), B_148) | ~r1_tarski(A_146, B_148) | r2_hidden(k4_tarski('#skF_1'(A_146, B_147), '#skF_2'(A_146, B_147)), B_147) | B_147=A_146 | ~v1_relat_1(B_147) | ~v1_relat_1(A_146))), inference(resolution, [status(thm)], [c_128, c_20])).
% 5.52/2.08  tff(c_10, plain, (![A_3, B_13]: (r2_hidden(k4_tarski('#skF_1'(A_3, B_13), '#skF_2'(A_3, B_13)), B_13) | ~r2_hidden(k4_tarski('#skF_3'(A_3, B_13), '#skF_4'(A_3, B_13)), B_13) | B_13=A_3 | ~v1_relat_1(B_13) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.52/2.08  tff(c_678, plain, (![A_149, B_150]: (~r1_tarski(A_149, B_150) | r2_hidden(k4_tarski('#skF_1'(A_149, B_150), '#skF_2'(A_149, B_150)), B_150) | B_150=A_149 | ~v1_relat_1(B_150) | ~v1_relat_1(A_149))), inference(resolution, [status(thm)], [c_647, c_10])).
% 5.52/2.08  tff(c_473, plain, (![A_130]: (r1_tarski(k4_relat_1(k1_xboole_0), A_130))), inference(splitRight, [status(thm)], [c_457])).
% 5.52/2.08  tff(c_92, plain, (![C_69, D_70, B_30, A_71]: (r2_hidden(k4_tarski(C_69, D_70), B_30) | ~r1_tarski(k4_relat_1(A_71), B_30) | ~r2_hidden(k4_tarski(D_70, C_69), A_71) | ~v1_relat_1(k4_relat_1(A_71)) | ~v1_relat_1(A_71))), inference(resolution, [status(thm)], [c_82, c_20])).
% 5.52/2.08  tff(c_488, plain, (![C_69, D_70, A_130]: (r2_hidden(k4_tarski(C_69, D_70), A_130) | ~r2_hidden(k4_tarski(D_70, C_69), k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_473, c_92])).
% 5.52/2.08  tff(c_506, plain, (![C_69, D_70, A_130]: (r2_hidden(k4_tarski(C_69, D_70), A_130) | ~r2_hidden(k4_tarski(D_70, C_69), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_358, c_488])).
% 5.52/2.08  tff(c_681, plain, (![A_149, A_130]: (r2_hidden(k4_tarski('#skF_2'(A_149, k1_xboole_0), '#skF_1'(A_149, k1_xboole_0)), A_130) | ~r1_tarski(A_149, k1_xboole_0) | k1_xboole_0=A_149 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_149))), inference(resolution, [status(thm)], [c_678, c_506])).
% 5.52/2.08  tff(c_698, plain, (![A_151, A_152]: (r2_hidden(k4_tarski('#skF_2'(A_151, k1_xboole_0), '#skF_1'(A_151, k1_xboole_0)), A_152) | ~r1_tarski(A_151, k1_xboole_0) | k1_xboole_0=A_151 | ~v1_relat_1(A_151))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_681])).
% 5.52/2.08  tff(c_708, plain, (![A_151, A_130]: (r2_hidden(k4_tarski('#skF_1'(A_151, k1_xboole_0), '#skF_2'(A_151, k1_xboole_0)), A_130) | ~r1_tarski(A_151, k1_xboole_0) | k1_xboole_0=A_151 | ~v1_relat_1(A_151))), inference(resolution, [status(thm)], [c_698, c_506])).
% 5.52/2.08  tff(c_288, plain, (![A_111, B_112]: (~r2_hidden(k4_tarski('#skF_1'(A_111, B_112), '#skF_2'(A_111, B_112)), A_111) | r2_hidden(k4_tarski('#skF_3'(A_111, B_112), '#skF_4'(A_111, B_112)), A_111) | B_112=A_111 | ~v1_relat_1(B_112) | ~v1_relat_1(A_111))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.52/2.08  tff(c_1256, plain, (![A_179, B_180, B_181]: (r2_hidden(k4_tarski('#skF_3'(A_179, B_180), '#skF_4'(A_179, B_180)), B_181) | ~r1_tarski(A_179, B_181) | ~r2_hidden(k4_tarski('#skF_1'(A_179, B_180), '#skF_2'(A_179, B_180)), A_179) | B_180=A_179 | ~v1_relat_1(B_180) | ~v1_relat_1(A_179))), inference(resolution, [status(thm)], [c_288, c_20])).
% 5.52/2.08  tff(c_1260, plain, (![A_130, B_181]: (r2_hidden(k4_tarski('#skF_3'(A_130, k1_xboole_0), '#skF_4'(A_130, k1_xboole_0)), B_181) | ~r1_tarski(A_130, B_181) | ~v1_relat_1(k1_xboole_0) | ~r1_tarski(A_130, k1_xboole_0) | k1_xboole_0=A_130 | ~v1_relat_1(A_130))), inference(resolution, [status(thm)], [c_708, c_1256])).
% 5.52/2.08  tff(c_3039, plain, (![A_230, B_231]: (r2_hidden(k4_tarski('#skF_3'(A_230, k1_xboole_0), '#skF_4'(A_230, k1_xboole_0)), B_231) | ~r1_tarski(A_230, B_231) | ~r1_tarski(A_230, k1_xboole_0) | k1_xboole_0=A_230 | ~v1_relat_1(A_230))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1260])).
% 5.52/2.08  tff(c_711, plain, (![A_153, B_154, B_155]: (r2_hidden(k4_tarski('#skF_1'(A_153, B_154), '#skF_2'(A_153, B_154)), B_155) | ~r1_tarski(B_154, B_155) | ~r1_tarski(A_153, B_154) | B_154=A_153 | ~v1_relat_1(B_154) | ~v1_relat_1(A_153))), inference(resolution, [status(thm)], [c_678, c_20])).
% 5.52/2.08  tff(c_8, plain, (![A_3, B_13]: (~r2_hidden(k4_tarski('#skF_1'(A_3, B_13), '#skF_2'(A_3, B_13)), A_3) | ~r2_hidden(k4_tarski('#skF_3'(A_3, B_13), '#skF_4'(A_3, B_13)), B_13) | B_13=A_3 | ~v1_relat_1(B_13) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.52/2.08  tff(c_725, plain, (![B_155, B_154]: (~r2_hidden(k4_tarski('#skF_3'(B_155, B_154), '#skF_4'(B_155, B_154)), B_154) | ~r1_tarski(B_154, B_155) | ~r1_tarski(B_155, B_154) | B_155=B_154 | ~v1_relat_1(B_154) | ~v1_relat_1(B_155))), inference(resolution, [status(thm)], [c_711, c_8])).
% 5.52/2.08  tff(c_3077, plain, (![A_230]: (~r1_tarski(k1_xboole_0, A_230) | ~v1_relat_1(k1_xboole_0) | ~r1_tarski(A_230, k1_xboole_0) | k1_xboole_0=A_230 | ~v1_relat_1(A_230))), inference(resolution, [status(thm)], [c_3039, c_725])).
% 5.52/2.08  tff(c_3117, plain, (![A_232]: (~r1_tarski(A_232, k1_xboole_0) | k1_xboole_0=A_232 | ~v1_relat_1(A_232))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4, c_3077])).
% 5.52/2.08  tff(c_3153, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_471, c_3117])).
% 5.52/2.08  tff(c_3190, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_358, c_3153])).
% 5.52/2.08  tff(c_3192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_3190])).
% 5.52/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.52/2.08  
% 5.52/2.08  Inference rules
% 5.52/2.08  ----------------------
% 5.52/2.08  #Ref     : 0
% 5.52/2.08  #Sup     : 650
% 5.52/2.08  #Fact    : 0
% 5.52/2.08  #Define  : 0
% 5.52/2.08  #Split   : 6
% 5.52/2.08  #Chain   : 0
% 5.52/2.08  #Close   : 0
% 5.52/2.08  
% 5.52/2.08  Ordering : KBO
% 5.52/2.08  
% 5.52/2.08  Simplification rules
% 5.52/2.08  ----------------------
% 5.52/2.08  #Subsume      : 131
% 5.52/2.08  #Demod        : 466
% 5.52/2.08  #Tautology    : 115
% 5.52/2.08  #SimpNegUnit  : 1
% 5.52/2.08  #BackRed      : 0
% 5.52/2.08  
% 5.52/2.08  #Partial instantiations: 0
% 5.52/2.08  #Strategies tried      : 1
% 5.52/2.08  
% 5.52/2.08  Timing (in seconds)
% 5.52/2.08  ----------------------
% 5.52/2.08  Preprocessing        : 0.32
% 5.52/2.08  Parsing              : 0.16
% 5.52/2.08  CNF conversion       : 0.03
% 5.52/2.08  Main loop            : 0.94
% 5.52/2.08  Inferencing          : 0.27
% 5.52/2.08  Reduction            : 0.26
% 5.52/2.08  Demodulation         : 0.17
% 5.52/2.08  BG Simplification    : 0.04
% 5.52/2.08  Subsumption          : 0.32
% 5.52/2.08  Abstraction          : 0.04
% 5.52/2.08  MUC search           : 0.00
% 5.52/2.08  Cooper               : 0.00
% 5.52/2.08  Total                : 1.30
% 5.52/2.08  Index Insertion      : 0.00
% 5.52/2.08  Index Deletion       : 0.00
% 5.52/2.08  Index Matching       : 0.00
% 5.52/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
