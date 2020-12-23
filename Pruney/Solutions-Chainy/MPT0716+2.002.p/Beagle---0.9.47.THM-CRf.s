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
% DateTime   : Thu Dec  3 10:05:36 EST 2020

% Result     : Theorem 10.76s
% Output     : CNFRefutation 11.01s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 269 expanded)
%              Number of leaves         :   28 ( 104 expanded)
%              Depth                    :   13
%              Number of atoms          :  292 ( 869 expanded)
%              Number of equality atoms :    9 (  30 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k1_funct_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( r1_tarski(C,k1_relat_1(k5_relat_1(A,B)))
              <=> ( r1_tarski(C,k1_relat_1(A))
                  & r1_tarski(k9_relat_1(A,C),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( r2_hidden(D,k1_relat_1(A))
                & r2_hidden(k1_funct_1(A,D),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ! [D] :
          ( v1_relat_1(D)
         => ( ( r1_tarski(C,D)
              & r1_tarski(A,B) )
           => r1_tarski(k9_relat_1(C,A),k9_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).

tff(c_54,plain,
    ( r1_tarski('#skF_6',k1_relat_1('#skF_4'))
    | ~ r1_tarski(k9_relat_1('#skF_4','#skF_7'),k1_relat_1('#skF_5'))
    | ~ r1_tarski('#skF_7',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_119,plain,(
    ~ r1_tarski('#skF_7',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_48,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_44,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_60,plain,
    ( r1_tarski('#skF_6',k1_relat_1('#skF_4'))
    | r1_tarski('#skF_7',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_82,plain,(
    r1_tarski('#skF_7',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_18,plain,(
    ! [A_16,B_18] :
      ( k10_relat_1(A_16,k1_relat_1(B_18)) = k1_relat_1(k5_relat_1(A_16,B_18))
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_146,plain,(
    ! [D_63,A_64,B_65] :
      ( r2_hidden(D_63,k1_relat_1(A_64))
      | ~ r2_hidden(D_63,k10_relat_1(A_64,B_65))
      | ~ v1_funct_1(A_64)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_325,plain,(
    ! [A_96,B_97,B_98] :
      ( r2_hidden('#skF_1'(k10_relat_1(A_96,B_97),B_98),k1_relat_1(A_96))
      | ~ v1_funct_1(A_96)
      | ~ v1_relat_1(A_96)
      | r1_tarski(k10_relat_1(A_96,B_97),B_98) ) ),
    inference(resolution,[status(thm)],[c_6,c_146])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_337,plain,(
    ! [A_99,B_100] :
      ( ~ v1_funct_1(A_99)
      | ~ v1_relat_1(A_99)
      | r1_tarski(k10_relat_1(A_99,B_100),k1_relat_1(A_99)) ) ),
    inference(resolution,[status(thm)],[c_325,c_4])).

tff(c_378,plain,(
    ! [A_106,B_107] :
      ( ~ v1_funct_1(A_106)
      | ~ v1_relat_1(A_106)
      | r1_tarski(k1_relat_1(k5_relat_1(A_106,B_107)),k1_relat_1(A_106))
      | ~ v1_relat_1(B_107)
      | ~ v1_relat_1(A_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_337])).

tff(c_14,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(A_8,C_10)
      | ~ r1_tarski(B_9,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_488,plain,(
    ! [A_116,A_117,B_118] :
      ( r1_tarski(A_116,k1_relat_1(A_117))
      | ~ r1_tarski(A_116,k1_relat_1(k5_relat_1(A_117,B_118)))
      | ~ v1_funct_1(A_117)
      | ~ v1_relat_1(B_118)
      | ~ v1_relat_1(A_117) ) ),
    inference(resolution,[status(thm)],[c_378,c_14])).

tff(c_513,plain,
    ( r1_tarski('#skF_7',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_488])).

tff(c_530,plain,(
    r1_tarski('#skF_7',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_46,c_513])).

tff(c_532,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_530])).

tff(c_534,plain,(
    r1_tarski('#skF_7',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_634,plain,(
    ! [D_127,A_128,B_129] :
      ( r2_hidden(D_127,k1_relat_1(A_128))
      | ~ r2_hidden(D_127,k10_relat_1(A_128,B_129))
      | ~ v1_funct_1(A_128)
      | ~ v1_relat_1(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_816,plain,(
    ! [A_159,B_160,B_161] :
      ( r2_hidden('#skF_1'(k10_relat_1(A_159,B_160),B_161),k1_relat_1(A_159))
      | ~ v1_funct_1(A_159)
      | ~ v1_relat_1(A_159)
      | r1_tarski(k10_relat_1(A_159,B_160),B_161) ) ),
    inference(resolution,[status(thm)],[c_6,c_634])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2655,plain,(
    ! [A_320,B_321,B_322,B_323] :
      ( r2_hidden('#skF_1'(k10_relat_1(A_320,B_321),B_322),B_323)
      | ~ r1_tarski(k1_relat_1(A_320),B_323)
      | ~ v1_funct_1(A_320)
      | ~ v1_relat_1(A_320)
      | r1_tarski(k10_relat_1(A_320,B_321),B_322) ) ),
    inference(resolution,[status(thm)],[c_816,c_2])).

tff(c_2688,plain,(
    ! [A_324,B_325,B_326] :
      ( ~ r1_tarski(k1_relat_1(A_324),B_325)
      | ~ v1_funct_1(A_324)
      | ~ v1_relat_1(A_324)
      | r1_tarski(k10_relat_1(A_324,B_326),B_325) ) ),
    inference(resolution,[status(thm)],[c_2655,c_4])).

tff(c_2994,plain,(
    ! [A_339,B_340,B_341] :
      ( ~ r1_tarski(k1_relat_1(A_339),B_340)
      | ~ v1_funct_1(A_339)
      | ~ v1_relat_1(A_339)
      | r1_tarski(k1_relat_1(k5_relat_1(A_339,B_341)),B_340)
      | ~ v1_relat_1(B_341)
      | ~ v1_relat_1(A_339) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2688])).

tff(c_3381,plain,(
    ! [A_358,B_359,A_360,B_361] :
      ( r1_tarski(A_358,B_359)
      | ~ r1_tarski(A_358,k1_relat_1(k5_relat_1(A_360,B_361)))
      | ~ r1_tarski(k1_relat_1(A_360),B_359)
      | ~ v1_funct_1(A_360)
      | ~ v1_relat_1(B_361)
      | ~ v1_relat_1(A_360) ) ),
    inference(resolution,[status(thm)],[c_2994,c_14])).

tff(c_3451,plain,(
    ! [A_360,B_361,B_359] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_360,B_361)),B_359)
      | ~ r1_tarski(k1_relat_1(A_360),B_359)
      | ~ v1_funct_1(A_360)
      | ~ v1_relat_1(B_361)
      | ~ v1_relat_1(A_360) ) ),
    inference(resolution,[status(thm)],[c_12,c_3381])).

tff(c_601,plain,(
    ! [A_123,B_124] :
      ( k10_relat_1(A_123,k1_relat_1(B_124)) = k1_relat_1(k5_relat_1(A_123,B_124))
      | ~ v1_relat_1(B_124)
      | ~ v1_relat_1(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_38,plain,(
    ! [B_32,A_31] :
      ( r1_tarski(k9_relat_1(B_32,k10_relat_1(B_32,A_31)),A_31)
      | ~ v1_funct_1(B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1314,plain,(
    ! [A_204,B_205] :
      ( r1_tarski(k9_relat_1(A_204,k1_relat_1(k5_relat_1(A_204,B_205))),k1_relat_1(B_205))
      | ~ v1_funct_1(A_204)
      | ~ v1_relat_1(A_204)
      | ~ v1_relat_1(B_205)
      | ~ v1_relat_1(A_204) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_601,c_38])).

tff(c_40,plain,(
    ! [A_33,C_35,B_34] :
      ( r1_tarski(A_33,k10_relat_1(C_35,B_34))
      | ~ r1_tarski(k9_relat_1(C_35,A_33),B_34)
      | ~ r1_tarski(A_33,k1_relat_1(C_35))
      | ~ v1_funct_1(C_35)
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_9748,plain,(
    ! [A_620,B_621] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_620,B_621)),k10_relat_1(A_620,k1_relat_1(B_621)))
      | ~ r1_tarski(k1_relat_1(k5_relat_1(A_620,B_621)),k1_relat_1(A_620))
      | ~ v1_funct_1(A_620)
      | ~ v1_relat_1(B_621)
      | ~ v1_relat_1(A_620) ) ),
    inference(resolution,[status(thm)],[c_1314,c_40])).

tff(c_86,plain,(
    ! [A_50,C_51,B_52] :
      ( r1_tarski(A_50,C_51)
      | ~ r1_tarski(B_52,C_51)
      | ~ r1_tarski(A_50,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_93,plain,(
    ! [A_53] :
      ( r1_tarski(A_53,k1_relat_1(k5_relat_1('#skF_4','#skF_5')))
      | ~ r1_tarski(A_53,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_82,c_86])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_99,plain,(
    ! [A_53] :
      ( k1_relat_1(k5_relat_1('#skF_4','#skF_5')) = A_53
      | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_4','#skF_5')),A_53)
      | ~ r1_tarski(A_53,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_93,c_8])).

tff(c_9831,plain,
    ( k10_relat_1('#skF_4',k1_relat_1('#skF_5')) = k1_relat_1(k5_relat_1('#skF_4','#skF_5'))
    | ~ r1_tarski(k10_relat_1('#skF_4',k1_relat_1('#skF_5')),'#skF_7')
    | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_4','#skF_5')),k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_9748,c_99])).

tff(c_9892,plain,
    ( k10_relat_1('#skF_4',k1_relat_1('#skF_5')) = k1_relat_1(k5_relat_1('#skF_4','#skF_5'))
    | ~ r1_tarski(k10_relat_1('#skF_4',k1_relat_1('#skF_5')),'#skF_7')
    | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_4','#skF_5')),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_46,c_9831])).

tff(c_9900,plain,(
    ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_4','#skF_5')),k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_9892])).

tff(c_9906,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3451,c_9900])).

tff(c_9922,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_46,c_12,c_9906])).

tff(c_9924,plain,(
    r1_tarski(k1_relat_1(k5_relat_1('#skF_4','#skF_5')),k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_9892])).

tff(c_78,plain,(
    ! [C_47,B_48,A_49] :
      ( r2_hidden(C_47,B_48)
      | ~ r2_hidden(C_47,A_49)
      | ~ r1_tarski(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_107,plain,(
    ! [A_56,B_57,B_58] :
      ( r2_hidden('#skF_1'(A_56,B_57),B_58)
      | ~ r1_tarski(A_56,B_58)
      | r1_tarski(A_56,B_57) ) ),
    inference(resolution,[status(thm)],[c_6,c_78])).

tff(c_671,plain,(
    ! [A_136,B_137,B_138,B_139] :
      ( r2_hidden('#skF_1'(A_136,B_137),B_138)
      | ~ r1_tarski(B_139,B_138)
      | ~ r1_tarski(A_136,B_139)
      | r1_tarski(A_136,B_137) ) ),
    inference(resolution,[status(thm)],[c_107,c_2])).

tff(c_715,plain,(
    ! [A_143,B_144] :
      ( r2_hidden('#skF_1'(A_143,B_144),k1_relat_1(k5_relat_1('#skF_4','#skF_5')))
      | ~ r1_tarski(A_143,'#skF_7')
      | r1_tarski(A_143,B_144) ) ),
    inference(resolution,[status(thm)],[c_82,c_671])).

tff(c_722,plain,(
    ! [A_143,B_144,B_2] :
      ( r2_hidden('#skF_1'(A_143,B_144),B_2)
      | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_4','#skF_5')),B_2)
      | ~ r1_tarski(A_143,'#skF_7')
      | r1_tarski(A_143,B_144) ) ),
    inference(resolution,[status(thm)],[c_715,c_2])).

tff(c_9820,plain,(
    ! [A_143,B_144] :
      ( r2_hidden('#skF_1'(A_143,B_144),k10_relat_1('#skF_4',k1_relat_1('#skF_5')))
      | ~ r1_tarski(A_143,'#skF_7')
      | r1_tarski(A_143,B_144)
      | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_4','#skF_5')),k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_9748,c_722])).

tff(c_9886,plain,(
    ! [A_143,B_144] :
      ( r2_hidden('#skF_1'(A_143,B_144),k10_relat_1('#skF_4',k1_relat_1('#skF_5')))
      | ~ r1_tarski(A_143,'#skF_7')
      | r1_tarski(A_143,B_144)
      | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_4','#skF_5')),k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_46,c_9820])).

tff(c_12204,plain,(
    ! [A_682,B_683] :
      ( r2_hidden('#skF_1'(A_682,B_683),k10_relat_1('#skF_4',k1_relat_1('#skF_5')))
      | ~ r1_tarski(A_682,'#skF_7')
      | r1_tarski(A_682,B_683) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9924,c_9886])).

tff(c_12234,plain,(
    ! [A_684] :
      ( ~ r1_tarski(A_684,'#skF_7')
      | r1_tarski(A_684,k10_relat_1('#skF_4',k1_relat_1('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_12204,c_4])).

tff(c_779,plain,(
    ! [C_153,A_154,D_155,B_156] :
      ( r1_tarski(k9_relat_1(C_153,A_154),k9_relat_1(D_155,B_156))
      | ~ r1_tarski(A_154,B_156)
      | ~ r1_tarski(C_153,D_155)
      | ~ v1_relat_1(D_155)
      | ~ v1_relat_1(C_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_100,plain,(
    ! [B_54,A_55] :
      ( r1_tarski(k9_relat_1(B_54,k10_relat_1(B_54,A_55)),A_55)
      | ~ v1_funct_1(B_54)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_105,plain,(
    ! [A_8,A_55,B_54] :
      ( r1_tarski(A_8,A_55)
      | ~ r1_tarski(A_8,k9_relat_1(B_54,k10_relat_1(B_54,A_55)))
      | ~ v1_funct_1(B_54)
      | ~ v1_relat_1(B_54) ) ),
    inference(resolution,[status(thm)],[c_100,c_14])).

tff(c_798,plain,(
    ! [C_153,A_154,A_55,D_155] :
      ( r1_tarski(k9_relat_1(C_153,A_154),A_55)
      | ~ v1_funct_1(D_155)
      | ~ r1_tarski(A_154,k10_relat_1(D_155,A_55))
      | ~ r1_tarski(C_153,D_155)
      | ~ v1_relat_1(D_155)
      | ~ v1_relat_1(C_153) ) ),
    inference(resolution,[status(thm)],[c_779,c_105])).

tff(c_12360,plain,(
    ! [C_153,A_684] :
      ( r1_tarski(k9_relat_1(C_153,A_684),k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_4')
      | ~ r1_tarski(C_153,'#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(C_153)
      | ~ r1_tarski(A_684,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_12234,c_798])).

tff(c_12804,plain,(
    ! [C_689,A_690] :
      ( r1_tarski(k9_relat_1(C_689,A_690),k1_relat_1('#skF_5'))
      | ~ r1_tarski(C_689,'#skF_4')
      | ~ v1_relat_1(C_689)
      | ~ r1_tarski(A_690,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_12360])).

tff(c_533,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_7'),k1_relat_1('#skF_5'))
    | r1_tarski('#skF_6',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_560,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_7'),k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_533])).

tff(c_12840,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_12804,c_560])).

tff(c_12867,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_48,c_12,c_12840])).

tff(c_12869,plain,(
    r1_tarski(k9_relat_1('#skF_4','#skF_7'),k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_533])).

tff(c_50,plain,
    ( ~ r1_tarski('#skF_6',k1_relat_1(k5_relat_1('#skF_4','#skF_5')))
    | ~ r1_tarski(k9_relat_1('#skF_4','#skF_7'),k1_relat_1('#skF_5'))
    | ~ r1_tarski('#skF_7',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_12897,plain,(
    ~ r1_tarski('#skF_6',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_534,c_12869,c_50])).

tff(c_12868,plain,(
    r1_tarski('#skF_6',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_533])).

tff(c_52,plain,
    ( r1_tarski(k9_relat_1('#skF_4','#skF_6'),k1_relat_1('#skF_5'))
    | ~ r1_tarski(k9_relat_1('#skF_4','#skF_7'),k1_relat_1('#skF_5'))
    | ~ r1_tarski('#skF_7',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_535,plain,(
    ~ r1_tarski('#skF_7',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_543,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_534,c_535])).

tff(c_544,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_7'),k1_relat_1('#skF_5'))
    | r1_tarski(k9_relat_1('#skF_4','#skF_6'),k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_12974,plain,(
    r1_tarski(k9_relat_1('#skF_4','#skF_6'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12869,c_544])).

tff(c_13536,plain,(
    ! [A_759,C_760,B_761] :
      ( r1_tarski(A_759,k10_relat_1(C_760,B_761))
      | ~ r1_tarski(k9_relat_1(C_760,A_759),B_761)
      | ~ r1_tarski(A_759,k1_relat_1(C_760))
      | ~ v1_funct_1(C_760)
      | ~ v1_relat_1(C_760) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_13560,plain,
    ( r1_tarski('#skF_6',k10_relat_1('#skF_4',k1_relat_1('#skF_5')))
    | ~ r1_tarski('#skF_6',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12974,c_13536])).

tff(c_13592,plain,(
    r1_tarski('#skF_6',k10_relat_1('#skF_4',k1_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_12868,c_13560])).

tff(c_13620,plain,
    ( r1_tarski('#skF_6',k1_relat_1(k5_relat_1('#skF_4','#skF_5')))
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_13592])).

tff(c_13634,plain,(
    r1_tarski('#skF_6',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_13620])).

tff(c_13636,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12897,c_13634])).

tff(c_13638,plain,(
    ~ r1_tarski('#skF_7',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_56,plain,
    ( ~ r1_tarski('#skF_6',k1_relat_1(k5_relat_1('#skF_4','#skF_5')))
    | r1_tarski('#skF_7',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_13642,plain,(
    ~ r1_tarski('#skF_6',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_13638,c_56])).

tff(c_13637,plain,(
    r1_tarski('#skF_6',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_58,plain,
    ( r1_tarski(k9_relat_1('#skF_4','#skF_6'),k1_relat_1('#skF_5'))
    | r1_tarski('#skF_7',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_13711,plain,(
    r1_tarski(k9_relat_1('#skF_4','#skF_6'),k1_relat_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_13638,c_58])).

tff(c_14136,plain,(
    ! [A_846,C_847,B_848] :
      ( r1_tarski(A_846,k10_relat_1(C_847,B_848))
      | ~ r1_tarski(k9_relat_1(C_847,A_846),B_848)
      | ~ r1_tarski(A_846,k1_relat_1(C_847))
      | ~ v1_funct_1(C_847)
      | ~ v1_relat_1(C_847) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_14154,plain,
    ( r1_tarski('#skF_6',k10_relat_1('#skF_4',k1_relat_1('#skF_5')))
    | ~ r1_tarski('#skF_6',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_13711,c_14136])).

tff(c_14173,plain,(
    r1_tarski('#skF_6',k10_relat_1('#skF_4',k1_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_13637,c_14154])).

tff(c_14195,plain,
    ( r1_tarski('#skF_6',k1_relat_1(k5_relat_1('#skF_4','#skF_5')))
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_14173])).

tff(c_14207,plain,(
    r1_tarski('#skF_6',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_14195])).

tff(c_14209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13642,c_14207])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:48:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.76/4.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.76/4.13  
% 10.76/4.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.76/4.13  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k1_funct_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 10.76/4.13  
% 10.76/4.13  %Foreground sorts:
% 10.76/4.13  
% 10.76/4.13  
% 10.76/4.13  %Background operators:
% 10.76/4.13  
% 10.76/4.13  
% 10.76/4.13  %Foreground operators:
% 10.76/4.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.76/4.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.76/4.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.76/4.13  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.76/4.13  tff('#skF_7', type, '#skF_7': $i).
% 10.76/4.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.76/4.13  tff('#skF_5', type, '#skF_5': $i).
% 10.76/4.13  tff('#skF_6', type, '#skF_6': $i).
% 10.76/4.13  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 10.76/4.13  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.76/4.13  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.76/4.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.76/4.13  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 10.76/4.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.76/4.13  tff('#skF_4', type, '#skF_4': $i).
% 10.76/4.13  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.76/4.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.76/4.13  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.76/4.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.76/4.13  
% 11.01/4.15  tff(f_109, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (r1_tarski(C, k1_relat_1(k5_relat_1(A, B))) <=> (r1_tarski(C, k1_relat_1(A)) & r1_tarski(k9_relat_1(A, C), k1_relat_1(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_1)).
% 11.01/4.15  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 11.01/4.15  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 11.01/4.15  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, k1_relat_1(A)) & r2_hidden(k1_funct_1(A, D), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_funct_1)).
% 11.01/4.15  tff(f_44, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 11.01/4.15  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.01/4.15  tff(f_82, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 11.01/4.15  tff(f_92, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 11.01/4.15  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k9_relat_1(C, A), k9_relat_1(D, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_relat_1)).
% 11.01/4.15  tff(c_54, plain, (r1_tarski('#skF_6', k1_relat_1('#skF_4')) | ~r1_tarski(k9_relat_1('#skF_4', '#skF_7'), k1_relat_1('#skF_5')) | ~r1_tarski('#skF_7', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.01/4.15  tff(c_119, plain, (~r1_tarski('#skF_7', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_54])).
% 11.01/4.15  tff(c_48, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.01/4.15  tff(c_44, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.01/4.15  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.01/4.15  tff(c_60, plain, (r1_tarski('#skF_6', k1_relat_1('#skF_4')) | r1_tarski('#skF_7', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.01/4.15  tff(c_82, plain, (r1_tarski('#skF_7', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_60])).
% 11.01/4.15  tff(c_18, plain, (![A_16, B_18]: (k10_relat_1(A_16, k1_relat_1(B_18))=k1_relat_1(k5_relat_1(A_16, B_18)) | ~v1_relat_1(B_18) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.01/4.15  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.01/4.15  tff(c_146, plain, (![D_63, A_64, B_65]: (r2_hidden(D_63, k1_relat_1(A_64)) | ~r2_hidden(D_63, k10_relat_1(A_64, B_65)) | ~v1_funct_1(A_64) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.01/4.15  tff(c_325, plain, (![A_96, B_97, B_98]: (r2_hidden('#skF_1'(k10_relat_1(A_96, B_97), B_98), k1_relat_1(A_96)) | ~v1_funct_1(A_96) | ~v1_relat_1(A_96) | r1_tarski(k10_relat_1(A_96, B_97), B_98))), inference(resolution, [status(thm)], [c_6, c_146])).
% 11.01/4.15  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.01/4.15  tff(c_337, plain, (![A_99, B_100]: (~v1_funct_1(A_99) | ~v1_relat_1(A_99) | r1_tarski(k10_relat_1(A_99, B_100), k1_relat_1(A_99)))), inference(resolution, [status(thm)], [c_325, c_4])).
% 11.01/4.15  tff(c_378, plain, (![A_106, B_107]: (~v1_funct_1(A_106) | ~v1_relat_1(A_106) | r1_tarski(k1_relat_1(k5_relat_1(A_106, B_107)), k1_relat_1(A_106)) | ~v1_relat_1(B_107) | ~v1_relat_1(A_106))), inference(superposition, [status(thm), theory('equality')], [c_18, c_337])).
% 11.01/4.15  tff(c_14, plain, (![A_8, C_10, B_9]: (r1_tarski(A_8, C_10) | ~r1_tarski(B_9, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.01/4.15  tff(c_488, plain, (![A_116, A_117, B_118]: (r1_tarski(A_116, k1_relat_1(A_117)) | ~r1_tarski(A_116, k1_relat_1(k5_relat_1(A_117, B_118))) | ~v1_funct_1(A_117) | ~v1_relat_1(B_118) | ~v1_relat_1(A_117))), inference(resolution, [status(thm)], [c_378, c_14])).
% 11.01/4.15  tff(c_513, plain, (r1_tarski('#skF_7', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_82, c_488])).
% 11.01/4.15  tff(c_530, plain, (r1_tarski('#skF_7', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_46, c_513])).
% 11.01/4.15  tff(c_532, plain, $false, inference(negUnitSimplification, [status(thm)], [c_119, c_530])).
% 11.01/4.15  tff(c_534, plain, (r1_tarski('#skF_7', k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_54])).
% 11.01/4.15  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.01/4.15  tff(c_634, plain, (![D_127, A_128, B_129]: (r2_hidden(D_127, k1_relat_1(A_128)) | ~r2_hidden(D_127, k10_relat_1(A_128, B_129)) | ~v1_funct_1(A_128) | ~v1_relat_1(A_128))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.01/4.15  tff(c_816, plain, (![A_159, B_160, B_161]: (r2_hidden('#skF_1'(k10_relat_1(A_159, B_160), B_161), k1_relat_1(A_159)) | ~v1_funct_1(A_159) | ~v1_relat_1(A_159) | r1_tarski(k10_relat_1(A_159, B_160), B_161))), inference(resolution, [status(thm)], [c_6, c_634])).
% 11.01/4.15  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.01/4.15  tff(c_2655, plain, (![A_320, B_321, B_322, B_323]: (r2_hidden('#skF_1'(k10_relat_1(A_320, B_321), B_322), B_323) | ~r1_tarski(k1_relat_1(A_320), B_323) | ~v1_funct_1(A_320) | ~v1_relat_1(A_320) | r1_tarski(k10_relat_1(A_320, B_321), B_322))), inference(resolution, [status(thm)], [c_816, c_2])).
% 11.01/4.15  tff(c_2688, plain, (![A_324, B_325, B_326]: (~r1_tarski(k1_relat_1(A_324), B_325) | ~v1_funct_1(A_324) | ~v1_relat_1(A_324) | r1_tarski(k10_relat_1(A_324, B_326), B_325))), inference(resolution, [status(thm)], [c_2655, c_4])).
% 11.01/4.15  tff(c_2994, plain, (![A_339, B_340, B_341]: (~r1_tarski(k1_relat_1(A_339), B_340) | ~v1_funct_1(A_339) | ~v1_relat_1(A_339) | r1_tarski(k1_relat_1(k5_relat_1(A_339, B_341)), B_340) | ~v1_relat_1(B_341) | ~v1_relat_1(A_339))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2688])).
% 11.01/4.15  tff(c_3381, plain, (![A_358, B_359, A_360, B_361]: (r1_tarski(A_358, B_359) | ~r1_tarski(A_358, k1_relat_1(k5_relat_1(A_360, B_361))) | ~r1_tarski(k1_relat_1(A_360), B_359) | ~v1_funct_1(A_360) | ~v1_relat_1(B_361) | ~v1_relat_1(A_360))), inference(resolution, [status(thm)], [c_2994, c_14])).
% 11.01/4.15  tff(c_3451, plain, (![A_360, B_361, B_359]: (r1_tarski(k1_relat_1(k5_relat_1(A_360, B_361)), B_359) | ~r1_tarski(k1_relat_1(A_360), B_359) | ~v1_funct_1(A_360) | ~v1_relat_1(B_361) | ~v1_relat_1(A_360))), inference(resolution, [status(thm)], [c_12, c_3381])).
% 11.01/4.15  tff(c_601, plain, (![A_123, B_124]: (k10_relat_1(A_123, k1_relat_1(B_124))=k1_relat_1(k5_relat_1(A_123, B_124)) | ~v1_relat_1(B_124) | ~v1_relat_1(A_123))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.01/4.15  tff(c_38, plain, (![B_32, A_31]: (r1_tarski(k9_relat_1(B_32, k10_relat_1(B_32, A_31)), A_31) | ~v1_funct_1(B_32) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.01/4.15  tff(c_1314, plain, (![A_204, B_205]: (r1_tarski(k9_relat_1(A_204, k1_relat_1(k5_relat_1(A_204, B_205))), k1_relat_1(B_205)) | ~v1_funct_1(A_204) | ~v1_relat_1(A_204) | ~v1_relat_1(B_205) | ~v1_relat_1(A_204))), inference(superposition, [status(thm), theory('equality')], [c_601, c_38])).
% 11.01/4.15  tff(c_40, plain, (![A_33, C_35, B_34]: (r1_tarski(A_33, k10_relat_1(C_35, B_34)) | ~r1_tarski(k9_relat_1(C_35, A_33), B_34) | ~r1_tarski(A_33, k1_relat_1(C_35)) | ~v1_funct_1(C_35) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.01/4.15  tff(c_9748, plain, (![A_620, B_621]: (r1_tarski(k1_relat_1(k5_relat_1(A_620, B_621)), k10_relat_1(A_620, k1_relat_1(B_621))) | ~r1_tarski(k1_relat_1(k5_relat_1(A_620, B_621)), k1_relat_1(A_620)) | ~v1_funct_1(A_620) | ~v1_relat_1(B_621) | ~v1_relat_1(A_620))), inference(resolution, [status(thm)], [c_1314, c_40])).
% 11.01/4.15  tff(c_86, plain, (![A_50, C_51, B_52]: (r1_tarski(A_50, C_51) | ~r1_tarski(B_52, C_51) | ~r1_tarski(A_50, B_52))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.01/4.15  tff(c_93, plain, (![A_53]: (r1_tarski(A_53, k1_relat_1(k5_relat_1('#skF_4', '#skF_5'))) | ~r1_tarski(A_53, '#skF_7'))), inference(resolution, [status(thm)], [c_82, c_86])).
% 11.01/4.15  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.01/4.15  tff(c_99, plain, (![A_53]: (k1_relat_1(k5_relat_1('#skF_4', '#skF_5'))=A_53 | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_4', '#skF_5')), A_53) | ~r1_tarski(A_53, '#skF_7'))), inference(resolution, [status(thm)], [c_93, c_8])).
% 11.01/4.15  tff(c_9831, plain, (k10_relat_1('#skF_4', k1_relat_1('#skF_5'))=k1_relat_1(k5_relat_1('#skF_4', '#skF_5')) | ~r1_tarski(k10_relat_1('#skF_4', k1_relat_1('#skF_5')), '#skF_7') | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_4', '#skF_5')), k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_9748, c_99])).
% 11.01/4.15  tff(c_9892, plain, (k10_relat_1('#skF_4', k1_relat_1('#skF_5'))=k1_relat_1(k5_relat_1('#skF_4', '#skF_5')) | ~r1_tarski(k10_relat_1('#skF_4', k1_relat_1('#skF_5')), '#skF_7') | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_4', '#skF_5')), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_46, c_9831])).
% 11.01/4.15  tff(c_9900, plain, (~r1_tarski(k1_relat_1(k5_relat_1('#skF_4', '#skF_5')), k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_9892])).
% 11.01/4.15  tff(c_9906, plain, (~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_3451, c_9900])).
% 11.01/4.15  tff(c_9922, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_46, c_12, c_9906])).
% 11.01/4.15  tff(c_9924, plain, (r1_tarski(k1_relat_1(k5_relat_1('#skF_4', '#skF_5')), k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_9892])).
% 11.01/4.15  tff(c_78, plain, (![C_47, B_48, A_49]: (r2_hidden(C_47, B_48) | ~r2_hidden(C_47, A_49) | ~r1_tarski(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.01/4.15  tff(c_107, plain, (![A_56, B_57, B_58]: (r2_hidden('#skF_1'(A_56, B_57), B_58) | ~r1_tarski(A_56, B_58) | r1_tarski(A_56, B_57))), inference(resolution, [status(thm)], [c_6, c_78])).
% 11.01/4.15  tff(c_671, plain, (![A_136, B_137, B_138, B_139]: (r2_hidden('#skF_1'(A_136, B_137), B_138) | ~r1_tarski(B_139, B_138) | ~r1_tarski(A_136, B_139) | r1_tarski(A_136, B_137))), inference(resolution, [status(thm)], [c_107, c_2])).
% 11.01/4.15  tff(c_715, plain, (![A_143, B_144]: (r2_hidden('#skF_1'(A_143, B_144), k1_relat_1(k5_relat_1('#skF_4', '#skF_5'))) | ~r1_tarski(A_143, '#skF_7') | r1_tarski(A_143, B_144))), inference(resolution, [status(thm)], [c_82, c_671])).
% 11.01/4.15  tff(c_722, plain, (![A_143, B_144, B_2]: (r2_hidden('#skF_1'(A_143, B_144), B_2) | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_4', '#skF_5')), B_2) | ~r1_tarski(A_143, '#skF_7') | r1_tarski(A_143, B_144))), inference(resolution, [status(thm)], [c_715, c_2])).
% 11.01/4.15  tff(c_9820, plain, (![A_143, B_144]: (r2_hidden('#skF_1'(A_143, B_144), k10_relat_1('#skF_4', k1_relat_1('#skF_5'))) | ~r1_tarski(A_143, '#skF_7') | r1_tarski(A_143, B_144) | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_4', '#skF_5')), k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_9748, c_722])).
% 11.01/4.15  tff(c_9886, plain, (![A_143, B_144]: (r2_hidden('#skF_1'(A_143, B_144), k10_relat_1('#skF_4', k1_relat_1('#skF_5'))) | ~r1_tarski(A_143, '#skF_7') | r1_tarski(A_143, B_144) | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_4', '#skF_5')), k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_46, c_9820])).
% 11.01/4.15  tff(c_12204, plain, (![A_682, B_683]: (r2_hidden('#skF_1'(A_682, B_683), k10_relat_1('#skF_4', k1_relat_1('#skF_5'))) | ~r1_tarski(A_682, '#skF_7') | r1_tarski(A_682, B_683))), inference(demodulation, [status(thm), theory('equality')], [c_9924, c_9886])).
% 11.01/4.15  tff(c_12234, plain, (![A_684]: (~r1_tarski(A_684, '#skF_7') | r1_tarski(A_684, k10_relat_1('#skF_4', k1_relat_1('#skF_5'))))), inference(resolution, [status(thm)], [c_12204, c_4])).
% 11.01/4.15  tff(c_779, plain, (![C_153, A_154, D_155, B_156]: (r1_tarski(k9_relat_1(C_153, A_154), k9_relat_1(D_155, B_156)) | ~r1_tarski(A_154, B_156) | ~r1_tarski(C_153, D_155) | ~v1_relat_1(D_155) | ~v1_relat_1(C_153))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.01/4.15  tff(c_100, plain, (![B_54, A_55]: (r1_tarski(k9_relat_1(B_54, k10_relat_1(B_54, A_55)), A_55) | ~v1_funct_1(B_54) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.01/4.15  tff(c_105, plain, (![A_8, A_55, B_54]: (r1_tarski(A_8, A_55) | ~r1_tarski(A_8, k9_relat_1(B_54, k10_relat_1(B_54, A_55))) | ~v1_funct_1(B_54) | ~v1_relat_1(B_54))), inference(resolution, [status(thm)], [c_100, c_14])).
% 11.01/4.15  tff(c_798, plain, (![C_153, A_154, A_55, D_155]: (r1_tarski(k9_relat_1(C_153, A_154), A_55) | ~v1_funct_1(D_155) | ~r1_tarski(A_154, k10_relat_1(D_155, A_55)) | ~r1_tarski(C_153, D_155) | ~v1_relat_1(D_155) | ~v1_relat_1(C_153))), inference(resolution, [status(thm)], [c_779, c_105])).
% 11.01/4.15  tff(c_12360, plain, (![C_153, A_684]: (r1_tarski(k9_relat_1(C_153, A_684), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_4') | ~r1_tarski(C_153, '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(C_153) | ~r1_tarski(A_684, '#skF_7'))), inference(resolution, [status(thm)], [c_12234, c_798])).
% 11.01/4.15  tff(c_12804, plain, (![C_689, A_690]: (r1_tarski(k9_relat_1(C_689, A_690), k1_relat_1('#skF_5')) | ~r1_tarski(C_689, '#skF_4') | ~v1_relat_1(C_689) | ~r1_tarski(A_690, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_12360])).
% 11.01/4.15  tff(c_533, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_7'), k1_relat_1('#skF_5')) | r1_tarski('#skF_6', k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_54])).
% 11.01/4.15  tff(c_560, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_7'), k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_533])).
% 11.01/4.15  tff(c_12840, plain, (~r1_tarski('#skF_4', '#skF_4') | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_12804, c_560])).
% 11.01/4.15  tff(c_12867, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_48, c_12, c_12840])).
% 11.01/4.15  tff(c_12869, plain, (r1_tarski(k9_relat_1('#skF_4', '#skF_7'), k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_533])).
% 11.01/4.15  tff(c_50, plain, (~r1_tarski('#skF_6', k1_relat_1(k5_relat_1('#skF_4', '#skF_5'))) | ~r1_tarski(k9_relat_1('#skF_4', '#skF_7'), k1_relat_1('#skF_5')) | ~r1_tarski('#skF_7', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.01/4.15  tff(c_12897, plain, (~r1_tarski('#skF_6', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_534, c_12869, c_50])).
% 11.01/4.15  tff(c_12868, plain, (r1_tarski('#skF_6', k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_533])).
% 11.01/4.15  tff(c_52, plain, (r1_tarski(k9_relat_1('#skF_4', '#skF_6'), k1_relat_1('#skF_5')) | ~r1_tarski(k9_relat_1('#skF_4', '#skF_7'), k1_relat_1('#skF_5')) | ~r1_tarski('#skF_7', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.01/4.15  tff(c_535, plain, (~r1_tarski('#skF_7', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_52])).
% 11.01/4.15  tff(c_543, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_534, c_535])).
% 11.01/4.15  tff(c_544, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_7'), k1_relat_1('#skF_5')) | r1_tarski(k9_relat_1('#skF_4', '#skF_6'), k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_52])).
% 11.01/4.15  tff(c_12974, plain, (r1_tarski(k9_relat_1('#skF_4', '#skF_6'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_12869, c_544])).
% 11.01/4.15  tff(c_13536, plain, (![A_759, C_760, B_761]: (r1_tarski(A_759, k10_relat_1(C_760, B_761)) | ~r1_tarski(k9_relat_1(C_760, A_759), B_761) | ~r1_tarski(A_759, k1_relat_1(C_760)) | ~v1_funct_1(C_760) | ~v1_relat_1(C_760))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.01/4.15  tff(c_13560, plain, (r1_tarski('#skF_6', k10_relat_1('#skF_4', k1_relat_1('#skF_5'))) | ~r1_tarski('#skF_6', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12974, c_13536])).
% 11.01/4.15  tff(c_13592, plain, (r1_tarski('#skF_6', k10_relat_1('#skF_4', k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_12868, c_13560])).
% 11.01/4.15  tff(c_13620, plain, (r1_tarski('#skF_6', k1_relat_1(k5_relat_1('#skF_4', '#skF_5'))) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18, c_13592])).
% 11.01/4.15  tff(c_13634, plain, (r1_tarski('#skF_6', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_13620])).
% 11.01/4.15  tff(c_13636, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12897, c_13634])).
% 11.01/4.15  tff(c_13638, plain, (~r1_tarski('#skF_7', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_60])).
% 11.01/4.15  tff(c_56, plain, (~r1_tarski('#skF_6', k1_relat_1(k5_relat_1('#skF_4', '#skF_5'))) | r1_tarski('#skF_7', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.01/4.15  tff(c_13642, plain, (~r1_tarski('#skF_6', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_13638, c_56])).
% 11.01/4.15  tff(c_13637, plain, (r1_tarski('#skF_6', k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_60])).
% 11.01/4.15  tff(c_58, plain, (r1_tarski(k9_relat_1('#skF_4', '#skF_6'), k1_relat_1('#skF_5')) | r1_tarski('#skF_7', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.01/4.15  tff(c_13711, plain, (r1_tarski(k9_relat_1('#skF_4', '#skF_6'), k1_relat_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_13638, c_58])).
% 11.01/4.15  tff(c_14136, plain, (![A_846, C_847, B_848]: (r1_tarski(A_846, k10_relat_1(C_847, B_848)) | ~r1_tarski(k9_relat_1(C_847, A_846), B_848) | ~r1_tarski(A_846, k1_relat_1(C_847)) | ~v1_funct_1(C_847) | ~v1_relat_1(C_847))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.01/4.15  tff(c_14154, plain, (r1_tarski('#skF_6', k10_relat_1('#skF_4', k1_relat_1('#skF_5'))) | ~r1_tarski('#skF_6', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_13711, c_14136])).
% 11.01/4.15  tff(c_14173, plain, (r1_tarski('#skF_6', k10_relat_1('#skF_4', k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_13637, c_14154])).
% 11.01/4.15  tff(c_14195, plain, (r1_tarski('#skF_6', k1_relat_1(k5_relat_1('#skF_4', '#skF_5'))) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18, c_14173])).
% 11.01/4.15  tff(c_14207, plain, (r1_tarski('#skF_6', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_14195])).
% 11.01/4.15  tff(c_14209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13642, c_14207])).
% 11.01/4.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.01/4.15  
% 11.01/4.15  Inference rules
% 11.01/4.15  ----------------------
% 11.01/4.15  #Ref     : 0
% 11.01/4.15  #Sup     : 3624
% 11.01/4.15  #Fact    : 0
% 11.01/4.15  #Define  : 0
% 11.01/4.15  #Split   : 23
% 11.01/4.15  #Chain   : 0
% 11.01/4.15  #Close   : 0
% 11.01/4.15  
% 11.01/4.15  Ordering : KBO
% 11.01/4.15  
% 11.01/4.15  Simplification rules
% 11.01/4.15  ----------------------
% 11.01/4.15  #Subsume      : 1223
% 11.01/4.15  #Demod        : 788
% 11.01/4.15  #Tautology    : 168
% 11.01/4.15  #SimpNegUnit  : 7
% 11.01/4.15  #BackRed      : 0
% 11.01/4.15  
% 11.01/4.15  #Partial instantiations: 0
% 11.01/4.15  #Strategies tried      : 1
% 11.01/4.15  
% 11.01/4.15  Timing (in seconds)
% 11.01/4.15  ----------------------
% 11.01/4.16  Preprocessing        : 0.33
% 11.01/4.16  Parsing              : 0.17
% 11.01/4.16  CNF conversion       : 0.03
% 11.01/4.16  Main loop            : 3.01
% 11.01/4.16  Inferencing          : 0.66
% 11.01/4.16  Reduction            : 0.62
% 11.01/4.16  Demodulation         : 0.40
% 11.01/4.16  BG Simplification    : 0.08
% 11.01/4.16  Subsumption          : 1.45
% 11.01/4.16  Abstraction          : 0.12
% 11.01/4.16  MUC search           : 0.00
% 11.01/4.16  Cooper               : 0.00
% 11.01/4.16  Total                : 3.38
% 11.01/4.16  Index Insertion      : 0.00
% 11.01/4.16  Index Deletion       : 0.00
% 11.01/4.16  Index Matching       : 0.00
% 11.01/4.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
