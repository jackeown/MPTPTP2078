%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:40 EST 2020

% Result     : Theorem 18.87s
% Output     : CNFRefutation 19.10s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 245 expanded)
%              Number of leaves         :   20 (  92 expanded)
%              Depth                    :   11
%              Number of atoms          :  148 ( 661 expanded)
%              Number of equality atoms :   31 ( 165 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k3_relat_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_65,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k3_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k3_relat_1(A),k3_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_243,plain,(
    ! [A_56,B_57,C_58] :
      ( ~ r2_hidden('#skF_1'(A_56,B_57,C_58),C_58)
      | r2_hidden('#skF_2'(A_56,B_57,C_58),C_58)
      | k3_xboole_0(A_56,B_57) = C_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_257,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_2'(A_1,B_2,B_2),B_2)
      | k3_xboole_0(A_1,B_2) = B_2 ) ),
    inference(resolution,[status(thm)],[c_16,c_243])).

tff(c_97,plain,(
    ! [A_46,B_47,C_48] :
      ( r2_hidden('#skF_1'(A_46,B_47,C_48),B_47)
      | r2_hidden('#skF_2'(A_46,B_47,C_48),C_48)
      | k3_xboole_0(A_46,B_47) = C_48 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1063,plain,(
    ! [A_117,B_118,A_119,B_120] :
      ( r2_hidden('#skF_2'(A_117,B_118,k3_xboole_0(A_119,B_120)),B_120)
      | r2_hidden('#skF_1'(A_117,B_118,k3_xboole_0(A_119,B_120)),B_118)
      | k3_xboole_0(A_119,B_120) = k3_xboole_0(A_117,B_118) ) ),
    inference(resolution,[status(thm)],[c_97,c_4])).

tff(c_10,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1112,plain,(
    ! [B_120,B_118,A_119] :
      ( ~ r2_hidden('#skF_2'(B_120,B_118,k3_xboole_0(A_119,B_120)),B_118)
      | r2_hidden('#skF_1'(B_120,B_118,k3_xboole_0(A_119,B_120)),B_118)
      | k3_xboole_0(B_120,B_118) = k3_xboole_0(A_119,B_120) ) ),
    inference(resolution,[status(thm)],[c_1063,c_10])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1279,plain,(
    ! [A_132,A_133,B_134,C_135] :
      ( r2_hidden('#skF_1'(A_132,k3_xboole_0(A_133,B_134),C_135),A_133)
      | r2_hidden('#skF_2'(A_132,k3_xboole_0(A_133,B_134),C_135),C_135)
      | k3_xboole_0(A_132,k3_xboole_0(A_133,B_134)) = C_135 ) ),
    inference(resolution,[status(thm)],[c_97,c_6])).

tff(c_1338,plain,(
    ! [A_133,A_132,B_2,A_1,B_134] :
      ( r2_hidden('#skF_2'(A_132,k3_xboole_0(A_133,B_134),k3_xboole_0(A_1,B_2)),B_2)
      | r2_hidden('#skF_1'(A_132,k3_xboole_0(A_133,B_134),k3_xboole_0(A_1,B_2)),A_133)
      | k3_xboole_0(A_132,k3_xboole_0(A_133,B_134)) = k3_xboole_0(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_1279,c_4])).

tff(c_190,plain,(
    ! [A_51,B_52,C_53] :
      ( r2_hidden('#skF_1'(A_51,B_52,C_53),A_51)
      | r2_hidden('#skF_2'(A_51,B_52,C_53),C_53)
      | k3_xboole_0(A_51,B_52) = C_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_210,plain,(
    ! [A_51,B_52,A_1,B_2] :
      ( r2_hidden('#skF_2'(A_51,B_52,k3_xboole_0(A_1,B_2)),B_2)
      | r2_hidden('#skF_1'(A_51,B_52,k3_xboole_0(A_1,B_2)),A_51)
      | k3_xboole_0(A_51,B_52) = k3_xboole_0(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_190,c_4])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k3_xboole_0(A_1,B_2))
      | ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1677,plain,(
    ! [A_164,B_165,A_166,B_167] :
      ( r2_hidden('#skF_2'(A_164,B_165,k3_xboole_0(A_166,B_167)),k3_xboole_0(A_166,B_167))
      | k3_xboole_0(A_166,B_167) = k3_xboole_0(A_164,B_165)
      | ~ r2_hidden('#skF_1'(A_164,B_165,k3_xboole_0(A_166,B_167)),B_167)
      | ~ r2_hidden('#skF_1'(A_164,B_165,k3_xboole_0(A_166,B_167)),A_166) ) ),
    inference(resolution,[status(thm)],[c_2,c_243])).

tff(c_9349,plain,(
    ! [A_632,B_633,A_634,B_635] :
      ( r2_hidden('#skF_2'(A_632,B_633,k3_xboole_0(A_634,B_635)),B_635)
      | k3_xboole_0(A_634,B_635) = k3_xboole_0(A_632,B_633)
      | ~ r2_hidden('#skF_1'(A_632,B_633,k3_xboole_0(A_634,B_635)),B_635)
      | ~ r2_hidden('#skF_1'(A_632,B_633,k3_xboole_0(A_634,B_635)),A_634) ) ),
    inference(resolution,[status(thm)],[c_1677,c_4])).

tff(c_9499,plain,(
    ! [A_636,B_637,A_638] :
      ( ~ r2_hidden('#skF_1'(A_636,B_637,k3_xboole_0(A_638,A_636)),A_638)
      | r2_hidden('#skF_2'(A_636,B_637,k3_xboole_0(A_638,A_636)),A_636)
      | k3_xboole_0(A_638,A_636) = k3_xboole_0(A_636,B_637) ) ),
    inference(resolution,[status(thm)],[c_210,c_9349])).

tff(c_9619,plain,(
    ! [B_2,A_133,B_134] :
      ( r2_hidden('#skF_2'(B_2,k3_xboole_0(A_133,B_134),k3_xboole_0(A_133,B_2)),B_2)
      | k3_xboole_0(B_2,k3_xboole_0(A_133,B_134)) = k3_xboole_0(A_133,B_2) ) ),
    inference(resolution,[status(thm)],[c_1338,c_9499])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_388,plain,(
    ! [A_73,B_74,C_75] :
      ( r2_hidden('#skF_1'(A_73,B_74,C_75),A_73)
      | ~ r2_hidden('#skF_2'(A_73,B_74,C_75),B_74)
      | ~ r2_hidden('#skF_2'(A_73,B_74,C_75),A_73)
      | k3_xboole_0(A_73,B_74) = C_75 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_403,plain,(
    ! [A_1,C_3] :
      ( ~ r2_hidden('#skF_2'(A_1,C_3,C_3),A_1)
      | r2_hidden('#skF_1'(A_1,C_3,C_3),A_1)
      | k3_xboole_0(A_1,C_3) = C_3 ) ),
    inference(resolution,[status(thm)],[c_18,c_388])).

tff(c_466,plain,(
    ! [A_87,B_88,C_89] :
      ( ~ r2_hidden('#skF_1'(A_87,B_88,C_89),C_89)
      | ~ r2_hidden('#skF_2'(A_87,B_88,C_89),B_88)
      | ~ r2_hidden('#skF_2'(A_87,B_88,C_89),A_87)
      | k3_xboole_0(A_87,B_88) = C_89 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_487,plain,(
    ! [A_90] :
      ( ~ r2_hidden('#skF_2'(A_90,A_90,A_90),A_90)
      | k3_xboole_0(A_90,A_90) = A_90 ) ),
    inference(resolution,[status(thm)],[c_403,c_466])).

tff(c_504,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_257,c_487])).

tff(c_2417,plain,(
    ! [A_221,B_222,A_223,B_224] :
      ( ~ r2_hidden('#skF_2'(A_221,B_222,k3_xboole_0(A_223,B_224)),B_222)
      | ~ r2_hidden('#skF_2'(A_221,B_222,k3_xboole_0(A_223,B_224)),A_221)
      | k3_xboole_0(A_223,B_224) = k3_xboole_0(A_221,B_222)
      | ~ r2_hidden('#skF_1'(A_221,B_222,k3_xboole_0(A_223,B_224)),B_224)
      | ~ r2_hidden('#skF_1'(A_221,B_222,k3_xboole_0(A_223,B_224)),A_223) ) ),
    inference(resolution,[status(thm)],[c_2,c_466])).

tff(c_13336,plain,(
    ! [A_781,A_782,B_783] :
      ( ~ r2_hidden('#skF_2'(A_781,k3_xboole_0(A_782,B_783),k3_xboole_0(A_782,B_783)),A_781)
      | ~ r2_hidden('#skF_1'(A_781,k3_xboole_0(A_782,B_783),k3_xboole_0(A_782,B_783)),B_783)
      | ~ r2_hidden('#skF_1'(A_781,k3_xboole_0(A_782,B_783),k3_xboole_0(A_782,B_783)),A_782)
      | k3_xboole_0(A_781,k3_xboole_0(A_782,B_783)) = k3_xboole_0(A_782,B_783) ) ),
    inference(resolution,[status(thm)],[c_257,c_2417])).

tff(c_13443,plain,(
    ! [A_781,B_2] :
      ( ~ r2_hidden('#skF_2'(A_781,B_2,k3_xboole_0(B_2,B_2)),A_781)
      | ~ r2_hidden('#skF_1'(A_781,k3_xboole_0(B_2,B_2),k3_xboole_0(B_2,B_2)),B_2)
      | ~ r2_hidden('#skF_1'(A_781,k3_xboole_0(B_2,B_2),k3_xboole_0(B_2,B_2)),B_2)
      | k3_xboole_0(A_781,k3_xboole_0(B_2,B_2)) = k3_xboole_0(B_2,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_504,c_13336])).

tff(c_13519,plain,(
    ! [A_784,B_785] :
      ( ~ r2_hidden('#skF_2'(A_784,B_785,B_785),A_784)
      | ~ r2_hidden('#skF_1'(A_784,B_785,B_785),B_785)
      | ~ r2_hidden('#skF_1'(A_784,B_785,B_785),B_785)
      | k3_xboole_0(A_784,B_785) = B_785 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_504,c_504,c_504,c_504,c_504,c_504,c_13443])).

tff(c_13707,plain,(
    ! [B_786,A_787] :
      ( ~ r2_hidden('#skF_1'(B_786,k3_xboole_0(A_787,B_786),k3_xboole_0(A_787,B_786)),k3_xboole_0(A_787,B_786))
      | k3_xboole_0(B_786,k3_xboole_0(A_787,B_786)) = k3_xboole_0(A_787,B_786) ) ),
    inference(resolution,[status(thm)],[c_9619,c_13519])).

tff(c_16093,plain,(
    ! [B_804,A_805] :
      ( ~ r2_hidden('#skF_2'(B_804,k3_xboole_0(A_805,B_804),k3_xboole_0(A_805,B_804)),k3_xboole_0(A_805,B_804))
      | k3_xboole_0(B_804,k3_xboole_0(A_805,B_804)) = k3_xboole_0(A_805,B_804) ) ),
    inference(resolution,[status(thm)],[c_1112,c_13707])).

tff(c_16221,plain,(
    ! [A_806,A_807] : k3_xboole_0(A_806,k3_xboole_0(A_807,A_806)) = k3_xboole_0(A_807,A_806) ),
    inference(resolution,[status(thm)],[c_257,c_16093])).

tff(c_38,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k4_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_22,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_50,plain,(
    ! [A_27,B_28] : r1_tarski(k3_xboole_0(A_27,B_28),A_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_22])).

tff(c_17605,plain,(
    ! [A_807,A_806] : r1_tarski(k3_xboole_0(A_807,A_806),A_806) ),
    inference(superposition,[status(thm),theory(equality)],[c_16221,c_50])).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k4_xboole_0(A_14,B_15))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_47,plain,(
    ! [A_27,B_28] :
      ( v1_relat_1(k3_xboole_0(A_27,B_28))
      | ~ v1_relat_1(A_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_26])).

tff(c_32,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_28,plain,(
    ! [A_16,B_18] :
      ( r1_tarski(k3_relat_1(A_16),k3_relat_1(B_18))
      | ~ r1_tarski(A_16,B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_91,plain,(
    ! [A_41,B_42,C_43] :
      ( r1_tarski(A_41,k3_xboole_0(B_42,C_43))
      | ~ r1_tarski(A_41,C_43)
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_30,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_xboole_0(k3_relat_1('#skF_3'),k3_relat_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_95,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_4'))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_91,c_30])).

tff(c_158,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_161,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_28,c_158])).

tff(c_164,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_50,c_161])).

tff(c_167,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_47,c_164])).

tff(c_171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_167])).

tff(c_172,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_176,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_28,c_172])).

tff(c_179,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_176])).

tff(c_180,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_179])).

tff(c_183,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_47,c_180])).

tff(c_187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_183])).

tff(c_188,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_18066,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17605,c_188])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:58:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.87/8.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.92/8.19  
% 18.92/8.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.92/8.20  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k3_relat_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 18.92/8.20  
% 18.92/8.20  %Foreground sorts:
% 18.92/8.20  
% 18.92/8.20  
% 18.92/8.20  %Background operators:
% 18.92/8.20  
% 18.92/8.20  
% 18.92/8.20  %Foreground operators:
% 18.92/8.20  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 18.92/8.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.92/8.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.92/8.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 18.92/8.20  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 18.92/8.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.92/8.20  tff('#skF_3', type, '#skF_3': $i).
% 18.92/8.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 18.92/8.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.92/8.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 18.92/8.20  tff('#skF_4', type, '#skF_4': $i).
% 18.92/8.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.92/8.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 18.92/8.20  
% 19.10/8.23  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 19.10/8.23  tff(f_44, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 19.10/8.23  tff(f_42, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 19.10/8.23  tff(f_65, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k3_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relat_1)).
% 19.10/8.23  tff(f_48, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_relat_1)).
% 19.10/8.23  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 19.10/8.23  tff(f_40, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 19.10/8.23  tff(c_16, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 19.10/8.23  tff(c_243, plain, (![A_56, B_57, C_58]: (~r2_hidden('#skF_1'(A_56, B_57, C_58), C_58) | r2_hidden('#skF_2'(A_56, B_57, C_58), C_58) | k3_xboole_0(A_56, B_57)=C_58)), inference(cnfTransformation, [status(thm)], [f_34])).
% 19.10/8.23  tff(c_257, plain, (![A_1, B_2]: (r2_hidden('#skF_2'(A_1, B_2, B_2), B_2) | k3_xboole_0(A_1, B_2)=B_2)), inference(resolution, [status(thm)], [c_16, c_243])).
% 19.10/8.23  tff(c_97, plain, (![A_46, B_47, C_48]: (r2_hidden('#skF_1'(A_46, B_47, C_48), B_47) | r2_hidden('#skF_2'(A_46, B_47, C_48), C_48) | k3_xboole_0(A_46, B_47)=C_48)), inference(cnfTransformation, [status(thm)], [f_34])).
% 19.10/8.23  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 19.10/8.23  tff(c_1063, plain, (![A_117, B_118, A_119, B_120]: (r2_hidden('#skF_2'(A_117, B_118, k3_xboole_0(A_119, B_120)), B_120) | r2_hidden('#skF_1'(A_117, B_118, k3_xboole_0(A_119, B_120)), B_118) | k3_xboole_0(A_119, B_120)=k3_xboole_0(A_117, B_118))), inference(resolution, [status(thm)], [c_97, c_4])).
% 19.10/8.23  tff(c_10, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 19.10/8.23  tff(c_1112, plain, (![B_120, B_118, A_119]: (~r2_hidden('#skF_2'(B_120, B_118, k3_xboole_0(A_119, B_120)), B_118) | r2_hidden('#skF_1'(B_120, B_118, k3_xboole_0(A_119, B_120)), B_118) | k3_xboole_0(B_120, B_118)=k3_xboole_0(A_119, B_120))), inference(resolution, [status(thm)], [c_1063, c_10])).
% 19.10/8.23  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 19.10/8.23  tff(c_1279, plain, (![A_132, A_133, B_134, C_135]: (r2_hidden('#skF_1'(A_132, k3_xboole_0(A_133, B_134), C_135), A_133) | r2_hidden('#skF_2'(A_132, k3_xboole_0(A_133, B_134), C_135), C_135) | k3_xboole_0(A_132, k3_xboole_0(A_133, B_134))=C_135)), inference(resolution, [status(thm)], [c_97, c_6])).
% 19.10/8.23  tff(c_1338, plain, (![A_133, A_132, B_2, A_1, B_134]: (r2_hidden('#skF_2'(A_132, k3_xboole_0(A_133, B_134), k3_xboole_0(A_1, B_2)), B_2) | r2_hidden('#skF_1'(A_132, k3_xboole_0(A_133, B_134), k3_xboole_0(A_1, B_2)), A_133) | k3_xboole_0(A_132, k3_xboole_0(A_133, B_134))=k3_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_1279, c_4])).
% 19.10/8.23  tff(c_190, plain, (![A_51, B_52, C_53]: (r2_hidden('#skF_1'(A_51, B_52, C_53), A_51) | r2_hidden('#skF_2'(A_51, B_52, C_53), C_53) | k3_xboole_0(A_51, B_52)=C_53)), inference(cnfTransformation, [status(thm)], [f_34])).
% 19.10/8.23  tff(c_210, plain, (![A_51, B_52, A_1, B_2]: (r2_hidden('#skF_2'(A_51, B_52, k3_xboole_0(A_1, B_2)), B_2) | r2_hidden('#skF_1'(A_51, B_52, k3_xboole_0(A_1, B_2)), A_51) | k3_xboole_0(A_51, B_52)=k3_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_190, c_4])).
% 19.10/8.23  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k3_xboole_0(A_1, B_2)) | ~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 19.10/8.23  tff(c_1677, plain, (![A_164, B_165, A_166, B_167]: (r2_hidden('#skF_2'(A_164, B_165, k3_xboole_0(A_166, B_167)), k3_xboole_0(A_166, B_167)) | k3_xboole_0(A_166, B_167)=k3_xboole_0(A_164, B_165) | ~r2_hidden('#skF_1'(A_164, B_165, k3_xboole_0(A_166, B_167)), B_167) | ~r2_hidden('#skF_1'(A_164, B_165, k3_xboole_0(A_166, B_167)), A_166))), inference(resolution, [status(thm)], [c_2, c_243])).
% 19.10/8.23  tff(c_9349, plain, (![A_632, B_633, A_634, B_635]: (r2_hidden('#skF_2'(A_632, B_633, k3_xboole_0(A_634, B_635)), B_635) | k3_xboole_0(A_634, B_635)=k3_xboole_0(A_632, B_633) | ~r2_hidden('#skF_1'(A_632, B_633, k3_xboole_0(A_634, B_635)), B_635) | ~r2_hidden('#skF_1'(A_632, B_633, k3_xboole_0(A_634, B_635)), A_634))), inference(resolution, [status(thm)], [c_1677, c_4])).
% 19.10/8.23  tff(c_9499, plain, (![A_636, B_637, A_638]: (~r2_hidden('#skF_1'(A_636, B_637, k3_xboole_0(A_638, A_636)), A_638) | r2_hidden('#skF_2'(A_636, B_637, k3_xboole_0(A_638, A_636)), A_636) | k3_xboole_0(A_638, A_636)=k3_xboole_0(A_636, B_637))), inference(resolution, [status(thm)], [c_210, c_9349])).
% 19.10/8.23  tff(c_9619, plain, (![B_2, A_133, B_134]: (r2_hidden('#skF_2'(B_2, k3_xboole_0(A_133, B_134), k3_xboole_0(A_133, B_2)), B_2) | k3_xboole_0(B_2, k3_xboole_0(A_133, B_134))=k3_xboole_0(A_133, B_2))), inference(resolution, [status(thm)], [c_1338, c_9499])).
% 19.10/8.23  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 19.10/8.23  tff(c_388, plain, (![A_73, B_74, C_75]: (r2_hidden('#skF_1'(A_73, B_74, C_75), A_73) | ~r2_hidden('#skF_2'(A_73, B_74, C_75), B_74) | ~r2_hidden('#skF_2'(A_73, B_74, C_75), A_73) | k3_xboole_0(A_73, B_74)=C_75)), inference(cnfTransformation, [status(thm)], [f_34])).
% 19.10/8.23  tff(c_403, plain, (![A_1, C_3]: (~r2_hidden('#skF_2'(A_1, C_3, C_3), A_1) | r2_hidden('#skF_1'(A_1, C_3, C_3), A_1) | k3_xboole_0(A_1, C_3)=C_3)), inference(resolution, [status(thm)], [c_18, c_388])).
% 19.10/8.23  tff(c_466, plain, (![A_87, B_88, C_89]: (~r2_hidden('#skF_1'(A_87, B_88, C_89), C_89) | ~r2_hidden('#skF_2'(A_87, B_88, C_89), B_88) | ~r2_hidden('#skF_2'(A_87, B_88, C_89), A_87) | k3_xboole_0(A_87, B_88)=C_89)), inference(cnfTransformation, [status(thm)], [f_34])).
% 19.10/8.23  tff(c_487, plain, (![A_90]: (~r2_hidden('#skF_2'(A_90, A_90, A_90), A_90) | k3_xboole_0(A_90, A_90)=A_90)), inference(resolution, [status(thm)], [c_403, c_466])).
% 19.10/8.23  tff(c_504, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_257, c_487])).
% 19.10/8.23  tff(c_2417, plain, (![A_221, B_222, A_223, B_224]: (~r2_hidden('#skF_2'(A_221, B_222, k3_xboole_0(A_223, B_224)), B_222) | ~r2_hidden('#skF_2'(A_221, B_222, k3_xboole_0(A_223, B_224)), A_221) | k3_xboole_0(A_223, B_224)=k3_xboole_0(A_221, B_222) | ~r2_hidden('#skF_1'(A_221, B_222, k3_xboole_0(A_223, B_224)), B_224) | ~r2_hidden('#skF_1'(A_221, B_222, k3_xboole_0(A_223, B_224)), A_223))), inference(resolution, [status(thm)], [c_2, c_466])).
% 19.10/8.23  tff(c_13336, plain, (![A_781, A_782, B_783]: (~r2_hidden('#skF_2'(A_781, k3_xboole_0(A_782, B_783), k3_xboole_0(A_782, B_783)), A_781) | ~r2_hidden('#skF_1'(A_781, k3_xboole_0(A_782, B_783), k3_xboole_0(A_782, B_783)), B_783) | ~r2_hidden('#skF_1'(A_781, k3_xboole_0(A_782, B_783), k3_xboole_0(A_782, B_783)), A_782) | k3_xboole_0(A_781, k3_xboole_0(A_782, B_783))=k3_xboole_0(A_782, B_783))), inference(resolution, [status(thm)], [c_257, c_2417])).
% 19.10/8.23  tff(c_13443, plain, (![A_781, B_2]: (~r2_hidden('#skF_2'(A_781, B_2, k3_xboole_0(B_2, B_2)), A_781) | ~r2_hidden('#skF_1'(A_781, k3_xboole_0(B_2, B_2), k3_xboole_0(B_2, B_2)), B_2) | ~r2_hidden('#skF_1'(A_781, k3_xboole_0(B_2, B_2), k3_xboole_0(B_2, B_2)), B_2) | k3_xboole_0(A_781, k3_xboole_0(B_2, B_2))=k3_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_504, c_13336])).
% 19.10/8.23  tff(c_13519, plain, (![A_784, B_785]: (~r2_hidden('#skF_2'(A_784, B_785, B_785), A_784) | ~r2_hidden('#skF_1'(A_784, B_785, B_785), B_785) | ~r2_hidden('#skF_1'(A_784, B_785, B_785), B_785) | k3_xboole_0(A_784, B_785)=B_785)), inference(demodulation, [status(thm), theory('equality')], [c_504, c_504, c_504, c_504, c_504, c_504, c_504, c_13443])).
% 19.10/8.23  tff(c_13707, plain, (![B_786, A_787]: (~r2_hidden('#skF_1'(B_786, k3_xboole_0(A_787, B_786), k3_xboole_0(A_787, B_786)), k3_xboole_0(A_787, B_786)) | k3_xboole_0(B_786, k3_xboole_0(A_787, B_786))=k3_xboole_0(A_787, B_786))), inference(resolution, [status(thm)], [c_9619, c_13519])).
% 19.10/8.23  tff(c_16093, plain, (![B_804, A_805]: (~r2_hidden('#skF_2'(B_804, k3_xboole_0(A_805, B_804), k3_xboole_0(A_805, B_804)), k3_xboole_0(A_805, B_804)) | k3_xboole_0(B_804, k3_xboole_0(A_805, B_804))=k3_xboole_0(A_805, B_804))), inference(resolution, [status(thm)], [c_1112, c_13707])).
% 19.10/8.23  tff(c_16221, plain, (![A_806, A_807]: (k3_xboole_0(A_806, k3_xboole_0(A_807, A_806))=k3_xboole_0(A_807, A_806))), inference(resolution, [status(thm)], [c_257, c_16093])).
% 19.10/8.23  tff(c_38, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k4_xboole_0(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_44])).
% 19.10/8.23  tff(c_22, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 19.10/8.23  tff(c_50, plain, (![A_27, B_28]: (r1_tarski(k3_xboole_0(A_27, B_28), A_27))), inference(superposition, [status(thm), theory('equality')], [c_38, c_22])).
% 19.10/8.23  tff(c_17605, plain, (![A_807, A_806]: (r1_tarski(k3_xboole_0(A_807, A_806), A_806))), inference(superposition, [status(thm), theory('equality')], [c_16221, c_50])).
% 19.10/8.23  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 19.10/8.23  tff(c_26, plain, (![A_14, B_15]: (v1_relat_1(k4_xboole_0(A_14, B_15)) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 19.10/8.23  tff(c_47, plain, (![A_27, B_28]: (v1_relat_1(k3_xboole_0(A_27, B_28)) | ~v1_relat_1(A_27))), inference(superposition, [status(thm), theory('equality')], [c_38, c_26])).
% 19.10/8.23  tff(c_32, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_65])).
% 19.10/8.23  tff(c_28, plain, (![A_16, B_18]: (r1_tarski(k3_relat_1(A_16), k3_relat_1(B_18)) | ~r1_tarski(A_16, B_18) | ~v1_relat_1(B_18) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 19.10/8.23  tff(c_91, plain, (![A_41, B_42, C_43]: (r1_tarski(A_41, k3_xboole_0(B_42, C_43)) | ~r1_tarski(A_41, C_43) | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_40])).
% 19.10/8.23  tff(c_30, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_xboole_0(k3_relat_1('#skF_3'), k3_relat_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_65])).
% 19.10/8.23  tff(c_95, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_4')) | ~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_91, c_30])).
% 19.10/8.23  tff(c_158, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_95])).
% 19.10/8.23  tff(c_161, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_158])).
% 19.10/8.23  tff(c_164, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_50, c_161])).
% 19.10/8.23  tff(c_167, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_47, c_164])).
% 19.10/8.23  tff(c_171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_167])).
% 19.10/8.23  tff(c_172, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_95])).
% 19.10/8.23  tff(c_176, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_172])).
% 19.10/8.23  tff(c_179, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_176])).
% 19.10/8.23  tff(c_180, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_179])).
% 19.10/8.23  tff(c_183, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_47, c_180])).
% 19.10/8.23  tff(c_187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_183])).
% 19.10/8.23  tff(c_188, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_179])).
% 19.10/8.23  tff(c_18066, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17605, c_188])).
% 19.10/8.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.10/8.23  
% 19.10/8.23  Inference rules
% 19.10/8.23  ----------------------
% 19.10/8.23  #Ref     : 0
% 19.10/8.23  #Sup     : 3906
% 19.10/8.23  #Fact    : 0
% 19.10/8.23  #Define  : 0
% 19.10/8.23  #Split   : 2
% 19.10/8.23  #Chain   : 0
% 19.10/8.23  #Close   : 0
% 19.10/8.23  
% 19.10/8.23  Ordering : KBO
% 19.10/8.23  
% 19.10/8.23  Simplification rules
% 19.10/8.23  ----------------------
% 19.10/8.23  #Subsume      : 1966
% 19.10/8.23  #Demod        : 5114
% 19.10/8.23  #Tautology    : 436
% 19.10/8.23  #SimpNegUnit  : 0
% 19.10/8.23  #BackRed      : 13
% 19.10/8.23  
% 19.10/8.23  #Partial instantiations: 0
% 19.10/8.23  #Strategies tried      : 1
% 19.10/8.23  
% 19.10/8.23  Timing (in seconds)
% 19.10/8.23  ----------------------
% 19.10/8.23  Preprocessing        : 0.46
% 19.10/8.23  Parsing              : 0.25
% 19.10/8.23  CNF conversion       : 0.04
% 19.10/8.24  Main loop            : 6.91
% 19.10/8.24  Inferencing          : 1.95
% 19.10/8.24  Reduction            : 1.93
% 19.10/8.24  Demodulation         : 1.47
% 19.10/8.24  BG Simplification    : 0.21
% 19.10/8.24  Subsumption          : 2.46
% 19.10/8.24  Abstraction          : 0.43
% 19.10/8.24  MUC search           : 0.00
% 19.10/8.24  Cooper               : 0.00
% 19.10/8.24  Total                : 7.44
% 19.10/8.24  Index Insertion      : 0.00
% 19.10/8.24  Index Deletion       : 0.00
% 19.10/8.24  Index Matching       : 0.00
% 19.10/8.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
