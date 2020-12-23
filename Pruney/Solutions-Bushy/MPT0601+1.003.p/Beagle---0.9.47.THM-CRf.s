%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0601+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:34 EST 2020

% Result     : Theorem 8.17s
% Output     : CNFRefutation 8.17s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 438 expanded)
%              Number of leaves         :   23 ( 155 expanded)
%              Depth                    :   13
%              Number of atoms          :  121 ( 936 expanded)
%              Number of equality atoms :   13 ( 108 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k11_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_250,plain,(
    ! [C_82,A_83] :
      ( r2_hidden(k4_tarski(C_82,'#skF_5'(A_83,k1_relat_1(A_83),C_82)),A_83)
      | ~ r2_hidden(C_82,k1_relat_1(A_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_153,plain,(
    ! [A_62,B_63,C_64] :
      ( r2_hidden(k4_tarski(A_62,B_63),C_64)
      | ~ r2_hidden(B_63,k11_relat_1(C_64,A_62))
      | ~ v1_relat_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [C_22,A_7,D_25] :
      ( r2_hidden(C_22,k1_relat_1(A_7))
      | ~ r2_hidden(k4_tarski(C_22,D_25),A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_166,plain,(
    ! [A_62,C_64,B_63] :
      ( r2_hidden(A_62,k1_relat_1(C_64))
      | ~ r2_hidden(B_63,k11_relat_1(C_64,A_62))
      | ~ v1_relat_1(C_64) ) ),
    inference(resolution,[status(thm)],[c_153,c_10])).

tff(c_5968,plain,(
    ! [A_245,C_246,C_247] :
      ( r2_hidden(A_245,k1_relat_1(C_246))
      | ~ v1_relat_1(C_246)
      | ~ r2_hidden(C_247,k1_relat_1(k11_relat_1(C_246,A_245))) ) ),
    inference(resolution,[status(thm)],[c_250,c_166])).

tff(c_6034,plain,(
    ! [A_245,C_246] :
      ( r2_hidden(A_245,k1_relat_1(C_246))
      | ~ v1_relat_1(C_246)
      | v1_xboole_0(k1_relat_1(k11_relat_1(C_246,A_245))) ) ),
    inference(resolution,[status(thm)],[c_6,c_5968])).

tff(c_6035,plain,(
    ! [A_248,C_249] :
      ( r2_hidden(A_248,k1_relat_1(C_249))
      | ~ v1_relat_1(C_249)
      | v1_xboole_0(k1_relat_1(k11_relat_1(C_249,A_248))) ) ),
    inference(resolution,[status(thm)],[c_6,c_5968])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_275,plain,(
    ! [A_84,C_85] :
      ( ~ v1_xboole_0(A_84)
      | ~ r2_hidden(C_85,k1_relat_1(A_84)) ) ),
    inference(resolution,[status(thm)],[c_250,c_4])).

tff(c_298,plain,(
    ! [A_84] :
      ( ~ v1_xboole_0(A_84)
      | v1_xboole_0(k1_relat_1(A_84)) ) ),
    inference(resolution,[status(thm)],[c_6,c_275])).

tff(c_299,plain,(
    ! [A_86] :
      ( ~ v1_xboole_0(A_86)
      | v1_xboole_0(k1_relat_1(A_86)) ) ),
    inference(resolution,[status(thm)],[c_6,c_275])).

tff(c_24,plain,(
    ! [A_29] :
      ( k1_xboole_0 = A_29
      | ~ v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_311,plain,(
    ! [A_87] :
      ( k1_relat_1(A_87) = k1_xboole_0
      | ~ v1_xboole_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_299,c_24])).

tff(c_321,plain,(
    ! [A_84] :
      ( k1_relat_1(k1_relat_1(A_84)) = k1_xboole_0
      | ~ v1_xboole_0(A_84) ) ),
    inference(resolution,[status(thm)],[c_298,c_311])).

tff(c_8,plain,(
    ! [C_22,A_7] :
      ( r2_hidden(k4_tarski(C_22,'#skF_5'(A_7,k1_relat_1(A_7),C_22)),A_7)
      | ~ r2_hidden(C_22,k1_relat_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_357,plain,(
    ! [A_91,C_92] :
      ( ~ v1_xboole_0(A_91)
      | ~ r2_hidden(C_92,k1_relat_1(k1_relat_1(A_91))) ) ),
    inference(resolution,[status(thm)],[c_8,c_275])).

tff(c_384,plain,(
    ! [A_93] :
      ( ~ v1_xboole_0(A_93)
      | v1_xboole_0(k1_relat_1(k1_relat_1(A_93))) ) ),
    inference(resolution,[status(thm)],[c_6,c_357])).

tff(c_398,plain,(
    ! [A_84] :
      ( ~ v1_xboole_0(A_84)
      | v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(A_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_384])).

tff(c_402,plain,(
    ! [A_84] :
      ( ~ v1_xboole_0(A_84)
      | ~ v1_xboole_0(A_84) ) ),
    inference(splitLeft,[status(thm)],[c_398])).

tff(c_7519,plain,(
    ! [C_284,A_285] :
      ( ~ v1_xboole_0(k1_relat_1(k11_relat_1(C_284,A_285)))
      | r2_hidden(A_285,k1_relat_1(C_284))
      | ~ v1_relat_1(C_284) ) ),
    inference(resolution,[status(thm)],[c_6035,c_402])).

tff(c_7529,plain,(
    ! [A_245,C_246] :
      ( r2_hidden(A_245,k1_relat_1(C_246))
      | ~ v1_relat_1(C_246) ) ),
    inference(resolution,[status(thm)],[c_6034,c_7519])).

tff(c_7533,plain,(
    ! [A_286,C_287] :
      ( r2_hidden(A_286,k1_relat_1(C_287))
      | ~ v1_relat_1(C_287) ) ),
    inference(resolution,[status(thm)],[c_6034,c_7519])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_7702,plain,(
    ! [C_293,A_294] :
      ( ~ r2_hidden(k1_relat_1(C_293),A_294)
      | ~ v1_relat_1(C_293) ) ),
    inference(resolution,[status(thm)],[c_7533,c_2])).

tff(c_7733,plain,(
    ! [C_293,C_246] :
      ( ~ v1_relat_1(C_293)
      | ~ v1_relat_1(C_246) ) ),
    inference(resolution,[status(thm)],[c_7529,c_7702])).

tff(c_7734,plain,(
    ! [C_246] : ~ v1_relat_1(C_246) ),
    inference(splitLeft,[status(thm)],[c_7733])).

tff(c_26,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_7736,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7734,c_26])).

tff(c_7737,plain,(
    ! [C_293] : ~ v1_relat_1(C_293) ),
    inference(splitRight,[status(thm)],[c_7733])).

tff(c_7856,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7737,c_26])).

tff(c_7857,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_398])).

tff(c_310,plain,(
    ! [A_86] :
      ( k1_relat_1(A_86) = k1_xboole_0
      | ~ v1_xboole_0(A_86) ) ),
    inference(resolution,[status(thm)],[c_299,c_24])).

tff(c_7866,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7857,c_310])).

tff(c_294,plain,(
    ! [A_84,C_22] :
      ( ~ v1_xboole_0(A_84)
      | ~ r2_hidden(C_22,k1_relat_1(k1_relat_1(A_84))) ) ),
    inference(resolution,[status(thm)],[c_8,c_275])).

tff(c_7876,plain,(
    ! [C_22] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_22,k1_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7866,c_294])).

tff(c_7897,plain,(
    ! [C_22] : ~ r2_hidden(C_22,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7866,c_7857,c_7876])).

tff(c_28,plain,
    ( k11_relat_1('#skF_7','#skF_6') = k1_xboole_0
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_46,plain,(
    ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_34,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_7'))
    | k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_48,plain,(
    k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_34])).

tff(c_50,plain,(
    ! [A_40,B_41,C_42] :
      ( r2_hidden(k4_tarski(A_40,B_41),C_42)
      | ~ r2_hidden(B_41,k11_relat_1(C_42,A_40))
      | ~ v1_relat_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_87,plain,(
    ! [A_50,C_51,B_52] :
      ( r2_hidden(A_50,k1_relat_1(C_51))
      | ~ r2_hidden(B_52,k11_relat_1(C_51,A_50))
      | ~ v1_relat_1(C_51) ) ),
    inference(resolution,[status(thm)],[c_50,c_10])).

tff(c_101,plain,(
    ! [A_56,C_57] :
      ( r2_hidden(A_56,k1_relat_1(C_57))
      | ~ v1_relat_1(C_57)
      | v1_xboole_0(k11_relat_1(C_57,A_56)) ) ),
    inference(resolution,[status(thm)],[c_6,c_87])).

tff(c_112,plain,
    ( ~ v1_relat_1('#skF_7')
    | v1_xboole_0(k11_relat_1('#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_101,c_46])).

tff(c_122,plain,(
    v1_xboole_0(k11_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_112])).

tff(c_129,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_122,c_24])).

tff(c_134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_129])).

tff(c_135,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_142,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_34])).

tff(c_22,plain,(
    ! [B_27,C_28,A_26] :
      ( r2_hidden(B_27,k11_relat_1(C_28,A_26))
      | ~ r2_hidden(k4_tarski(A_26,B_27),C_28)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_11053,plain,(
    ! [A_378,C_379] :
      ( r2_hidden('#skF_5'(A_378,k1_relat_1(A_378),C_379),k11_relat_1(A_378,C_379))
      | ~ v1_relat_1(A_378)
      | ~ r2_hidden(C_379,k1_relat_1(A_378)) ) ),
    inference(resolution,[status(thm)],[c_250,c_22])).

tff(c_11100,plain,
    ( r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k1_xboole_0)
    | ~ v1_relat_1('#skF_7')
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_11053])).

tff(c_11108,plain,(
    r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_26,c_11100])).

tff(c_11110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7897,c_11108])).

%------------------------------------------------------------------------------
