%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:33 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 4.09s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 123 expanded)
%              Number of leaves         :   32 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :  129 ( 235 expanded)
%              Number of equality atoms :   46 (  70 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => r1_tarski(k2_relat_1(k7_relat_1(B,k1_tarski(A))),k1_tarski(k1_funct_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_59,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k1_relat_1(C)) )
       => k9_relat_1(C,k2_tarski(A,B)) = k2_tarski(k1_funct_1(C,A),k1_funct_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_40,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_144,plain,(
    ! [B_48,A_49] :
      ( r1_xboole_0(k1_relat_1(B_48),A_49)
      | k7_relat_1(B_48,A_49) != k1_xboole_0
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( k4_xboole_0(A_4,B_5) = A_4
      | ~ r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_423,plain,(
    ! [B_92,A_93] :
      ( k4_xboole_0(k1_relat_1(B_92),A_93) = k1_relat_1(B_92)
      | k7_relat_1(B_92,A_93) != k1_xboole_0
      | ~ v1_relat_1(B_92) ) ),
    inference(resolution,[status(thm)],[c_144,c_10])).

tff(c_14,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_xboole_0(A_6,k4_xboole_0(C_8,B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_980,plain,(
    ! [A_163,B_164,A_165] :
      ( r1_xboole_0(A_163,k1_relat_1(B_164))
      | ~ r1_tarski(A_163,A_165)
      | k7_relat_1(B_164,A_165) != k1_xboole_0
      | ~ v1_relat_1(B_164) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_14])).

tff(c_988,plain,(
    ! [B_166,B_167] :
      ( r1_xboole_0(B_166,k1_relat_1(B_167))
      | k7_relat_1(B_167,B_166) != k1_xboole_0
      | ~ v1_relat_1(B_167) ) ),
    inference(resolution,[status(thm)],[c_6,c_980])).

tff(c_1002,plain,(
    ! [B_168,B_169] :
      ( k4_xboole_0(B_168,k1_relat_1(B_169)) = B_168
      | k7_relat_1(B_169,B_168) != k1_xboole_0
      | ~ v1_relat_1(B_169) ) ),
    inference(resolution,[status(thm)],[c_988,c_10])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_184,plain,(
    ! [B_53,A_54] :
      ( k7_relat_1(B_53,A_54) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_53),A_54)
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_316,plain,(
    ! [B_77,C_78,B_79] :
      ( k7_relat_1(B_77,k4_xboole_0(C_78,B_79)) = k1_xboole_0
      | ~ v1_relat_1(B_77)
      | ~ r1_tarski(k1_relat_1(B_77),B_79) ) ),
    inference(resolution,[status(thm)],[c_14,c_184])).

tff(c_363,plain,(
    ! [B_84,C_85] :
      ( k7_relat_1(B_84,k4_xboole_0(C_85,k1_relat_1(B_84))) = k1_xboole_0
      | ~ v1_relat_1(B_84) ) ),
    inference(resolution,[status(thm)],[c_6,c_316])).

tff(c_24,plain,(
    ! [B_18,A_17] :
      ( k2_relat_1(k7_relat_1(B_18,A_17)) = k9_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_369,plain,(
    ! [B_84,C_85] :
      ( k9_relat_1(B_84,k4_xboole_0(C_85,k1_relat_1(B_84))) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(B_84)
      | ~ v1_relat_1(B_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_24])).

tff(c_381,plain,(
    ! [B_84,C_85] :
      ( k9_relat_1(B_84,k4_xboole_0(C_85,k1_relat_1(B_84))) = k1_xboole_0
      | ~ v1_relat_1(B_84)
      | ~ v1_relat_1(B_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_369])).

tff(c_1278,plain,(
    ! [B_240,B_241] :
      ( k9_relat_1(B_240,B_241) = k1_xboole_0
      | ~ v1_relat_1(B_240)
      | ~ v1_relat_1(B_240)
      | k7_relat_1(B_240,B_241) != k1_xboole_0
      | ~ v1_relat_1(B_240) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1002,c_381])).

tff(c_1280,plain,(
    ! [B_241] :
      ( k9_relat_1('#skF_2',B_241) = k1_xboole_0
      | k7_relat_1('#skF_2',B_241) != k1_xboole_0
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_1278])).

tff(c_1284,plain,(
    ! [B_242] :
      ( k9_relat_1('#skF_2',B_242) = k1_xboole_0
      | k7_relat_1('#skF_2',B_242) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1280])).

tff(c_118,plain,(
    ! [B_44,A_45] :
      ( k2_relat_1(k7_relat_1(B_44,A_45)) = k9_relat_1(B_44,A_45)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_36,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_2',k1_tarski('#skF_1'))),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_124,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_36])).

tff(c_130,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_124])).

tff(c_1297,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | k7_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1284,c_130])).

tff(c_1316,plain,(
    k7_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1297])).

tff(c_38,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( r1_xboole_0(k1_tarski(A_15),B_16)
      | r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_72,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(A_33,B_34) = A_33
      | ~ r1_xboole_0(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_80,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(k1_tarski(A_15),B_16) = k1_tarski(A_15)
      | r2_hidden(A_15,B_16) ) ),
    inference(resolution,[status(thm)],[c_22,c_72])).

tff(c_376,plain,(
    ! [B_84,A_15] :
      ( k7_relat_1(B_84,k1_tarski(A_15)) = k1_xboole_0
      | ~ v1_relat_1(B_84)
      | r2_hidden(A_15,k1_relat_1(B_84)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_363])).

tff(c_810,plain,(
    ! [B_139,A_140] :
      ( k7_relat_1(B_139,k1_tarski(A_140)) = k1_xboole_0
      | ~ v1_relat_1(B_139)
      | r2_hidden(A_140,k1_relat_1(B_139)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_363])).

tff(c_16,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_209,plain,(
    ! [C_58,A_59,B_60] :
      ( k2_tarski(k1_funct_1(C_58,A_59),k1_funct_1(C_58,B_60)) = k9_relat_1(C_58,k2_tarski(A_59,B_60))
      | ~ r2_hidden(B_60,k1_relat_1(C_58))
      | ~ r2_hidden(A_59,k1_relat_1(C_58))
      | ~ v1_funct_1(C_58)
      | ~ v1_relat_1(C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_223,plain,(
    ! [C_58,A_59] :
      ( k9_relat_1(C_58,k2_tarski(A_59,A_59)) = k1_tarski(k1_funct_1(C_58,A_59))
      | ~ r2_hidden(A_59,k1_relat_1(C_58))
      | ~ r2_hidden(A_59,k1_relat_1(C_58))
      | ~ v1_funct_1(C_58)
      | ~ v1_relat_1(C_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_209])).

tff(c_227,plain,(
    ! [C_58,A_59] :
      ( k9_relat_1(C_58,k1_tarski(A_59)) = k1_tarski(k1_funct_1(C_58,A_59))
      | ~ r2_hidden(A_59,k1_relat_1(C_58))
      | ~ r2_hidden(A_59,k1_relat_1(C_58))
      | ~ v1_funct_1(C_58)
      | ~ v1_relat_1(C_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_223])).

tff(c_1499,plain,(
    ! [B_293,A_294] :
      ( k9_relat_1(B_293,k1_tarski(A_294)) = k1_tarski(k1_funct_1(B_293,A_294))
      | ~ r2_hidden(A_294,k1_relat_1(B_293))
      | ~ v1_funct_1(B_293)
      | k7_relat_1(B_293,k1_tarski(A_294)) = k1_xboole_0
      | ~ v1_relat_1(B_293) ) ),
    inference(resolution,[status(thm)],[c_810,c_227])).

tff(c_1613,plain,(
    ! [B_298,A_299] :
      ( k9_relat_1(B_298,k1_tarski(A_299)) = k1_tarski(k1_funct_1(B_298,A_299))
      | ~ v1_funct_1(B_298)
      | k7_relat_1(B_298,k1_tarski(A_299)) = k1_xboole_0
      | ~ v1_relat_1(B_298) ) ),
    inference(resolution,[status(thm)],[c_376,c_1499])).

tff(c_1623,plain,
    ( ~ r1_tarski(k1_tarski(k1_funct_1('#skF_2','#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_2')
    | k7_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1613,c_130])).

tff(c_1635,plain,(
    k7_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_6,c_1623])).

tff(c_1637,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1316,c_1635])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:24:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.73/1.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/1.75  
% 3.73/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/1.75  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.73/1.75  
% 3.73/1.75  %Foreground sorts:
% 3.73/1.75  
% 3.73/1.75  
% 3.73/1.75  %Background operators:
% 3.73/1.75  
% 3.73/1.75  
% 3.73/1.75  %Foreground operators:
% 3.73/1.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.73/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.73/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.73/1.75  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.73/1.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.73/1.75  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.73/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.73/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.73/1.75  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.73/1.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.73/1.75  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.73/1.75  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.73/1.75  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.73/1.75  tff('#skF_2', type, '#skF_2': $i).
% 3.73/1.75  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.73/1.75  tff('#skF_1', type, '#skF_1': $i).
% 3.73/1.75  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.73/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.73/1.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.73/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.73/1.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.73/1.75  
% 4.09/1.76  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.09/1.76  tff(f_82, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_funct_1)).
% 4.09/1.76  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.09/1.76  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 4.09/1.76  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.09/1.76  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 4.09/1.76  tff(f_59, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 4.09/1.76  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 4.09/1.76  tff(f_52, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 4.09/1.76  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.09/1.76  tff(f_75, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k1_relat_1(C))) => (k9_relat_1(C, k2_tarski(A, B)) = k2_tarski(k1_funct_1(C, A), k1_funct_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_funct_1)).
% 4.09/1.76  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.09/1.76  tff(c_40, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.09/1.76  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.09/1.76  tff(c_144, plain, (![B_48, A_49]: (r1_xboole_0(k1_relat_1(B_48), A_49) | k7_relat_1(B_48, A_49)!=k1_xboole_0 | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.09/1.76  tff(c_10, plain, (![A_4, B_5]: (k4_xboole_0(A_4, B_5)=A_4 | ~r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.09/1.76  tff(c_423, plain, (![B_92, A_93]: (k4_xboole_0(k1_relat_1(B_92), A_93)=k1_relat_1(B_92) | k7_relat_1(B_92, A_93)!=k1_xboole_0 | ~v1_relat_1(B_92))), inference(resolution, [status(thm)], [c_144, c_10])).
% 4.09/1.76  tff(c_14, plain, (![A_6, C_8, B_7]: (r1_xboole_0(A_6, k4_xboole_0(C_8, B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.09/1.76  tff(c_980, plain, (![A_163, B_164, A_165]: (r1_xboole_0(A_163, k1_relat_1(B_164)) | ~r1_tarski(A_163, A_165) | k7_relat_1(B_164, A_165)!=k1_xboole_0 | ~v1_relat_1(B_164))), inference(superposition, [status(thm), theory('equality')], [c_423, c_14])).
% 4.09/1.76  tff(c_988, plain, (![B_166, B_167]: (r1_xboole_0(B_166, k1_relat_1(B_167)) | k7_relat_1(B_167, B_166)!=k1_xboole_0 | ~v1_relat_1(B_167))), inference(resolution, [status(thm)], [c_6, c_980])).
% 4.09/1.76  tff(c_1002, plain, (![B_168, B_169]: (k4_xboole_0(B_168, k1_relat_1(B_169))=B_168 | k7_relat_1(B_169, B_168)!=k1_xboole_0 | ~v1_relat_1(B_169))), inference(resolution, [status(thm)], [c_988, c_10])).
% 4.09/1.76  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.09/1.76  tff(c_184, plain, (![B_53, A_54]: (k7_relat_1(B_53, A_54)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_53), A_54) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.09/1.76  tff(c_316, plain, (![B_77, C_78, B_79]: (k7_relat_1(B_77, k4_xboole_0(C_78, B_79))=k1_xboole_0 | ~v1_relat_1(B_77) | ~r1_tarski(k1_relat_1(B_77), B_79))), inference(resolution, [status(thm)], [c_14, c_184])).
% 4.09/1.76  tff(c_363, plain, (![B_84, C_85]: (k7_relat_1(B_84, k4_xboole_0(C_85, k1_relat_1(B_84)))=k1_xboole_0 | ~v1_relat_1(B_84))), inference(resolution, [status(thm)], [c_6, c_316])).
% 4.09/1.76  tff(c_24, plain, (![B_18, A_17]: (k2_relat_1(k7_relat_1(B_18, A_17))=k9_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.09/1.76  tff(c_369, plain, (![B_84, C_85]: (k9_relat_1(B_84, k4_xboole_0(C_85, k1_relat_1(B_84)))=k2_relat_1(k1_xboole_0) | ~v1_relat_1(B_84) | ~v1_relat_1(B_84))), inference(superposition, [status(thm), theory('equality')], [c_363, c_24])).
% 4.09/1.76  tff(c_381, plain, (![B_84, C_85]: (k9_relat_1(B_84, k4_xboole_0(C_85, k1_relat_1(B_84)))=k1_xboole_0 | ~v1_relat_1(B_84) | ~v1_relat_1(B_84))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_369])).
% 4.09/1.76  tff(c_1278, plain, (![B_240, B_241]: (k9_relat_1(B_240, B_241)=k1_xboole_0 | ~v1_relat_1(B_240) | ~v1_relat_1(B_240) | k7_relat_1(B_240, B_241)!=k1_xboole_0 | ~v1_relat_1(B_240))), inference(superposition, [status(thm), theory('equality')], [c_1002, c_381])).
% 4.09/1.76  tff(c_1280, plain, (![B_241]: (k9_relat_1('#skF_2', B_241)=k1_xboole_0 | k7_relat_1('#skF_2', B_241)!=k1_xboole_0 | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_1278])).
% 4.09/1.76  tff(c_1284, plain, (![B_242]: (k9_relat_1('#skF_2', B_242)=k1_xboole_0 | k7_relat_1('#skF_2', B_242)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1280])).
% 4.09/1.76  tff(c_118, plain, (![B_44, A_45]: (k2_relat_1(k7_relat_1(B_44, A_45))=k9_relat_1(B_44, A_45) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.09/1.76  tff(c_36, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_2', k1_tarski('#skF_1'))), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.09/1.76  tff(c_124, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_118, c_36])).
% 4.09/1.76  tff(c_130, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_124])).
% 4.09/1.76  tff(c_1297, plain, (~r1_tarski(k1_xboole_0, k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | k7_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1284, c_130])).
% 4.09/1.76  tff(c_1316, plain, (k7_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1297])).
% 4.09/1.76  tff(c_38, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.09/1.76  tff(c_22, plain, (![A_15, B_16]: (r1_xboole_0(k1_tarski(A_15), B_16) | r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.09/1.76  tff(c_72, plain, (![A_33, B_34]: (k4_xboole_0(A_33, B_34)=A_33 | ~r1_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.09/1.76  tff(c_80, plain, (![A_15, B_16]: (k4_xboole_0(k1_tarski(A_15), B_16)=k1_tarski(A_15) | r2_hidden(A_15, B_16))), inference(resolution, [status(thm)], [c_22, c_72])).
% 4.09/1.76  tff(c_376, plain, (![B_84, A_15]: (k7_relat_1(B_84, k1_tarski(A_15))=k1_xboole_0 | ~v1_relat_1(B_84) | r2_hidden(A_15, k1_relat_1(B_84)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_363])).
% 4.09/1.76  tff(c_810, plain, (![B_139, A_140]: (k7_relat_1(B_139, k1_tarski(A_140))=k1_xboole_0 | ~v1_relat_1(B_139) | r2_hidden(A_140, k1_relat_1(B_139)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_363])).
% 4.09/1.76  tff(c_16, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.09/1.76  tff(c_209, plain, (![C_58, A_59, B_60]: (k2_tarski(k1_funct_1(C_58, A_59), k1_funct_1(C_58, B_60))=k9_relat_1(C_58, k2_tarski(A_59, B_60)) | ~r2_hidden(B_60, k1_relat_1(C_58)) | ~r2_hidden(A_59, k1_relat_1(C_58)) | ~v1_funct_1(C_58) | ~v1_relat_1(C_58))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.09/1.76  tff(c_223, plain, (![C_58, A_59]: (k9_relat_1(C_58, k2_tarski(A_59, A_59))=k1_tarski(k1_funct_1(C_58, A_59)) | ~r2_hidden(A_59, k1_relat_1(C_58)) | ~r2_hidden(A_59, k1_relat_1(C_58)) | ~v1_funct_1(C_58) | ~v1_relat_1(C_58))), inference(superposition, [status(thm), theory('equality')], [c_16, c_209])).
% 4.09/1.76  tff(c_227, plain, (![C_58, A_59]: (k9_relat_1(C_58, k1_tarski(A_59))=k1_tarski(k1_funct_1(C_58, A_59)) | ~r2_hidden(A_59, k1_relat_1(C_58)) | ~r2_hidden(A_59, k1_relat_1(C_58)) | ~v1_funct_1(C_58) | ~v1_relat_1(C_58))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_223])).
% 4.09/1.76  tff(c_1499, plain, (![B_293, A_294]: (k9_relat_1(B_293, k1_tarski(A_294))=k1_tarski(k1_funct_1(B_293, A_294)) | ~r2_hidden(A_294, k1_relat_1(B_293)) | ~v1_funct_1(B_293) | k7_relat_1(B_293, k1_tarski(A_294))=k1_xboole_0 | ~v1_relat_1(B_293))), inference(resolution, [status(thm)], [c_810, c_227])).
% 4.09/1.76  tff(c_1613, plain, (![B_298, A_299]: (k9_relat_1(B_298, k1_tarski(A_299))=k1_tarski(k1_funct_1(B_298, A_299)) | ~v1_funct_1(B_298) | k7_relat_1(B_298, k1_tarski(A_299))=k1_xboole_0 | ~v1_relat_1(B_298))), inference(resolution, [status(thm)], [c_376, c_1499])).
% 4.09/1.76  tff(c_1623, plain, (~r1_tarski(k1_tarski(k1_funct_1('#skF_2', '#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_2') | k7_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1613, c_130])).
% 4.09/1.76  tff(c_1635, plain, (k7_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_6, c_1623])).
% 4.09/1.76  tff(c_1637, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1316, c_1635])).
% 4.09/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.09/1.76  
% 4.09/1.76  Inference rules
% 4.09/1.76  ----------------------
% 4.09/1.76  #Ref     : 0
% 4.09/1.76  #Sup     : 389
% 4.09/1.76  #Fact    : 0
% 4.09/1.76  #Define  : 0
% 4.09/1.76  #Split   : 2
% 4.09/1.76  #Chain   : 0
% 4.09/1.76  #Close   : 0
% 4.09/1.76  
% 4.09/1.76  Ordering : KBO
% 4.09/1.76  
% 4.09/1.76  Simplification rules
% 4.09/1.76  ----------------------
% 4.09/1.76  #Subsume      : 116
% 4.09/1.76  #Demod        : 117
% 4.09/1.76  #Tautology    : 171
% 4.09/1.76  #SimpNegUnit  : 1
% 4.09/1.76  #BackRed      : 0
% 4.09/1.76  
% 4.09/1.76  #Partial instantiations: 0
% 4.09/1.76  #Strategies tried      : 1
% 4.09/1.76  
% 4.09/1.76  Timing (in seconds)
% 4.09/1.76  ----------------------
% 4.09/1.77  Preprocessing        : 0.36
% 4.09/1.77  Parsing              : 0.18
% 4.09/1.77  CNF conversion       : 0.02
% 4.09/1.77  Main loop            : 0.54
% 4.09/1.77  Inferencing          : 0.21
% 4.09/1.77  Reduction            : 0.14
% 4.09/1.77  Demodulation         : 0.09
% 4.09/1.77  BG Simplification    : 0.03
% 4.09/1.77  Subsumption          : 0.13
% 4.09/1.77  Abstraction          : 0.03
% 4.09/1.77  MUC search           : 0.00
% 4.09/1.77  Cooper               : 0.00
% 4.09/1.77  Total                : 0.93
% 4.09/1.77  Index Insertion      : 0.00
% 4.09/1.77  Index Deletion       : 0.00
% 4.09/1.77  Index Matching       : 0.00
% 4.09/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
