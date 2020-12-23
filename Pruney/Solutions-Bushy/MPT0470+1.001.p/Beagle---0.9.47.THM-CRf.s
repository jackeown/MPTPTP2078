%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0470+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:21 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 134 expanded)
%              Number of leaves         :   21 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :   98 ( 258 expanded)
%              Number of equality atoms :   22 (  66 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_1 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_59,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_47,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_28,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( C = k5_relat_1(A,B)
              <=> ! [D,E] :
                    ( r2_hidden(k4_tarski(D,E),C)
                  <=> ? [F] :
                        ( r2_hidden(k4_tarski(D,F),A)
                        & r2_hidden(k4_tarski(F,E),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(c_26,plain,
    ( k5_relat_1('#skF_7',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_35,plain,(
    k5_relat_1(k1_xboole_0,'#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_28,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_29,plain,(
    ! [A_103] :
      ( v1_relat_1(A_103)
      | ~ v1_xboole_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_33,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_29])).

tff(c_157,plain,(
    ! [A_150,B_151,C_152] :
      ( r2_hidden(k4_tarski('#skF_2'(A_150,B_151,C_152),'#skF_4'(A_150,B_151,C_152)),A_150)
      | r2_hidden(k4_tarski('#skF_5'(A_150,B_151,C_152),'#skF_6'(A_150,B_151,C_152)),C_152)
      | k5_relat_1(A_150,B_151) = C_152
      | ~ v1_relat_1(C_152)
      | ~ v1_relat_1(B_151)
      | ~ v1_relat_1(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,(
    ! [B_102,A_101] :
      ( ~ v1_xboole_0(B_102)
      | ~ r2_hidden(A_101,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_232,plain,(
    ! [A_153,B_154,C_155] :
      ( ~ v1_xboole_0(A_153)
      | r2_hidden(k4_tarski('#skF_5'(A_153,B_154,C_155),'#skF_6'(A_153,B_154,C_155)),C_155)
      | k5_relat_1(A_153,B_154) = C_155
      | ~ v1_relat_1(C_155)
      | ~ v1_relat_1(B_154)
      | ~ v1_relat_1(A_153) ) ),
    inference(resolution,[status(thm)],[c_157,c_24])).

tff(c_345,plain,(
    ! [C_159,A_160,B_161] :
      ( ~ v1_xboole_0(C_159)
      | ~ v1_xboole_0(A_160)
      | k5_relat_1(A_160,B_161) = C_159
      | ~ v1_relat_1(C_159)
      | ~ v1_relat_1(B_161)
      | ~ v1_relat_1(A_160) ) ),
    inference(resolution,[status(thm)],[c_232,c_24])).

tff(c_347,plain,(
    ! [A_160,B_161] :
      ( ~ v1_xboole_0(A_160)
      | k5_relat_1(A_160,B_161) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(B_161)
      | ~ v1_relat_1(A_160) ) ),
    inference(resolution,[status(thm)],[c_22,c_345])).

tff(c_351,plain,(
    ! [A_162,B_163] :
      ( ~ v1_xboole_0(A_162)
      | k5_relat_1(A_162,B_163) = k1_xboole_0
      | ~ v1_relat_1(B_163)
      | ~ v1_relat_1(A_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_347])).

tff(c_353,plain,(
    ! [B_163] :
      ( k5_relat_1(k1_xboole_0,B_163) = k1_xboole_0
      | ~ v1_relat_1(B_163)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_351])).

tff(c_357,plain,(
    ! [B_164] :
      ( k5_relat_1(k1_xboole_0,B_164) = k1_xboole_0
      | ~ v1_relat_1(B_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_353])).

tff(c_363,plain,(
    k5_relat_1(k1_xboole_0,'#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_357])).

tff(c_368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_363])).

tff(c_369,plain,(
    k5_relat_1('#skF_7',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_651,plain,(
    ! [A_227,B_228,C_229] :
      ( r2_hidden(k4_tarski('#skF_4'(A_227,B_228,C_229),'#skF_3'(A_227,B_228,C_229)),B_228)
      | r2_hidden(k4_tarski('#skF_5'(A_227,B_228,C_229),'#skF_6'(A_227,B_228,C_229)),C_229)
      | k5_relat_1(A_227,B_228) = C_229
      | ~ v1_relat_1(C_229)
      | ~ v1_relat_1(B_228)
      | ~ v1_relat_1(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_370,plain,(
    k5_relat_1(k1_xboole_0,'#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_411,plain,(
    ! [D_180,E_181,A_182,B_183] :
      ( r2_hidden(k4_tarski(D_180,'#skF_1'(E_181,k5_relat_1(A_182,B_183),D_180,A_182,B_183)),A_182)
      | ~ r2_hidden(k4_tarski(D_180,E_181),k5_relat_1(A_182,B_183))
      | ~ v1_relat_1(k5_relat_1(A_182,B_183))
      | ~ v1_relat_1(B_183)
      | ~ v1_relat_1(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_423,plain,(
    ! [D_180,E_181] :
      ( r2_hidden(k4_tarski(D_180,'#skF_1'(E_181,k1_xboole_0,D_180,k1_xboole_0,'#skF_7')),k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_180,E_181),k5_relat_1(k1_xboole_0,'#skF_7'))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,'#skF_7'))
      | ~ v1_relat_1('#skF_7')
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_411])).

tff(c_429,plain,(
    ! [D_184,E_185] :
      ( r2_hidden(k4_tarski(D_184,'#skF_1'(E_185,k1_xboole_0,D_184,k1_xboole_0,'#skF_7')),k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_184,E_185),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_28,c_33,c_370,c_370,c_423])).

tff(c_434,plain,(
    ! [D_184,E_185] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_184,E_185),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_429,c_24])).

tff(c_440,plain,(
    ! [D_184,E_185] : ~ r2_hidden(k4_tarski(D_184,E_185),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_434])).

tff(c_691,plain,(
    ! [A_227,C_229] :
      ( r2_hidden(k4_tarski('#skF_5'(A_227,k1_xboole_0,C_229),'#skF_6'(A_227,k1_xboole_0,C_229)),C_229)
      | k5_relat_1(A_227,k1_xboole_0) = C_229
      | ~ v1_relat_1(C_229)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_227) ) ),
    inference(resolution,[status(thm)],[c_651,c_440])).

tff(c_775,plain,(
    ! [A_230,C_231] :
      ( r2_hidden(k4_tarski('#skF_5'(A_230,k1_xboole_0,C_231),'#skF_6'(A_230,k1_xboole_0,C_231)),C_231)
      | k5_relat_1(A_230,k1_xboole_0) = C_231
      | ~ v1_relat_1(C_231)
      | ~ v1_relat_1(A_230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_691])).

tff(c_815,plain,(
    ! [A_230] :
      ( k5_relat_1(A_230,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_230) ) ),
    inference(resolution,[status(thm)],[c_775,c_440])).

tff(c_840,plain,(
    ! [A_232] :
      ( k5_relat_1(A_232,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_815])).

tff(c_846,plain,(
    k5_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_840])).

tff(c_851,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_369,c_846])).

%------------------------------------------------------------------------------
