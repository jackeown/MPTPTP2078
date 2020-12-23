%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:20 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 208 expanded)
%              Number of leaves         :   29 (  84 expanded)
%              Depth                    :   19
%              Number of atoms          :  147 ( 460 expanded)
%              Number of equality atoms :   25 ( 115 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_9 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_5 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

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

tff('#skF_10',type,(
    '#skF_10': $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_90,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_98,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_82,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_44,plain,
    ( k5_relat_1('#skF_11',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_11') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_88,plain,(
    k5_relat_1(k1_xboole_0,'#skF_11') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_46,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_12,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_70,plain,(
    ! [A_125,B_126] : v1_relat_1(k2_zfmisc_1(A_125,B_126)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_72,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_70])).

tff(c_38,plain,(
    ! [A_115,B_116] :
      ( v1_relat_1(k5_relat_1(A_115,B_116))
      | ~ v1_relat_1(B_116)
      | ~ v1_relat_1(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_42,plain,(
    ! [A_119] :
      ( k1_xboole_0 = A_119
      | r2_hidden(k4_tarski('#skF_9'(A_119),'#skF_10'(A_119)),A_119)
      | ~ v1_relat_1(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_36,plain,(
    ! [D_107,B_68,E_108,A_16] :
      ( r2_hidden(k4_tarski(D_107,'#skF_3'(B_68,D_107,E_108,k5_relat_1(A_16,B_68),A_16)),A_16)
      | ~ r2_hidden(k4_tarski(D_107,E_108),k5_relat_1(A_16,B_68))
      | ~ v1_relat_1(k5_relat_1(A_16,B_68))
      | ~ v1_relat_1(B_68)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_34,plain,(
    ! [B_68,D_107,E_108,A_16] :
      ( r2_hidden(k4_tarski('#skF_3'(B_68,D_107,E_108,k5_relat_1(A_16,B_68),A_16),E_108),B_68)
      | ~ r2_hidden(k4_tarski(D_107,E_108),k5_relat_1(A_16,B_68))
      | ~ v1_relat_1(k5_relat_1(A_16,B_68))
      | ~ v1_relat_1(B_68)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_188,plain,(
    ! [B_171,D_172,E_173,A_174] :
      ( r2_hidden(k4_tarski('#skF_3'(B_171,D_172,E_173,k5_relat_1(A_174,B_171),A_174),E_173),B_171)
      | ~ r2_hidden(k4_tarski(D_172,E_173),k5_relat_1(A_174,B_171))
      | ~ v1_relat_1(k5_relat_1(A_174,B_171))
      | ~ v1_relat_1(B_171)
      | ~ v1_relat_1(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_8,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_92,plain,(
    ! [A_137,B_138,C_139] :
      ( ~ r1_xboole_0(A_137,B_138)
      | ~ r2_hidden(C_139,B_138)
      | ~ r2_hidden(C_139,A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_95,plain,(
    ! [C_139,A_6] :
      ( ~ r2_hidden(C_139,k1_xboole_0)
      | ~ r2_hidden(C_139,A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_92])).

tff(c_193,plain,(
    ! [D_172,E_173,A_174,A_6] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(k1_xboole_0,D_172,E_173,k5_relat_1(A_174,k1_xboole_0),A_174),E_173),A_6)
      | ~ r2_hidden(k4_tarski(D_172,E_173),k5_relat_1(A_174,k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_174,k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_174) ) ),
    inference(resolution,[status(thm)],[c_188,c_95])).

tff(c_207,plain,(
    ! [D_178,E_179,A_180,A_181] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(k1_xboole_0,D_178,E_179,k5_relat_1(A_180,k1_xboole_0),A_180),E_179),A_181)
      | ~ r2_hidden(k4_tarski(D_178,E_179),k5_relat_1(A_180,k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_180,k1_xboole_0))
      | ~ v1_relat_1(A_180) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_193])).

tff(c_215,plain,(
    ! [D_107,E_108,A_16] :
      ( ~ r2_hidden(k4_tarski(D_107,E_108),k5_relat_1(A_16,k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_16,k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_16) ) ),
    inference(resolution,[status(thm)],[c_34,c_207])).

tff(c_220,plain,(
    ! [D_182,E_183,A_184] :
      ( ~ r2_hidden(k4_tarski(D_182,E_183),k5_relat_1(A_184,k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_184,k1_xboole_0))
      | ~ v1_relat_1(A_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_215])).

tff(c_239,plain,(
    ! [A_185] :
      ( ~ v1_relat_1(A_185)
      | k5_relat_1(A_185,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_185,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_42,c_220])).

tff(c_243,plain,(
    ! [A_115] :
      ( k5_relat_1(A_115,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_115) ) ),
    inference(resolution,[status(thm)],[c_38,c_239])).

tff(c_247,plain,(
    ! [A_186] :
      ( k5_relat_1(A_186,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_243])).

tff(c_260,plain,(
    k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_72,c_247])).

tff(c_219,plain,(
    ! [D_107,E_108,A_16] :
      ( ~ r2_hidden(k4_tarski(D_107,E_108),k5_relat_1(A_16,k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_16,k1_xboole_0))
      | ~ v1_relat_1(A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_215])).

tff(c_290,plain,(
    ! [D_107,E_108] :
      ( ~ r2_hidden(k4_tarski(D_107,E_108),k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_219])).

tff(c_344,plain,(
    ! [D_191,E_192] : ~ r2_hidden(k4_tarski(D_191,E_192),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_72,c_260,c_290])).

tff(c_348,plain,(
    ! [D_107,E_108,B_68] :
      ( ~ r2_hidden(k4_tarski(D_107,E_108),k5_relat_1(k1_xboole_0,B_68))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_68))
      | ~ v1_relat_1(B_68)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_36,c_344])).

tff(c_468,plain,(
    ! [D_197,E_198,B_199] :
      ( ~ r2_hidden(k4_tarski(D_197,E_198),k5_relat_1(k1_xboole_0,B_199))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_199))
      | ~ v1_relat_1(B_199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_348])).

tff(c_496,plain,(
    ! [B_200] :
      ( ~ v1_relat_1(B_200)
      | k5_relat_1(k1_xboole_0,B_200) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_200)) ) ),
    inference(resolution,[status(thm)],[c_42,c_468])).

tff(c_503,plain,(
    ! [B_116] :
      ( k5_relat_1(k1_xboole_0,B_116) = k1_xboole_0
      | ~ v1_relat_1(B_116)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_38,c_496])).

tff(c_509,plain,(
    ! [B_201] :
      ( k5_relat_1(k1_xboole_0,B_201) = k1_xboole_0
      | ~ v1_relat_1(B_201) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_503])).

tff(c_521,plain,(
    k5_relat_1(k1_xboole_0,'#skF_11') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_509])).

tff(c_529,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_521])).

tff(c_530,plain,(
    k5_relat_1('#skF_11',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_730,plain,(
    ! [B_256,D_257,E_258,A_259] :
      ( r2_hidden(k4_tarski('#skF_3'(B_256,D_257,E_258,k5_relat_1(A_259,B_256),A_259),E_258),B_256)
      | ~ r2_hidden(k4_tarski(D_257,E_258),k5_relat_1(A_259,B_256))
      | ~ v1_relat_1(k5_relat_1(A_259,B_256))
      | ~ v1_relat_1(B_256)
      | ~ v1_relat_1(A_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_544,plain,(
    ! [A_208,B_209,C_210] :
      ( ~ r1_xboole_0(A_208,B_209)
      | ~ r2_hidden(C_210,B_209)
      | ~ r2_hidden(C_210,A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_547,plain,(
    ! [C_210,A_6] :
      ( ~ r2_hidden(C_210,k1_xboole_0)
      | ~ r2_hidden(C_210,A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_544])).

tff(c_739,plain,(
    ! [D_257,E_258,A_259,A_6] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(k1_xboole_0,D_257,E_258,k5_relat_1(A_259,k1_xboole_0),A_259),E_258),A_6)
      | ~ r2_hidden(k4_tarski(D_257,E_258),k5_relat_1(A_259,k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_259,k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_259) ) ),
    inference(resolution,[status(thm)],[c_730,c_547])).

tff(c_773,plain,(
    ! [D_267,E_268,A_269,A_270] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(k1_xboole_0,D_267,E_268,k5_relat_1(A_269,k1_xboole_0),A_269),E_268),A_270)
      | ~ r2_hidden(k4_tarski(D_267,E_268),k5_relat_1(A_269,k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_269,k1_xboole_0))
      | ~ v1_relat_1(A_269) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_739])).

tff(c_781,plain,(
    ! [D_107,E_108,A_16] :
      ( ~ r2_hidden(k4_tarski(D_107,E_108),k5_relat_1(A_16,k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_16,k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_16) ) ),
    inference(resolution,[status(thm)],[c_34,c_773])).

tff(c_791,plain,(
    ! [D_271,E_272,A_273] :
      ( ~ r2_hidden(k4_tarski(D_271,E_272),k5_relat_1(A_273,k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_273,k1_xboole_0))
      | ~ v1_relat_1(A_273) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_781])).

tff(c_819,plain,(
    ! [A_274] :
      ( ~ v1_relat_1(A_274)
      | k5_relat_1(A_274,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_274,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_42,c_791])).

tff(c_823,plain,(
    ! [A_115] :
      ( k5_relat_1(A_115,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_115) ) ),
    inference(resolution,[status(thm)],[c_38,c_819])).

tff(c_827,plain,(
    ! [A_275] :
      ( k5_relat_1(A_275,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_275) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_823])).

tff(c_839,plain,(
    k5_relat_1('#skF_11',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_827])).

tff(c_846,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_530,c_839])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:31:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.50  
% 3.13/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.50  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_9 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_5 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_1
% 3.13/1.50  
% 3.13/1.50  %Foreground sorts:
% 3.13/1.50  
% 3.13/1.50  
% 3.13/1.50  %Background operators:
% 3.13/1.50  
% 3.13/1.50  
% 3.13/1.50  %Foreground operators:
% 3.13/1.50  tff('#skF_9', type, '#skF_9': $i > $i).
% 3.13/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.13/1.50  tff('#skF_11', type, '#skF_11': $i).
% 3.13/1.50  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.13/1.50  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.13/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.13/1.50  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.13/1.50  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.13/1.50  tff('#skF_10', type, '#skF_10': $i > $i).
% 3.13/1.50  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.13/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.13/1.50  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.13/1.50  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 3.13/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.13/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.13/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.13/1.50  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 3.13/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.13/1.50  
% 3.13/1.52  tff(f_105, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 3.13/1.52  tff(f_51, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.13/1.52  tff(f_90, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.13/1.52  tff(f_88, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.13/1.52  tff(f_98, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 3.13/1.52  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_1)).
% 3.13/1.52  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.13/1.52  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.13/1.52  tff(c_44, plain, (k5_relat_1('#skF_11', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_11')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.13/1.52  tff(c_88, plain, (k5_relat_1(k1_xboole_0, '#skF_11')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_44])).
% 3.13/1.52  tff(c_46, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.13/1.52  tff(c_12, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.13/1.52  tff(c_70, plain, (![A_125, B_126]: (v1_relat_1(k2_zfmisc_1(A_125, B_126)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.13/1.52  tff(c_72, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_70])).
% 3.13/1.52  tff(c_38, plain, (![A_115, B_116]: (v1_relat_1(k5_relat_1(A_115, B_116)) | ~v1_relat_1(B_116) | ~v1_relat_1(A_115))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.13/1.52  tff(c_42, plain, (![A_119]: (k1_xboole_0=A_119 | r2_hidden(k4_tarski('#skF_9'(A_119), '#skF_10'(A_119)), A_119) | ~v1_relat_1(A_119))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.13/1.52  tff(c_36, plain, (![D_107, B_68, E_108, A_16]: (r2_hidden(k4_tarski(D_107, '#skF_3'(B_68, D_107, E_108, k5_relat_1(A_16, B_68), A_16)), A_16) | ~r2_hidden(k4_tarski(D_107, E_108), k5_relat_1(A_16, B_68)) | ~v1_relat_1(k5_relat_1(A_16, B_68)) | ~v1_relat_1(B_68) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.13/1.52  tff(c_34, plain, (![B_68, D_107, E_108, A_16]: (r2_hidden(k4_tarski('#skF_3'(B_68, D_107, E_108, k5_relat_1(A_16, B_68), A_16), E_108), B_68) | ~r2_hidden(k4_tarski(D_107, E_108), k5_relat_1(A_16, B_68)) | ~v1_relat_1(k5_relat_1(A_16, B_68)) | ~v1_relat_1(B_68) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.13/1.52  tff(c_188, plain, (![B_171, D_172, E_173, A_174]: (r2_hidden(k4_tarski('#skF_3'(B_171, D_172, E_173, k5_relat_1(A_174, B_171), A_174), E_173), B_171) | ~r2_hidden(k4_tarski(D_172, E_173), k5_relat_1(A_174, B_171)) | ~v1_relat_1(k5_relat_1(A_174, B_171)) | ~v1_relat_1(B_171) | ~v1_relat_1(A_174))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.13/1.52  tff(c_8, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.13/1.52  tff(c_92, plain, (![A_137, B_138, C_139]: (~r1_xboole_0(A_137, B_138) | ~r2_hidden(C_139, B_138) | ~r2_hidden(C_139, A_137))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.13/1.52  tff(c_95, plain, (![C_139, A_6]: (~r2_hidden(C_139, k1_xboole_0) | ~r2_hidden(C_139, A_6))), inference(resolution, [status(thm)], [c_8, c_92])).
% 3.13/1.52  tff(c_193, plain, (![D_172, E_173, A_174, A_6]: (~r2_hidden(k4_tarski('#skF_3'(k1_xboole_0, D_172, E_173, k5_relat_1(A_174, k1_xboole_0), A_174), E_173), A_6) | ~r2_hidden(k4_tarski(D_172, E_173), k5_relat_1(A_174, k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_174, k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_174))), inference(resolution, [status(thm)], [c_188, c_95])).
% 3.13/1.52  tff(c_207, plain, (![D_178, E_179, A_180, A_181]: (~r2_hidden(k4_tarski('#skF_3'(k1_xboole_0, D_178, E_179, k5_relat_1(A_180, k1_xboole_0), A_180), E_179), A_181) | ~r2_hidden(k4_tarski(D_178, E_179), k5_relat_1(A_180, k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_180, k1_xboole_0)) | ~v1_relat_1(A_180))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_193])).
% 3.13/1.52  tff(c_215, plain, (![D_107, E_108, A_16]: (~r2_hidden(k4_tarski(D_107, E_108), k5_relat_1(A_16, k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_16, k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_16))), inference(resolution, [status(thm)], [c_34, c_207])).
% 3.13/1.52  tff(c_220, plain, (![D_182, E_183, A_184]: (~r2_hidden(k4_tarski(D_182, E_183), k5_relat_1(A_184, k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_184, k1_xboole_0)) | ~v1_relat_1(A_184))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_215])).
% 3.13/1.52  tff(c_239, plain, (![A_185]: (~v1_relat_1(A_185) | k5_relat_1(A_185, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_185, k1_xboole_0)))), inference(resolution, [status(thm)], [c_42, c_220])).
% 3.13/1.52  tff(c_243, plain, (![A_115]: (k5_relat_1(A_115, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_115))), inference(resolution, [status(thm)], [c_38, c_239])).
% 3.13/1.52  tff(c_247, plain, (![A_186]: (k5_relat_1(A_186, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_186))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_243])).
% 3.13/1.52  tff(c_260, plain, (k5_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_72, c_247])).
% 3.13/1.52  tff(c_219, plain, (![D_107, E_108, A_16]: (~r2_hidden(k4_tarski(D_107, E_108), k5_relat_1(A_16, k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_16, k1_xboole_0)) | ~v1_relat_1(A_16))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_215])).
% 3.13/1.52  tff(c_290, plain, (![D_107, E_108]: (~r2_hidden(k4_tarski(D_107, E_108), k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_260, c_219])).
% 3.13/1.52  tff(c_344, plain, (![D_191, E_192]: (~r2_hidden(k4_tarski(D_191, E_192), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_72, c_260, c_290])).
% 3.13/1.52  tff(c_348, plain, (![D_107, E_108, B_68]: (~r2_hidden(k4_tarski(D_107, E_108), k5_relat_1(k1_xboole_0, B_68)) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_68)) | ~v1_relat_1(B_68) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_36, c_344])).
% 3.13/1.52  tff(c_468, plain, (![D_197, E_198, B_199]: (~r2_hidden(k4_tarski(D_197, E_198), k5_relat_1(k1_xboole_0, B_199)) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_199)) | ~v1_relat_1(B_199))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_348])).
% 3.13/1.52  tff(c_496, plain, (![B_200]: (~v1_relat_1(B_200) | k5_relat_1(k1_xboole_0, B_200)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_200)))), inference(resolution, [status(thm)], [c_42, c_468])).
% 3.13/1.52  tff(c_503, plain, (![B_116]: (k5_relat_1(k1_xboole_0, B_116)=k1_xboole_0 | ~v1_relat_1(B_116) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_38, c_496])).
% 3.13/1.52  tff(c_509, plain, (![B_201]: (k5_relat_1(k1_xboole_0, B_201)=k1_xboole_0 | ~v1_relat_1(B_201))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_503])).
% 3.13/1.52  tff(c_521, plain, (k5_relat_1(k1_xboole_0, '#skF_11')=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_509])).
% 3.13/1.52  tff(c_529, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_521])).
% 3.13/1.52  tff(c_530, plain, (k5_relat_1('#skF_11', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_44])).
% 3.13/1.52  tff(c_730, plain, (![B_256, D_257, E_258, A_259]: (r2_hidden(k4_tarski('#skF_3'(B_256, D_257, E_258, k5_relat_1(A_259, B_256), A_259), E_258), B_256) | ~r2_hidden(k4_tarski(D_257, E_258), k5_relat_1(A_259, B_256)) | ~v1_relat_1(k5_relat_1(A_259, B_256)) | ~v1_relat_1(B_256) | ~v1_relat_1(A_259))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.13/1.52  tff(c_544, plain, (![A_208, B_209, C_210]: (~r1_xboole_0(A_208, B_209) | ~r2_hidden(C_210, B_209) | ~r2_hidden(C_210, A_208))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.13/1.52  tff(c_547, plain, (![C_210, A_6]: (~r2_hidden(C_210, k1_xboole_0) | ~r2_hidden(C_210, A_6))), inference(resolution, [status(thm)], [c_8, c_544])).
% 3.13/1.52  tff(c_739, plain, (![D_257, E_258, A_259, A_6]: (~r2_hidden(k4_tarski('#skF_3'(k1_xboole_0, D_257, E_258, k5_relat_1(A_259, k1_xboole_0), A_259), E_258), A_6) | ~r2_hidden(k4_tarski(D_257, E_258), k5_relat_1(A_259, k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_259, k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_259))), inference(resolution, [status(thm)], [c_730, c_547])).
% 3.13/1.52  tff(c_773, plain, (![D_267, E_268, A_269, A_270]: (~r2_hidden(k4_tarski('#skF_3'(k1_xboole_0, D_267, E_268, k5_relat_1(A_269, k1_xboole_0), A_269), E_268), A_270) | ~r2_hidden(k4_tarski(D_267, E_268), k5_relat_1(A_269, k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_269, k1_xboole_0)) | ~v1_relat_1(A_269))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_739])).
% 3.13/1.52  tff(c_781, plain, (![D_107, E_108, A_16]: (~r2_hidden(k4_tarski(D_107, E_108), k5_relat_1(A_16, k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_16, k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_16))), inference(resolution, [status(thm)], [c_34, c_773])).
% 3.13/1.52  tff(c_791, plain, (![D_271, E_272, A_273]: (~r2_hidden(k4_tarski(D_271, E_272), k5_relat_1(A_273, k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_273, k1_xboole_0)) | ~v1_relat_1(A_273))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_781])).
% 3.13/1.52  tff(c_819, plain, (![A_274]: (~v1_relat_1(A_274) | k5_relat_1(A_274, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_274, k1_xboole_0)))), inference(resolution, [status(thm)], [c_42, c_791])).
% 3.13/1.52  tff(c_823, plain, (![A_115]: (k5_relat_1(A_115, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_115))), inference(resolution, [status(thm)], [c_38, c_819])).
% 3.13/1.52  tff(c_827, plain, (![A_275]: (k5_relat_1(A_275, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_275))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_823])).
% 3.13/1.52  tff(c_839, plain, (k5_relat_1('#skF_11', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_827])).
% 3.13/1.52  tff(c_846, plain, $false, inference(negUnitSimplification, [status(thm)], [c_530, c_839])).
% 3.13/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.52  
% 3.13/1.52  Inference rules
% 3.13/1.52  ----------------------
% 3.13/1.52  #Ref     : 0
% 3.13/1.52  #Sup     : 154
% 3.13/1.52  #Fact    : 0
% 3.13/1.52  #Define  : 0
% 3.13/1.52  #Split   : 2
% 3.13/1.52  #Chain   : 0
% 3.13/1.52  #Close   : 0
% 3.13/1.52  
% 3.13/1.52  Ordering : KBO
% 3.13/1.52  
% 3.13/1.52  Simplification rules
% 3.13/1.52  ----------------------
% 3.13/1.52  #Subsume      : 25
% 3.13/1.52  #Demod        : 168
% 3.13/1.52  #Tautology    : 54
% 3.13/1.52  #SimpNegUnit  : 6
% 3.13/1.52  #BackRed      : 15
% 3.13/1.52  
% 3.13/1.52  #Partial instantiations: 0
% 3.13/1.52  #Strategies tried      : 1
% 3.13/1.52  
% 3.13/1.52  Timing (in seconds)
% 3.13/1.52  ----------------------
% 3.27/1.52  Preprocessing        : 0.32
% 3.27/1.52  Parsing              : 0.18
% 3.27/1.52  CNF conversion       : 0.03
% 3.27/1.52  Main loop            : 0.39
% 3.27/1.53  Inferencing          : 0.15
% 3.27/1.53  Reduction            : 0.11
% 3.27/1.53  Demodulation         : 0.08
% 3.27/1.53  BG Simplification    : 0.02
% 3.27/1.53  Subsumption          : 0.08
% 3.27/1.53  Abstraction          : 0.02
% 3.27/1.53  MUC search           : 0.00
% 3.27/1.53  Cooper               : 0.00
% 3.27/1.53  Total                : 0.75
% 3.27/1.53  Index Insertion      : 0.00
% 3.27/1.53  Index Deletion       : 0.00
% 3.27/1.53  Index Matching       : 0.00
% 3.27/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
