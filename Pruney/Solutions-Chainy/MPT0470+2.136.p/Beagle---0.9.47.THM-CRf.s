%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:20 EST 2020

% Result     : Theorem 4.12s
% Output     : CNFRefutation 4.12s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 237 expanded)
%              Number of leaves         :   32 (  90 expanded)
%              Depth                    :   19
%              Number of atoms          :  151 ( 508 expanded)
%              Number of equality atoms :   23 (  85 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_9 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_5 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_52,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_76,axiom,(
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

tff(f_56,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_50,axiom,(
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

tff(c_46,plain,
    ( k5_relat_1('#skF_11',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_11') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_76,plain,(
    k5_relat_1(k1_xboole_0,'#skF_11') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_48,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_14,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_58,plain,(
    ! [A_125,B_126] :
      ( v1_relat_1(k3_xboole_0(A_125,B_126))
      | ~ v1_relat_1(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_61,plain,(
    ! [A_11] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_58])).

tff(c_71,plain,(
    ! [A_11] : ~ v1_relat_1(A_11) ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_74,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_48])).

tff(c_75,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_40,plain,(
    ! [A_115,B_116] :
      ( v1_relat_1(k5_relat_1(A_115,B_116))
      | ~ v1_relat_1(B_116)
      | ~ v1_relat_1(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_44,plain,(
    ! [A_119] :
      ( k1_xboole_0 = A_119
      | r2_hidden(k4_tarski('#skF_9'(A_119),'#skF_10'(A_119)),A_119)
      | ~ v1_relat_1(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_38,plain,(
    ! [D_107,B_68,E_108,A_16] :
      ( r2_hidden(k4_tarski(D_107,'#skF_3'(B_68,D_107,E_108,k5_relat_1(A_16,B_68),A_16)),A_16)
      | ~ r2_hidden(k4_tarski(D_107,E_108),k5_relat_1(A_16,B_68))
      | ~ v1_relat_1(k5_relat_1(A_16,B_68))
      | ~ v1_relat_1(B_68)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_36,plain,(
    ! [B_68,D_107,E_108,A_16] :
      ( r2_hidden(k4_tarski('#skF_3'(B_68,D_107,E_108,k5_relat_1(A_16,B_68),A_16),E_108),B_68)
      | ~ r2_hidden(k4_tarski(D_107,E_108),k5_relat_1(A_16,B_68))
      | ~ v1_relat_1(k5_relat_1(A_16,B_68))
      | ~ v1_relat_1(B_68)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_195,plain,(
    ! [B_169,D_170,E_171,A_172] :
      ( r2_hidden(k4_tarski('#skF_3'(B_169,D_170,E_171,k5_relat_1(A_172,B_169),A_172),E_171),B_169)
      | ~ r2_hidden(k4_tarski(D_170,E_171),k5_relat_1(A_172,B_169))
      | ~ v1_relat_1(k5_relat_1(A_172,B_169))
      | ~ v1_relat_1(B_169)
      | ~ v1_relat_1(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_18,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_98,plain,(
    ! [A_143,B_144,C_145] :
      ( ~ r1_xboole_0(A_143,B_144)
      | ~ r2_hidden(C_145,B_144)
      | ~ r2_hidden(C_145,A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_101,plain,(
    ! [C_145,A_13] :
      ( ~ r2_hidden(C_145,k1_xboole_0)
      | ~ r2_hidden(C_145,A_13) ) ),
    inference(resolution,[status(thm)],[c_18,c_98])).

tff(c_200,plain,(
    ! [D_170,E_171,A_172,A_13] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(k1_xboole_0,D_170,E_171,k5_relat_1(A_172,k1_xboole_0),A_172),E_171),A_13)
      | ~ r2_hidden(k4_tarski(D_170,E_171),k5_relat_1(A_172,k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_172,k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_172) ) ),
    inference(resolution,[status(thm)],[c_195,c_101])).

tff(c_574,plain,(
    ! [D_264,E_265,A_266,A_267] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(k1_xboole_0,D_264,E_265,k5_relat_1(A_266,k1_xboole_0),A_266),E_265),A_267)
      | ~ r2_hidden(k4_tarski(D_264,E_265),k5_relat_1(A_266,k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_266,k1_xboole_0))
      | ~ v1_relat_1(A_266) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_200])).

tff(c_582,plain,(
    ! [D_107,E_108,A_16] :
      ( ~ r2_hidden(k4_tarski(D_107,E_108),k5_relat_1(A_16,k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_16,k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_16) ) ),
    inference(resolution,[status(thm)],[c_36,c_574])).

tff(c_587,plain,(
    ! [D_268,E_269,A_270] :
      ( ~ r2_hidden(k4_tarski(D_268,E_269),k5_relat_1(A_270,k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_270,k1_xboole_0))
      | ~ v1_relat_1(A_270) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_582])).

tff(c_636,plain,(
    ! [A_271] :
      ( ~ v1_relat_1(A_271)
      | k5_relat_1(A_271,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_271,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_44,c_587])).

tff(c_640,plain,(
    ! [A_115] :
      ( k5_relat_1(A_115,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_115) ) ),
    inference(resolution,[status(thm)],[c_40,c_636])).

tff(c_644,plain,(
    ! [A_272] :
      ( k5_relat_1(A_272,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_272) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_640])).

tff(c_658,plain,(
    k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_75,c_644])).

tff(c_586,plain,(
    ! [D_107,E_108,A_16] :
      ( ~ r2_hidden(k4_tarski(D_107,E_108),k5_relat_1(A_16,k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_16,k1_xboole_0))
      | ~ v1_relat_1(A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_582])).

tff(c_664,plain,(
    ! [D_107,E_108] :
      ( ~ r2_hidden(k4_tarski(D_107,E_108),k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_658,c_586])).

tff(c_763,plain,(
    ! [D_278,E_279] : ~ r2_hidden(k4_tarski(D_278,E_279),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_75,c_658,c_664])).

tff(c_787,plain,(
    ! [D_107,E_108,B_68] :
      ( ~ r2_hidden(k4_tarski(D_107,E_108),k5_relat_1(k1_xboole_0,B_68))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_68))
      | ~ v1_relat_1(B_68)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_38,c_763])).

tff(c_934,plain,(
    ! [D_284,E_285,B_286] :
      ( ~ r2_hidden(k4_tarski(D_284,E_285),k5_relat_1(k1_xboole_0,B_286))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_286))
      | ~ v1_relat_1(B_286) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_787])).

tff(c_992,plain,(
    ! [B_287] :
      ( ~ v1_relat_1(B_287)
      | k5_relat_1(k1_xboole_0,B_287) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_287)) ) ),
    inference(resolution,[status(thm)],[c_44,c_934])).

tff(c_999,plain,(
    ! [B_116] :
      ( k5_relat_1(k1_xboole_0,B_116) = k1_xboole_0
      | ~ v1_relat_1(B_116)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_40,c_992])).

tff(c_1005,plain,(
    ! [B_288] :
      ( k5_relat_1(k1_xboole_0,B_288) = k1_xboole_0
      | ~ v1_relat_1(B_288) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_999])).

tff(c_1017,plain,(
    k5_relat_1(k1_xboole_0,'#skF_11') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_1005])).

tff(c_1025,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1017])).

tff(c_1026,plain,(
    k5_relat_1('#skF_11',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1155,plain,(
    ! [B_329,D_330,E_331,A_332] :
      ( r2_hidden(k4_tarski('#skF_3'(B_329,D_330,E_331,k5_relat_1(A_332,B_329),A_332),E_331),B_329)
      | ~ r2_hidden(k4_tarski(D_330,E_331),k5_relat_1(A_332,B_329))
      | ~ v1_relat_1(k5_relat_1(A_332,B_329))
      | ~ v1_relat_1(B_329)
      | ~ v1_relat_1(A_332) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1058,plain,(
    ! [A_303,B_304,C_305] :
      ( ~ r1_xboole_0(A_303,B_304)
      | ~ r2_hidden(C_305,B_304)
      | ~ r2_hidden(C_305,A_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1061,plain,(
    ! [C_305,A_13] :
      ( ~ r2_hidden(C_305,k1_xboole_0)
      | ~ r2_hidden(C_305,A_13) ) ),
    inference(resolution,[status(thm)],[c_18,c_1058])).

tff(c_1160,plain,(
    ! [D_330,E_331,A_332,A_13] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(k1_xboole_0,D_330,E_331,k5_relat_1(A_332,k1_xboole_0),A_332),E_331),A_13)
      | ~ r2_hidden(k4_tarski(D_330,E_331),k5_relat_1(A_332,k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_332,k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_332) ) ),
    inference(resolution,[status(thm)],[c_1155,c_1061])).

tff(c_1707,plain,(
    ! [D_440,E_441,A_442,A_443] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(k1_xboole_0,D_440,E_441,k5_relat_1(A_442,k1_xboole_0),A_442),E_441),A_443)
      | ~ r2_hidden(k4_tarski(D_440,E_441),k5_relat_1(A_442,k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_442,k1_xboole_0))
      | ~ v1_relat_1(A_442) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_1160])).

tff(c_1715,plain,(
    ! [D_107,E_108,A_16] :
      ( ~ r2_hidden(k4_tarski(D_107,E_108),k5_relat_1(A_16,k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_16,k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_16) ) ),
    inference(resolution,[status(thm)],[c_36,c_1707])).

tff(c_1740,plain,(
    ! [D_448,E_449,A_450] :
      ( ~ r2_hidden(k4_tarski(D_448,E_449),k5_relat_1(A_450,k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_450,k1_xboole_0))
      | ~ v1_relat_1(A_450) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_1715])).

tff(c_1798,plain,(
    ! [A_451] :
      ( ~ v1_relat_1(A_451)
      | k5_relat_1(A_451,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_451,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_44,c_1740])).

tff(c_1802,plain,(
    ! [A_115] :
      ( k5_relat_1(A_115,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_115) ) ),
    inference(resolution,[status(thm)],[c_40,c_1798])).

tff(c_1806,plain,(
    ! [A_452] :
      ( k5_relat_1(A_452,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_452) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_1802])).

tff(c_1818,plain,(
    k5_relat_1('#skF_11',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_1806])).

tff(c_1825,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1026,c_1818])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:02:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.12/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.12/1.68  
% 4.12/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.12/1.69  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_9 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_5 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_1
% 4.12/1.69  
% 4.12/1.69  %Foreground sorts:
% 4.12/1.69  
% 4.12/1.69  
% 4.12/1.69  %Background operators:
% 4.12/1.69  
% 4.12/1.69  
% 4.12/1.69  %Foreground operators:
% 4.12/1.69  tff('#skF_9', type, '#skF_9': $i > $i).
% 4.12/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.12/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.12/1.69  tff('#skF_11', type, '#skF_11': $i).
% 4.12/1.69  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 4.12/1.69  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.12/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.12/1.69  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.12/1.69  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.12/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.12/1.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.12/1.69  tff('#skF_10', type, '#skF_10': $i > $i).
% 4.12/1.69  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.12/1.69  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.12/1.69  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 4.12/1.69  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 4.12/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.12/1.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.12/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.12/1.69  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.12/1.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.12/1.69  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 4.12/1.69  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.12/1.69  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.12/1.69  
% 4.12/1.70  tff(f_101, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 4.12/1.70  tff(f_52, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.12/1.70  tff(f_86, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 4.12/1.70  tff(f_82, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 4.12/1.70  tff(f_94, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 4.12/1.70  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_1)).
% 4.12/1.70  tff(f_56, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.12/1.70  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.12/1.70  tff(c_46, plain, (k5_relat_1('#skF_11', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_11')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.12/1.70  tff(c_76, plain, (k5_relat_1(k1_xboole_0, '#skF_11')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_46])).
% 4.12/1.70  tff(c_48, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.12/1.70  tff(c_14, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.12/1.70  tff(c_58, plain, (![A_125, B_126]: (v1_relat_1(k3_xboole_0(A_125, B_126)) | ~v1_relat_1(A_125))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.12/1.70  tff(c_61, plain, (![A_11]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_11))), inference(superposition, [status(thm), theory('equality')], [c_14, c_58])).
% 4.12/1.70  tff(c_71, plain, (![A_11]: (~v1_relat_1(A_11))), inference(splitLeft, [status(thm)], [c_61])).
% 4.12/1.70  tff(c_74, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_48])).
% 4.12/1.70  tff(c_75, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_61])).
% 4.12/1.70  tff(c_40, plain, (![A_115, B_116]: (v1_relat_1(k5_relat_1(A_115, B_116)) | ~v1_relat_1(B_116) | ~v1_relat_1(A_115))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.12/1.70  tff(c_44, plain, (![A_119]: (k1_xboole_0=A_119 | r2_hidden(k4_tarski('#skF_9'(A_119), '#skF_10'(A_119)), A_119) | ~v1_relat_1(A_119))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.12/1.70  tff(c_38, plain, (![D_107, B_68, E_108, A_16]: (r2_hidden(k4_tarski(D_107, '#skF_3'(B_68, D_107, E_108, k5_relat_1(A_16, B_68), A_16)), A_16) | ~r2_hidden(k4_tarski(D_107, E_108), k5_relat_1(A_16, B_68)) | ~v1_relat_1(k5_relat_1(A_16, B_68)) | ~v1_relat_1(B_68) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.12/1.70  tff(c_36, plain, (![B_68, D_107, E_108, A_16]: (r2_hidden(k4_tarski('#skF_3'(B_68, D_107, E_108, k5_relat_1(A_16, B_68), A_16), E_108), B_68) | ~r2_hidden(k4_tarski(D_107, E_108), k5_relat_1(A_16, B_68)) | ~v1_relat_1(k5_relat_1(A_16, B_68)) | ~v1_relat_1(B_68) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.12/1.70  tff(c_195, plain, (![B_169, D_170, E_171, A_172]: (r2_hidden(k4_tarski('#skF_3'(B_169, D_170, E_171, k5_relat_1(A_172, B_169), A_172), E_171), B_169) | ~r2_hidden(k4_tarski(D_170, E_171), k5_relat_1(A_172, B_169)) | ~v1_relat_1(k5_relat_1(A_172, B_169)) | ~v1_relat_1(B_169) | ~v1_relat_1(A_172))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.12/1.70  tff(c_18, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.12/1.70  tff(c_98, plain, (![A_143, B_144, C_145]: (~r1_xboole_0(A_143, B_144) | ~r2_hidden(C_145, B_144) | ~r2_hidden(C_145, A_143))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.12/1.70  tff(c_101, plain, (![C_145, A_13]: (~r2_hidden(C_145, k1_xboole_0) | ~r2_hidden(C_145, A_13))), inference(resolution, [status(thm)], [c_18, c_98])).
% 4.12/1.70  tff(c_200, plain, (![D_170, E_171, A_172, A_13]: (~r2_hidden(k4_tarski('#skF_3'(k1_xboole_0, D_170, E_171, k5_relat_1(A_172, k1_xboole_0), A_172), E_171), A_13) | ~r2_hidden(k4_tarski(D_170, E_171), k5_relat_1(A_172, k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_172, k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_172))), inference(resolution, [status(thm)], [c_195, c_101])).
% 4.12/1.70  tff(c_574, plain, (![D_264, E_265, A_266, A_267]: (~r2_hidden(k4_tarski('#skF_3'(k1_xboole_0, D_264, E_265, k5_relat_1(A_266, k1_xboole_0), A_266), E_265), A_267) | ~r2_hidden(k4_tarski(D_264, E_265), k5_relat_1(A_266, k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_266, k1_xboole_0)) | ~v1_relat_1(A_266))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_200])).
% 4.12/1.70  tff(c_582, plain, (![D_107, E_108, A_16]: (~r2_hidden(k4_tarski(D_107, E_108), k5_relat_1(A_16, k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_16, k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_16))), inference(resolution, [status(thm)], [c_36, c_574])).
% 4.12/1.70  tff(c_587, plain, (![D_268, E_269, A_270]: (~r2_hidden(k4_tarski(D_268, E_269), k5_relat_1(A_270, k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_270, k1_xboole_0)) | ~v1_relat_1(A_270))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_582])).
% 4.12/1.70  tff(c_636, plain, (![A_271]: (~v1_relat_1(A_271) | k5_relat_1(A_271, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_271, k1_xboole_0)))), inference(resolution, [status(thm)], [c_44, c_587])).
% 4.12/1.70  tff(c_640, plain, (![A_115]: (k5_relat_1(A_115, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_115))), inference(resolution, [status(thm)], [c_40, c_636])).
% 4.12/1.70  tff(c_644, plain, (![A_272]: (k5_relat_1(A_272, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_272))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_640])).
% 4.12/1.70  tff(c_658, plain, (k5_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_75, c_644])).
% 4.12/1.70  tff(c_586, plain, (![D_107, E_108, A_16]: (~r2_hidden(k4_tarski(D_107, E_108), k5_relat_1(A_16, k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_16, k1_xboole_0)) | ~v1_relat_1(A_16))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_582])).
% 4.12/1.70  tff(c_664, plain, (![D_107, E_108]: (~r2_hidden(k4_tarski(D_107, E_108), k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_658, c_586])).
% 4.12/1.70  tff(c_763, plain, (![D_278, E_279]: (~r2_hidden(k4_tarski(D_278, E_279), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_75, c_658, c_664])).
% 4.12/1.70  tff(c_787, plain, (![D_107, E_108, B_68]: (~r2_hidden(k4_tarski(D_107, E_108), k5_relat_1(k1_xboole_0, B_68)) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_68)) | ~v1_relat_1(B_68) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_38, c_763])).
% 4.12/1.70  tff(c_934, plain, (![D_284, E_285, B_286]: (~r2_hidden(k4_tarski(D_284, E_285), k5_relat_1(k1_xboole_0, B_286)) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_286)) | ~v1_relat_1(B_286))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_787])).
% 4.12/1.70  tff(c_992, plain, (![B_287]: (~v1_relat_1(B_287) | k5_relat_1(k1_xboole_0, B_287)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_287)))), inference(resolution, [status(thm)], [c_44, c_934])).
% 4.12/1.70  tff(c_999, plain, (![B_116]: (k5_relat_1(k1_xboole_0, B_116)=k1_xboole_0 | ~v1_relat_1(B_116) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_40, c_992])).
% 4.12/1.70  tff(c_1005, plain, (![B_288]: (k5_relat_1(k1_xboole_0, B_288)=k1_xboole_0 | ~v1_relat_1(B_288))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_999])).
% 4.12/1.70  tff(c_1017, plain, (k5_relat_1(k1_xboole_0, '#skF_11')=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_1005])).
% 4.12/1.70  tff(c_1025, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_1017])).
% 4.12/1.70  tff(c_1026, plain, (k5_relat_1('#skF_11', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_46])).
% 4.12/1.70  tff(c_1155, plain, (![B_329, D_330, E_331, A_332]: (r2_hidden(k4_tarski('#skF_3'(B_329, D_330, E_331, k5_relat_1(A_332, B_329), A_332), E_331), B_329) | ~r2_hidden(k4_tarski(D_330, E_331), k5_relat_1(A_332, B_329)) | ~v1_relat_1(k5_relat_1(A_332, B_329)) | ~v1_relat_1(B_329) | ~v1_relat_1(A_332))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.12/1.70  tff(c_1058, plain, (![A_303, B_304, C_305]: (~r1_xboole_0(A_303, B_304) | ~r2_hidden(C_305, B_304) | ~r2_hidden(C_305, A_303))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.12/1.70  tff(c_1061, plain, (![C_305, A_13]: (~r2_hidden(C_305, k1_xboole_0) | ~r2_hidden(C_305, A_13))), inference(resolution, [status(thm)], [c_18, c_1058])).
% 4.12/1.70  tff(c_1160, plain, (![D_330, E_331, A_332, A_13]: (~r2_hidden(k4_tarski('#skF_3'(k1_xboole_0, D_330, E_331, k5_relat_1(A_332, k1_xboole_0), A_332), E_331), A_13) | ~r2_hidden(k4_tarski(D_330, E_331), k5_relat_1(A_332, k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_332, k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_332))), inference(resolution, [status(thm)], [c_1155, c_1061])).
% 4.12/1.70  tff(c_1707, plain, (![D_440, E_441, A_442, A_443]: (~r2_hidden(k4_tarski('#skF_3'(k1_xboole_0, D_440, E_441, k5_relat_1(A_442, k1_xboole_0), A_442), E_441), A_443) | ~r2_hidden(k4_tarski(D_440, E_441), k5_relat_1(A_442, k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_442, k1_xboole_0)) | ~v1_relat_1(A_442))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_1160])).
% 4.12/1.70  tff(c_1715, plain, (![D_107, E_108, A_16]: (~r2_hidden(k4_tarski(D_107, E_108), k5_relat_1(A_16, k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_16, k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_16))), inference(resolution, [status(thm)], [c_36, c_1707])).
% 4.12/1.70  tff(c_1740, plain, (![D_448, E_449, A_450]: (~r2_hidden(k4_tarski(D_448, E_449), k5_relat_1(A_450, k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_450, k1_xboole_0)) | ~v1_relat_1(A_450))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_1715])).
% 4.12/1.70  tff(c_1798, plain, (![A_451]: (~v1_relat_1(A_451) | k5_relat_1(A_451, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_451, k1_xboole_0)))), inference(resolution, [status(thm)], [c_44, c_1740])).
% 4.12/1.70  tff(c_1802, plain, (![A_115]: (k5_relat_1(A_115, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_115))), inference(resolution, [status(thm)], [c_40, c_1798])).
% 4.12/1.70  tff(c_1806, plain, (![A_452]: (k5_relat_1(A_452, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_452))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_1802])).
% 4.12/1.70  tff(c_1818, plain, (k5_relat_1('#skF_11', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_1806])).
% 4.12/1.70  tff(c_1825, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1026, c_1818])).
% 4.12/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.12/1.70  
% 4.12/1.70  Inference rules
% 4.12/1.70  ----------------------
% 4.12/1.70  #Ref     : 0
% 4.12/1.70  #Sup     : 390
% 4.12/1.70  #Fact    : 0
% 4.12/1.70  #Define  : 0
% 4.12/1.70  #Split   : 5
% 4.12/1.70  #Chain   : 0
% 4.12/1.70  #Close   : 0
% 4.12/1.70  
% 4.12/1.70  Ordering : KBO
% 4.12/1.70  
% 4.12/1.70  Simplification rules
% 4.12/1.70  ----------------------
% 4.12/1.70  #Subsume      : 132
% 4.12/1.70  #Demod        : 211
% 4.12/1.70  #Tautology    : 58
% 4.12/1.70  #SimpNegUnit  : 9
% 4.12/1.70  #BackRed      : 33
% 4.12/1.70  
% 4.12/1.70  #Partial instantiations: 0
% 4.12/1.70  #Strategies tried      : 1
% 4.12/1.70  
% 4.12/1.70  Timing (in seconds)
% 4.12/1.70  ----------------------
% 4.12/1.71  Preprocessing        : 0.31
% 4.12/1.71  Parsing              : 0.16
% 4.12/1.71  CNF conversion       : 0.03
% 4.12/1.71  Main loop            : 0.63
% 4.12/1.71  Inferencing          : 0.22
% 4.12/1.71  Reduction            : 0.16
% 4.12/1.71  Demodulation         : 0.11
% 4.12/1.71  BG Simplification    : 0.03
% 4.12/1.71  Subsumption          : 0.16
% 4.12/1.71  Abstraction          : 0.03
% 4.12/1.71  MUC search           : 0.00
% 4.12/1.71  Cooper               : 0.00
% 4.12/1.71  Total                : 0.97
% 4.12/1.71  Index Insertion      : 0.00
% 4.12/1.71  Index Deletion       : 0.00
% 4.12/1.71  Index Matching       : 0.00
% 4.12/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
