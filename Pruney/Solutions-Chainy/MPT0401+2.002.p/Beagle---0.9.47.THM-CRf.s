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
% DateTime   : Thu Dec  3 09:57:38 EST 2020

% Result     : Theorem 9.08s
% Output     : CNFRefutation 9.08s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 185 expanded)
%              Number of leaves         :   27 (  72 expanded)
%              Depth                    :   16
%              Number of atoms          :  112 ( 314 expanded)
%              Number of equality atoms :   21 (  72 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k3_xboole_0 > k2_xboole_0 > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_setfam_1(B,k1_tarski(A))
       => ! [C] :
            ( r2_hidden(C,B)
           => r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_setfam_1)).

tff(c_38,plain,(
    ~ r1_tarski('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_40,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_193,plain,(
    ! [A_61,B_62] :
      ( r2_hidden('#skF_2'(A_61,B_62),A_61)
      | r1_tarski(k3_tarski(A_61),B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_82,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(k1_tarski(A_42),B_43)
      | ~ r2_hidden(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_30,plain,(
    ! [B_25,A_24] :
      ( B_25 = A_24
      | ~ r1_tarski(k1_tarski(A_24),k1_tarski(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_94,plain,(
    ! [B_25,A_42] :
      ( B_25 = A_42
      | ~ r2_hidden(A_42,k1_tarski(B_25)) ) ),
    inference(resolution,[status(thm)],[c_82,c_30])).

tff(c_13886,plain,(
    ! [B_387,B_388] :
      ( '#skF_2'(k1_tarski(B_387),B_388) = B_387
      | r1_tarski(k3_tarski(k1_tarski(B_387)),B_388) ) ),
    inference(resolution,[status(thm)],[c_193,c_94])).

tff(c_45,plain,(
    ! [A_33,B_34] :
      ( k2_xboole_0(A_33,B_34) = B_34
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_49,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_45])).

tff(c_255,plain,(
    ! [A_72,B_73,C_74] : r1_tarski(k2_xboole_0(k3_xboole_0(A_72,B_73),k3_xboole_0(A_72,C_74)),k2_xboole_0(B_73,C_74)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_284,plain,(
    ! [A_72,B_73] : r1_tarski(k3_xboole_0(A_72,B_73),k2_xboole_0(B_73,B_73)) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_255])).

tff(c_292,plain,(
    ! [A_72,B_73] : r1_tarski(k3_xboole_0(A_72,B_73),B_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_284])).

tff(c_294,plain,(
    ! [A_75,B_76] : r1_tarski(k3_xboole_0(A_75,B_76),B_76) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_284])).

tff(c_12,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(A_8,C_10)
      | ~ r1_tarski(B_9,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_399,plain,(
    ! [A_84,B_85,A_86] :
      ( r1_tarski(A_84,B_85)
      | ~ r1_tarski(A_84,k3_xboole_0(A_86,B_85)) ) ),
    inference(resolution,[status(thm)],[c_294,c_12])).

tff(c_430,plain,(
    ! [A_87,A_88,B_89] : r1_tarski(k3_xboole_0(A_87,k3_xboole_0(A_88,B_89)),B_89) ),
    inference(resolution,[status(thm)],[c_292,c_399])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_466,plain,(
    ! [A_87,A_88,B_89] : k2_xboole_0(k3_xboole_0(A_87,k3_xboole_0(A_88,B_89)),B_89) = B_89 ),
    inference(resolution,[status(thm)],[c_430,c_10])).

tff(c_71,plain,(
    ! [A_40,B_41] :
      ( r2_hidden(A_40,B_41)
      | ~ r1_tarski(k1_tarski(A_40),B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_81,plain,(
    ! [A_40] : r2_hidden(A_40,k1_tarski(A_40)) ),
    inference(resolution,[status(thm)],[c_6,c_71])).

tff(c_125,plain,(
    ! [A_50,C_51,B_52] :
      ( r1_tarski(k3_xboole_0(A_50,C_51),B_52)
      | ~ r1_tarski(A_50,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_136,plain,(
    ! [A_50,C_51,B_52] :
      ( k2_xboole_0(k3_xboole_0(A_50,C_51),B_52) = B_52
      | ~ r1_tarski(A_50,B_52) ) ),
    inference(resolution,[status(thm)],[c_125,c_10])).

tff(c_103,plain,(
    ! [A_47,B_48] :
      ( k3_xboole_0(A_47,B_48) = A_47
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_115,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_103])).

tff(c_723,plain,(
    ! [B_103,B_104] : r1_tarski(k2_xboole_0(k3_xboole_0(B_103,B_104),B_103),k2_xboole_0(B_104,B_103)) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_255])).

tff(c_737,plain,(
    ! [B_52,C_51] :
      ( r1_tarski(B_52,k2_xboole_0(C_51,B_52))
      | ~ r1_tarski(B_52,B_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_723])).

tff(c_785,plain,(
    ! [B_52,C_51] : r1_tarski(B_52,k2_xboole_0(C_51,B_52)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_737])).

tff(c_28,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,k3_tarski(B_23))
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_234,plain,(
    ! [A_67,C_68,B_69] :
      ( r1_tarski(A_67,C_68)
      | ~ r1_tarski(B_69,C_68)
      | ~ r1_tarski(A_67,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1804,plain,(
    ! [A_143,B_144,A_145] :
      ( r1_tarski(A_143,k3_tarski(B_144))
      | ~ r1_tarski(A_143,A_145)
      | ~ r2_hidden(A_145,B_144) ) ),
    inference(resolution,[status(thm)],[c_28,c_234])).

tff(c_3039,plain,(
    ! [B_182,B_183,C_184] :
      ( r1_tarski(B_182,k3_tarski(B_183))
      | ~ r2_hidden(k2_xboole_0(C_184,B_182),B_183) ) ),
    inference(resolution,[status(thm)],[c_785,c_1804])).

tff(c_3097,plain,(
    ! [B_185,C_186] : r1_tarski(B_185,k3_tarski(k1_tarski(k2_xboole_0(C_186,B_185)))) ),
    inference(resolution,[status(thm)],[c_81,c_3039])).

tff(c_3287,plain,(
    ! [B_189] : r1_tarski(B_189,k3_tarski(k1_tarski(B_189))) ),
    inference(superposition,[status(thm),theory(equality)],[c_466,c_3097])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3321,plain,(
    ! [B_189] :
      ( k3_tarski(k1_tarski(B_189)) = B_189
      | ~ r1_tarski(k3_tarski(k1_tarski(B_189)),B_189) ) ),
    inference(resolution,[status(thm)],[c_3287,c_2])).

tff(c_14000,plain,(
    ! [B_391] :
      ( k3_tarski(k1_tarski(B_391)) = B_391
      | '#skF_2'(k1_tarski(B_391),B_391) = B_391 ) ),
    inference(resolution,[status(thm)],[c_13886,c_3321])).

tff(c_32,plain,(
    ! [A_26,B_27] :
      ( ~ r1_tarski('#skF_2'(A_26,B_27),B_27)
      | r1_tarski(k3_tarski(A_26),B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_14200,plain,(
    ! [B_391] :
      ( ~ r1_tarski(B_391,B_391)
      | r1_tarski(k3_tarski(k1_tarski(B_391)),B_391)
      | k3_tarski(k1_tarski(B_391)) = B_391 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14000,c_32])).

tff(c_14332,plain,(
    ! [B_396] :
      ( r1_tarski(k3_tarski(k1_tarski(B_396)),B_396)
      | k3_tarski(k1_tarski(B_396)) = B_396 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14200])).

tff(c_14410,plain,(
    ! [B_396] : k3_tarski(k1_tarski(B_396)) = B_396 ),
    inference(resolution,[status(thm)],[c_14332,c_3321])).

tff(c_42,plain,(
    r1_setfam_1('#skF_4',k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_36,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(k3_tarski(A_29),k3_tarski(B_30))
      | ~ r1_setfam_1(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_5938,plain,(
    ! [A_242,B_243,A_244] :
      ( r1_tarski(A_242,k3_tarski(B_243))
      | ~ r1_tarski(A_242,k3_tarski(A_244))
      | ~ r1_setfam_1(A_244,B_243) ) ),
    inference(resolution,[status(thm)],[c_36,c_234])).

tff(c_15775,plain,(
    ! [A_432,B_433,B_434] :
      ( r1_tarski(A_432,k3_tarski(B_433))
      | ~ r1_setfam_1(B_434,B_433)
      | ~ r2_hidden(A_432,B_434) ) ),
    inference(resolution,[status(thm)],[c_28,c_5938])).

tff(c_15777,plain,(
    ! [A_432] :
      ( r1_tarski(A_432,k3_tarski(k1_tarski('#skF_3')))
      | ~ r2_hidden(A_432,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_15775])).

tff(c_15780,plain,(
    ! [A_435] :
      ( r1_tarski(A_435,'#skF_3')
      | ~ r2_hidden(A_435,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14410,c_15777])).

tff(c_15787,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_15780])).

tff(c_15792,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_15787])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 09:38:45 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.08/3.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.08/3.29  
% 9.08/3.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.08/3.29  %$ r2_hidden > r1_tarski > r1_setfam_1 > k3_xboole_0 > k2_xboole_0 > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 9.08/3.29  
% 9.08/3.29  %Foreground sorts:
% 9.08/3.29  
% 9.08/3.29  
% 9.08/3.29  %Background operators:
% 9.08/3.29  
% 9.08/3.29  
% 9.08/3.29  %Foreground operators:
% 9.08/3.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.08/3.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.08/3.29  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 9.08/3.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.08/3.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.08/3.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.08/3.29  tff('#skF_5', type, '#skF_5': $i).
% 9.08/3.29  tff('#skF_3', type, '#skF_3': $i).
% 9.08/3.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.08/3.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.08/3.29  tff('#skF_4', type, '#skF_4': $i).
% 9.08/3.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.08/3.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.08/3.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.08/3.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.08/3.29  
% 9.08/3.30  tff(f_95, negated_conjecture, ~(![A, B]: (r1_setfam_1(B, k1_tarski(A)) => (![C]: (r2_hidden(C, B) => r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_setfam_1)).
% 9.08/3.30  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.08/3.30  tff(f_83, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 9.08/3.30  tff(f_68, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 9.08/3.30  tff(f_76, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_zfmisc_1)).
% 9.08/3.30  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 9.08/3.30  tff(f_64, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 9.08/3.30  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 9.08/3.30  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 9.08/3.30  tff(f_62, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.08/3.30  tff(f_72, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 9.08/3.30  tff(f_87, axiom, (![A, B]: (r1_setfam_1(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_setfam_1)).
% 9.08/3.30  tff(c_38, plain, (~r1_tarski('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.08/3.30  tff(c_40, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.08/3.30  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.08/3.30  tff(c_193, plain, (![A_61, B_62]: (r2_hidden('#skF_2'(A_61, B_62), A_61) | r1_tarski(k3_tarski(A_61), B_62))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.08/3.30  tff(c_82, plain, (![A_42, B_43]: (r1_tarski(k1_tarski(A_42), B_43) | ~r2_hidden(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.08/3.30  tff(c_30, plain, (![B_25, A_24]: (B_25=A_24 | ~r1_tarski(k1_tarski(A_24), k1_tarski(B_25)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.08/3.30  tff(c_94, plain, (![B_25, A_42]: (B_25=A_42 | ~r2_hidden(A_42, k1_tarski(B_25)))), inference(resolution, [status(thm)], [c_82, c_30])).
% 9.08/3.30  tff(c_13886, plain, (![B_387, B_388]: ('#skF_2'(k1_tarski(B_387), B_388)=B_387 | r1_tarski(k3_tarski(k1_tarski(B_387)), B_388))), inference(resolution, [status(thm)], [c_193, c_94])).
% 9.08/3.30  tff(c_45, plain, (![A_33, B_34]: (k2_xboole_0(A_33, B_34)=B_34 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.08/3.30  tff(c_49, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_45])).
% 9.08/3.30  tff(c_255, plain, (![A_72, B_73, C_74]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_72, B_73), k3_xboole_0(A_72, C_74)), k2_xboole_0(B_73, C_74)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.08/3.30  tff(c_284, plain, (![A_72, B_73]: (r1_tarski(k3_xboole_0(A_72, B_73), k2_xboole_0(B_73, B_73)))), inference(superposition, [status(thm), theory('equality')], [c_49, c_255])).
% 9.08/3.30  tff(c_292, plain, (![A_72, B_73]: (r1_tarski(k3_xboole_0(A_72, B_73), B_73))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_284])).
% 9.08/3.30  tff(c_294, plain, (![A_75, B_76]: (r1_tarski(k3_xboole_0(A_75, B_76), B_76))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_284])).
% 9.08/3.30  tff(c_12, plain, (![A_8, C_10, B_9]: (r1_tarski(A_8, C_10) | ~r1_tarski(B_9, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.08/3.30  tff(c_399, plain, (![A_84, B_85, A_86]: (r1_tarski(A_84, B_85) | ~r1_tarski(A_84, k3_xboole_0(A_86, B_85)))), inference(resolution, [status(thm)], [c_294, c_12])).
% 9.08/3.30  tff(c_430, plain, (![A_87, A_88, B_89]: (r1_tarski(k3_xboole_0(A_87, k3_xboole_0(A_88, B_89)), B_89))), inference(resolution, [status(thm)], [c_292, c_399])).
% 9.08/3.30  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.08/3.30  tff(c_466, plain, (![A_87, A_88, B_89]: (k2_xboole_0(k3_xboole_0(A_87, k3_xboole_0(A_88, B_89)), B_89)=B_89)), inference(resolution, [status(thm)], [c_430, c_10])).
% 9.08/3.30  tff(c_71, plain, (![A_40, B_41]: (r2_hidden(A_40, B_41) | ~r1_tarski(k1_tarski(A_40), B_41))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.08/3.30  tff(c_81, plain, (![A_40]: (r2_hidden(A_40, k1_tarski(A_40)))), inference(resolution, [status(thm)], [c_6, c_71])).
% 9.08/3.30  tff(c_125, plain, (![A_50, C_51, B_52]: (r1_tarski(k3_xboole_0(A_50, C_51), B_52) | ~r1_tarski(A_50, B_52))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.08/3.30  tff(c_136, plain, (![A_50, C_51, B_52]: (k2_xboole_0(k3_xboole_0(A_50, C_51), B_52)=B_52 | ~r1_tarski(A_50, B_52))), inference(resolution, [status(thm)], [c_125, c_10])).
% 9.08/3.30  tff(c_103, plain, (![A_47, B_48]: (k3_xboole_0(A_47, B_48)=A_47 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.08/3.30  tff(c_115, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_103])).
% 9.08/3.30  tff(c_723, plain, (![B_103, B_104]: (r1_tarski(k2_xboole_0(k3_xboole_0(B_103, B_104), B_103), k2_xboole_0(B_104, B_103)))), inference(superposition, [status(thm), theory('equality')], [c_115, c_255])).
% 9.08/3.30  tff(c_737, plain, (![B_52, C_51]: (r1_tarski(B_52, k2_xboole_0(C_51, B_52)) | ~r1_tarski(B_52, B_52))), inference(superposition, [status(thm), theory('equality')], [c_136, c_723])).
% 9.08/3.30  tff(c_785, plain, (![B_52, C_51]: (r1_tarski(B_52, k2_xboole_0(C_51, B_52)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_737])).
% 9.08/3.30  tff(c_28, plain, (![A_22, B_23]: (r1_tarski(A_22, k3_tarski(B_23)) | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.08/3.30  tff(c_234, plain, (![A_67, C_68, B_69]: (r1_tarski(A_67, C_68) | ~r1_tarski(B_69, C_68) | ~r1_tarski(A_67, B_69))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.08/3.30  tff(c_1804, plain, (![A_143, B_144, A_145]: (r1_tarski(A_143, k3_tarski(B_144)) | ~r1_tarski(A_143, A_145) | ~r2_hidden(A_145, B_144))), inference(resolution, [status(thm)], [c_28, c_234])).
% 9.08/3.30  tff(c_3039, plain, (![B_182, B_183, C_184]: (r1_tarski(B_182, k3_tarski(B_183)) | ~r2_hidden(k2_xboole_0(C_184, B_182), B_183))), inference(resolution, [status(thm)], [c_785, c_1804])).
% 9.08/3.30  tff(c_3097, plain, (![B_185, C_186]: (r1_tarski(B_185, k3_tarski(k1_tarski(k2_xboole_0(C_186, B_185)))))), inference(resolution, [status(thm)], [c_81, c_3039])).
% 9.08/3.30  tff(c_3287, plain, (![B_189]: (r1_tarski(B_189, k3_tarski(k1_tarski(B_189))))), inference(superposition, [status(thm), theory('equality')], [c_466, c_3097])).
% 9.08/3.30  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.08/3.30  tff(c_3321, plain, (![B_189]: (k3_tarski(k1_tarski(B_189))=B_189 | ~r1_tarski(k3_tarski(k1_tarski(B_189)), B_189))), inference(resolution, [status(thm)], [c_3287, c_2])).
% 9.08/3.30  tff(c_14000, plain, (![B_391]: (k3_tarski(k1_tarski(B_391))=B_391 | '#skF_2'(k1_tarski(B_391), B_391)=B_391)), inference(resolution, [status(thm)], [c_13886, c_3321])).
% 9.08/3.30  tff(c_32, plain, (![A_26, B_27]: (~r1_tarski('#skF_2'(A_26, B_27), B_27) | r1_tarski(k3_tarski(A_26), B_27))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.08/3.30  tff(c_14200, plain, (![B_391]: (~r1_tarski(B_391, B_391) | r1_tarski(k3_tarski(k1_tarski(B_391)), B_391) | k3_tarski(k1_tarski(B_391))=B_391)), inference(superposition, [status(thm), theory('equality')], [c_14000, c_32])).
% 9.08/3.30  tff(c_14332, plain, (![B_396]: (r1_tarski(k3_tarski(k1_tarski(B_396)), B_396) | k3_tarski(k1_tarski(B_396))=B_396)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14200])).
% 9.08/3.30  tff(c_14410, plain, (![B_396]: (k3_tarski(k1_tarski(B_396))=B_396)), inference(resolution, [status(thm)], [c_14332, c_3321])).
% 9.08/3.30  tff(c_42, plain, (r1_setfam_1('#skF_4', k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.08/3.30  tff(c_36, plain, (![A_29, B_30]: (r1_tarski(k3_tarski(A_29), k3_tarski(B_30)) | ~r1_setfam_1(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.08/3.30  tff(c_5938, plain, (![A_242, B_243, A_244]: (r1_tarski(A_242, k3_tarski(B_243)) | ~r1_tarski(A_242, k3_tarski(A_244)) | ~r1_setfam_1(A_244, B_243))), inference(resolution, [status(thm)], [c_36, c_234])).
% 9.08/3.30  tff(c_15775, plain, (![A_432, B_433, B_434]: (r1_tarski(A_432, k3_tarski(B_433)) | ~r1_setfam_1(B_434, B_433) | ~r2_hidden(A_432, B_434))), inference(resolution, [status(thm)], [c_28, c_5938])).
% 9.08/3.30  tff(c_15777, plain, (![A_432]: (r1_tarski(A_432, k3_tarski(k1_tarski('#skF_3'))) | ~r2_hidden(A_432, '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_15775])).
% 9.08/3.30  tff(c_15780, plain, (![A_435]: (r1_tarski(A_435, '#skF_3') | ~r2_hidden(A_435, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14410, c_15777])).
% 9.08/3.30  tff(c_15787, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_15780])).
% 9.08/3.30  tff(c_15792, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_15787])).
% 9.08/3.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.08/3.30  
% 9.08/3.30  Inference rules
% 9.08/3.30  ----------------------
% 9.08/3.30  #Ref     : 0
% 9.08/3.30  #Sup     : 3845
% 9.08/3.30  #Fact    : 0
% 9.08/3.30  #Define  : 0
% 9.08/3.30  #Split   : 1
% 9.08/3.30  #Chain   : 0
% 9.08/3.30  #Close   : 0
% 9.08/3.30  
% 9.08/3.30  Ordering : KBO
% 9.08/3.30  
% 9.08/3.30  Simplification rules
% 9.08/3.30  ----------------------
% 9.08/3.30  #Subsume      : 365
% 9.08/3.30  #Demod        : 1719
% 9.08/3.30  #Tautology    : 1659
% 9.08/3.30  #SimpNegUnit  : 1
% 9.08/3.30  #BackRed      : 50
% 9.08/3.30  
% 9.08/3.30  #Partial instantiations: 0
% 9.08/3.30  #Strategies tried      : 1
% 9.08/3.30  
% 9.08/3.30  Timing (in seconds)
% 9.08/3.30  ----------------------
% 9.08/3.31  Preprocessing        : 0.31
% 9.08/3.31  Parsing              : 0.18
% 9.08/3.31  CNF conversion       : 0.02
% 9.08/3.31  Main loop            : 2.17
% 9.08/3.31  Inferencing          : 0.58
% 9.08/3.31  Reduction            : 0.81
% 9.08/3.31  Demodulation         : 0.65
% 9.08/3.31  BG Simplification    : 0.08
% 9.08/3.31  Subsumption          : 0.53
% 9.08/3.31  Abstraction          : 0.11
% 9.08/3.31  MUC search           : 0.00
% 9.08/3.31  Cooper               : 0.00
% 9.08/3.31  Total                : 2.51
% 9.08/3.31  Index Insertion      : 0.00
% 9.08/3.31  Index Deletion       : 0.00
% 9.08/3.31  Index Matching       : 0.00
% 9.08/3.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
