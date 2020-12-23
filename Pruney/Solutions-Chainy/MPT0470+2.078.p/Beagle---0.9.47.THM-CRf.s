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
% DateTime   : Thu Dec  3 09:59:11 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 112 expanded)
%              Number of leaves         :   30 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :  129 ( 192 expanded)
%              Number of equality atoms :   32 (  48 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_58,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_52,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_101,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_98,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_32,plain,
    ( k5_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_56,plain,(
    k5_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_50,plain,(
    ! [A_25] :
      ( v1_relat_1(A_25)
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_54,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_50])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( v1_relat_1(k5_relat_1(A_13,B_14))
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_14,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_2'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_70,plain,(
    ! [A_31,B_32,C_33] :
      ( ~ r1_xboole_0(A_31,B_32)
      | ~ r2_hidden(C_33,k3_xboole_0(A_31,B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_77,plain,(
    ! [A_36,B_37] :
      ( ~ r1_xboole_0(A_36,B_37)
      | k3_xboole_0(A_36,B_37) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_70])).

tff(c_81,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_77])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_111,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_42,B_43)),k1_relat_1(A_42))
      | ~ v1_relat_1(B_43)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_117,plain,(
    ! [B_43] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_43)),k1_xboole_0)
      | ~ v1_relat_1(B_43)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_111])).

tff(c_121,plain,(
    ! [B_44] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_44)),k1_xboole_0)
      | ~ v1_relat_1(B_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_117])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_124,plain,(
    ! [B_44] :
      ( k3_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,B_44)),k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,B_44))
      | ~ v1_relat_1(B_44) ) ),
    inference(resolution,[status(thm)],[c_121,c_12])).

tff(c_127,plain,(
    ! [B_45] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_45)) = k1_xboole_0
      | ~ v1_relat_1(B_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_124])).

tff(c_20,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0(k1_relat_1(A_15))
      | ~ v1_relat_1(A_15)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_142,plain,(
    ! [B_45] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_45))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_45))
      | ~ v1_relat_1(B_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_20])).

tff(c_236,plain,(
    ! [B_52] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_52))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_52))
      | ~ v1_relat_1(B_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_142])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_254,plain,(
    ! [B_54] :
      ( k5_relat_1(k1_xboole_0,B_54) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_54))
      | ~ v1_relat_1(B_54) ) ),
    inference(resolution,[status(thm)],[c_236,c_4])).

tff(c_258,plain,(
    ! [B_14] :
      ( k5_relat_1(k1_xboole_0,B_14) = k1_xboole_0
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_254])).

tff(c_262,plain,(
    ! [B_55] :
      ( k5_relat_1(k1_xboole_0,B_55) = k1_xboole_0
      | ~ v1_relat_1(B_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_258])).

tff(c_271,plain,(
    k5_relat_1(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_262])).

tff(c_277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_271])).

tff(c_278,plain,(
    k5_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_303,plain,(
    ! [A_62,B_63,C_64] :
      ( ~ r1_xboole_0(A_62,B_63)
      | ~ r2_hidden(C_64,k3_xboole_0(A_62,B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_309,plain,(
    ! [A_65,B_66] :
      ( ~ r1_xboole_0(A_65,B_66)
      | k3_xboole_0(A_65,B_66) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_303])).

tff(c_313,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_309])).

tff(c_28,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_343,plain,(
    ! [A_71,B_72] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_71,B_72)),k2_relat_1(B_72))
      | ~ v1_relat_1(B_72)
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_352,plain,(
    ! [A_71] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_71,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_343])).

tff(c_378,plain,(
    ! [A_73] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_73,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_352])).

tff(c_381,plain,(
    ! [A_73] :
      ( k3_xboole_0(k2_relat_1(k5_relat_1(A_73,k1_xboole_0)),k1_xboole_0) = k2_relat_1(k5_relat_1(A_73,k1_xboole_0))
      | ~ v1_relat_1(A_73) ) ),
    inference(resolution,[status(thm)],[c_378,c_12])).

tff(c_384,plain,(
    ! [A_74] :
      ( k2_relat_1(k5_relat_1(A_74,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_381])).

tff(c_22,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0(k2_relat_1(A_16))
      | ~ v1_relat_1(A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_399,plain,(
    ! [A_74] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_74,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_74,k1_xboole_0))
      | ~ v1_relat_1(A_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_22])).

tff(c_513,plain,(
    ! [A_81] :
      ( ~ v1_relat_1(k5_relat_1(A_81,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_81,k1_xboole_0))
      | ~ v1_relat_1(A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_399])).

tff(c_536,plain,(
    ! [A_83] :
      ( k5_relat_1(A_83,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_83,k1_xboole_0))
      | ~ v1_relat_1(A_83) ) ),
    inference(resolution,[status(thm)],[c_513,c_4])).

tff(c_540,plain,(
    ! [A_13] :
      ( k5_relat_1(A_13,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_13) ) ),
    inference(resolution,[status(thm)],[c_18,c_536])).

tff(c_544,plain,(
    ! [A_84] :
      ( k5_relat_1(A_84,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_540])).

tff(c_553,plain,(
    k5_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_544])).

tff(c_559,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_278,c_553])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:31:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.35  
% 2.51/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.36  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.51/1.36  
% 2.51/1.36  %Foreground sorts:
% 2.51/1.36  
% 2.51/1.36  
% 2.51/1.36  %Background operators:
% 2.51/1.36  
% 2.51/1.36  
% 2.51/1.36  %Foreground operators:
% 2.51/1.36  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.51/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.51/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.51/1.36  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.51/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.51/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.51/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.51/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.51/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.51/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.51/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.51/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.51/1.36  
% 2.51/1.37  tff(f_108, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 2.51/1.37  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.51/1.37  tff(f_62, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.51/1.37  tff(f_68, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.51/1.37  tff(f_58, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.51/1.37  tff(f_52, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.51/1.37  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.51/1.37  tff(f_101, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.51/1.37  tff(f_91, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 2.51/1.37  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.51/1.37  tff(f_76, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.51/1.37  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.51/1.37  tff(f_98, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 2.51/1.37  tff(f_84, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.51/1.37  tff(c_32, plain, (k5_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.51/1.37  tff(c_56, plain, (k5_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32])).
% 2.51/1.37  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.51/1.37  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.51/1.37  tff(c_50, plain, (![A_25]: (v1_relat_1(A_25) | ~v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.51/1.37  tff(c_54, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_50])).
% 2.51/1.37  tff(c_18, plain, (![A_13, B_14]: (v1_relat_1(k5_relat_1(A_13, B_14)) | ~v1_relat_1(B_14) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.51/1.37  tff(c_14, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.51/1.37  tff(c_10, plain, (![A_7]: (r2_hidden('#skF_2'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.51/1.37  tff(c_70, plain, (![A_31, B_32, C_33]: (~r1_xboole_0(A_31, B_32) | ~r2_hidden(C_33, k3_xboole_0(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.51/1.37  tff(c_77, plain, (![A_36, B_37]: (~r1_xboole_0(A_36, B_37) | k3_xboole_0(A_36, B_37)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_70])).
% 2.51/1.37  tff(c_81, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_77])).
% 2.51/1.37  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.51/1.37  tff(c_111, plain, (![A_42, B_43]: (r1_tarski(k1_relat_1(k5_relat_1(A_42, B_43)), k1_relat_1(A_42)) | ~v1_relat_1(B_43) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.51/1.37  tff(c_117, plain, (![B_43]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_43)), k1_xboole_0) | ~v1_relat_1(B_43) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_111])).
% 2.51/1.37  tff(c_121, plain, (![B_44]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_44)), k1_xboole_0) | ~v1_relat_1(B_44))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_117])).
% 2.51/1.37  tff(c_12, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.51/1.37  tff(c_124, plain, (![B_44]: (k3_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0, B_44)), k1_xboole_0)=k1_relat_1(k5_relat_1(k1_xboole_0, B_44)) | ~v1_relat_1(B_44))), inference(resolution, [status(thm)], [c_121, c_12])).
% 2.51/1.37  tff(c_127, plain, (![B_45]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_45))=k1_xboole_0 | ~v1_relat_1(B_45))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_124])).
% 2.51/1.37  tff(c_20, plain, (![A_15]: (~v1_xboole_0(k1_relat_1(A_15)) | ~v1_relat_1(A_15) | v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.51/1.37  tff(c_142, plain, (![B_45]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_45)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_45)) | ~v1_relat_1(B_45))), inference(superposition, [status(thm), theory('equality')], [c_127, c_20])).
% 2.51/1.37  tff(c_236, plain, (![B_52]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_52)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_52)) | ~v1_relat_1(B_52))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_142])).
% 2.51/1.37  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.51/1.37  tff(c_254, plain, (![B_54]: (k5_relat_1(k1_xboole_0, B_54)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_54)) | ~v1_relat_1(B_54))), inference(resolution, [status(thm)], [c_236, c_4])).
% 2.51/1.37  tff(c_258, plain, (![B_14]: (k5_relat_1(k1_xboole_0, B_14)=k1_xboole_0 | ~v1_relat_1(B_14) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_254])).
% 2.51/1.37  tff(c_262, plain, (![B_55]: (k5_relat_1(k1_xboole_0, B_55)=k1_xboole_0 | ~v1_relat_1(B_55))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_258])).
% 2.51/1.37  tff(c_271, plain, (k5_relat_1(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_262])).
% 2.51/1.37  tff(c_277, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_271])).
% 2.51/1.37  tff(c_278, plain, (k5_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 2.51/1.37  tff(c_303, plain, (![A_62, B_63, C_64]: (~r1_xboole_0(A_62, B_63) | ~r2_hidden(C_64, k3_xboole_0(A_62, B_63)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.51/1.37  tff(c_309, plain, (![A_65, B_66]: (~r1_xboole_0(A_65, B_66) | k3_xboole_0(A_65, B_66)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_303])).
% 2.51/1.37  tff(c_313, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_309])).
% 2.51/1.37  tff(c_28, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.51/1.37  tff(c_343, plain, (![A_71, B_72]: (r1_tarski(k2_relat_1(k5_relat_1(A_71, B_72)), k2_relat_1(B_72)) | ~v1_relat_1(B_72) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.51/1.37  tff(c_352, plain, (![A_71]: (r1_tarski(k2_relat_1(k5_relat_1(A_71, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_71))), inference(superposition, [status(thm), theory('equality')], [c_28, c_343])).
% 2.51/1.37  tff(c_378, plain, (![A_73]: (r1_tarski(k2_relat_1(k5_relat_1(A_73, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_73))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_352])).
% 2.51/1.37  tff(c_381, plain, (![A_73]: (k3_xboole_0(k2_relat_1(k5_relat_1(A_73, k1_xboole_0)), k1_xboole_0)=k2_relat_1(k5_relat_1(A_73, k1_xboole_0)) | ~v1_relat_1(A_73))), inference(resolution, [status(thm)], [c_378, c_12])).
% 2.51/1.37  tff(c_384, plain, (![A_74]: (k2_relat_1(k5_relat_1(A_74, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_74))), inference(demodulation, [status(thm), theory('equality')], [c_313, c_381])).
% 2.51/1.37  tff(c_22, plain, (![A_16]: (~v1_xboole_0(k2_relat_1(A_16)) | ~v1_relat_1(A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.51/1.37  tff(c_399, plain, (![A_74]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_74, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_74, k1_xboole_0)) | ~v1_relat_1(A_74))), inference(superposition, [status(thm), theory('equality')], [c_384, c_22])).
% 2.51/1.37  tff(c_513, plain, (![A_81]: (~v1_relat_1(k5_relat_1(A_81, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_81, k1_xboole_0)) | ~v1_relat_1(A_81))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_399])).
% 2.51/1.37  tff(c_536, plain, (![A_83]: (k5_relat_1(A_83, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_83, k1_xboole_0)) | ~v1_relat_1(A_83))), inference(resolution, [status(thm)], [c_513, c_4])).
% 2.51/1.37  tff(c_540, plain, (![A_13]: (k5_relat_1(A_13, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_13))), inference(resolution, [status(thm)], [c_18, c_536])).
% 2.51/1.37  tff(c_544, plain, (![A_84]: (k5_relat_1(A_84, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_84))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_540])).
% 2.51/1.37  tff(c_553, plain, (k5_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_544])).
% 2.51/1.37  tff(c_559, plain, $false, inference(negUnitSimplification, [status(thm)], [c_278, c_553])).
% 2.51/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.37  
% 2.51/1.37  Inference rules
% 2.51/1.37  ----------------------
% 2.51/1.37  #Ref     : 0
% 2.51/1.37  #Sup     : 109
% 2.51/1.37  #Fact    : 0
% 2.51/1.37  #Define  : 0
% 2.51/1.37  #Split   : 3
% 2.51/1.37  #Chain   : 0
% 2.51/1.37  #Close   : 0
% 2.51/1.37  
% 2.51/1.37  Ordering : KBO
% 2.51/1.37  
% 2.51/1.37  Simplification rules
% 2.51/1.37  ----------------------
% 2.51/1.37  #Subsume      : 19
% 2.51/1.37  #Demod        : 86
% 2.51/1.37  #Tautology    : 54
% 2.51/1.37  #SimpNegUnit  : 13
% 2.51/1.37  #BackRed      : 6
% 2.51/1.37  
% 2.51/1.37  #Partial instantiations: 0
% 2.51/1.37  #Strategies tried      : 1
% 2.51/1.37  
% 2.51/1.37  Timing (in seconds)
% 2.51/1.37  ----------------------
% 2.51/1.37  Preprocessing        : 0.29
% 2.51/1.37  Parsing              : 0.17
% 2.51/1.37  CNF conversion       : 0.02
% 2.51/1.37  Main loop            : 0.28
% 2.51/1.37  Inferencing          : 0.12
% 2.51/1.37  Reduction            : 0.07
% 2.51/1.38  Demodulation         : 0.05
% 2.51/1.38  BG Simplification    : 0.01
% 2.51/1.38  Subsumption          : 0.05
% 2.51/1.38  Abstraction          : 0.01
% 2.51/1.38  MUC search           : 0.00
% 2.51/1.38  Cooper               : 0.00
% 2.51/1.38  Total                : 0.60
% 2.51/1.38  Index Insertion      : 0.00
% 2.51/1.38  Index Deletion       : 0.00
% 2.51/1.38  Index Matching       : 0.00
% 2.51/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
