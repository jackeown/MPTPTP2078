%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:08 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 118 expanded)
%              Number of leaves         :   30 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  137 ( 208 expanded)
%              Number of equality atoms :   32 (  48 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_54,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_105,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_102,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_40,plain,
    ( k5_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_68,plain,(
    k5_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_42,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_57,plain,(
    ! [A_27] :
      ( v1_relat_1(A_27)
      | ~ v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_61,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_57])).

tff(c_26,plain,(
    ! [A_16,B_17] :
      ( v1_relat_1(k5_relat_1(A_16,B_17))
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_99,plain,(
    ! [A_45,B_46] :
      ( r2_hidden('#skF_2'(A_45,B_46),B_46)
      | r1_xboole_0(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_109,plain,(
    ! [B_49,A_50] :
      ( ~ v1_xboole_0(B_49)
      | r1_xboole_0(A_50,B_49) ) ),
    inference(resolution,[status(thm)],[c_99,c_2])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = A_13
      | ~ r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_125,plain,(
    ! [A_54,B_55] :
      ( k4_xboole_0(A_54,B_55) = A_54
      | ~ v1_xboole_0(B_55) ) ),
    inference(resolution,[status(thm)],[c_109,c_20])).

tff(c_128,plain,(
    ! [A_54] : k4_xboole_0(A_54,k1_xboole_0) = A_54 ),
    inference(resolution,[status(thm)],[c_6,c_125])).

tff(c_38,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_173,plain,(
    ! [A_65,B_66] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_65,B_66)),k1_relat_1(A_65))
      | ~ v1_relat_1(B_66)
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_179,plain,(
    ! [B_66] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_66)),k1_xboole_0)
      | ~ v1_relat_1(B_66)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_173])).

tff(c_194,plain,(
    ! [B_68] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_68)),k1_xboole_0)
      | ~ v1_relat_1(B_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_179])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = k1_xboole_0
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_197,plain,(
    ! [B_68] :
      ( k4_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,B_68)),k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_68) ) ),
    inference(resolution,[status(thm)],[c_194,c_18])).

tff(c_200,plain,(
    ! [B_69] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_69)) = k1_xboole_0
      | ~ v1_relat_1(B_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_197])).

tff(c_28,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(k1_relat_1(A_18))
      | ~ v1_relat_1(A_18)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_215,plain,(
    ! [B_69] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_69))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_69))
      | ~ v1_relat_1(B_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_28])).

tff(c_303,plain,(
    ! [B_76] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_76))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_76))
      | ~ v1_relat_1(B_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_215])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_333,plain,(
    ! [B_78] :
      ( k5_relat_1(k1_xboole_0,B_78) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_78))
      | ~ v1_relat_1(B_78) ) ),
    inference(resolution,[status(thm)],[c_303,c_8])).

tff(c_337,plain,(
    ! [B_17] :
      ( k5_relat_1(k1_xboole_0,B_17) = k1_xboole_0
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_333])).

tff(c_341,plain,(
    ! [B_79] :
      ( k5_relat_1(k1_xboole_0,B_79) = k1_xboole_0
      | ~ v1_relat_1(B_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_337])).

tff(c_350,plain,(
    k5_relat_1(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_341])).

tff(c_356,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_350])).

tff(c_357,plain,(
    k5_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_387,plain,(
    ! [A_90,B_91] :
      ( r2_hidden('#skF_2'(A_90,B_91),B_91)
      | r1_xboole_0(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_392,plain,(
    ! [B_92,A_93] :
      ( ~ v1_xboole_0(B_92)
      | r1_xboole_0(A_93,B_92) ) ),
    inference(resolution,[status(thm)],[c_387,c_2])).

tff(c_407,plain,(
    ! [A_98,B_99] :
      ( k4_xboole_0(A_98,B_99) = A_98
      | ~ v1_xboole_0(B_99) ) ),
    inference(resolution,[status(thm)],[c_392,c_20])).

tff(c_410,plain,(
    ! [A_98] : k4_xboole_0(A_98,k1_xboole_0) = A_98 ),
    inference(resolution,[status(thm)],[c_6,c_407])).

tff(c_36,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_514,plain,(
    ! [A_118,B_119] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_118,B_119)),k2_relat_1(B_119))
      | ~ v1_relat_1(B_119)
      | ~ v1_relat_1(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_523,plain,(
    ! [A_118] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_118,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_514])).

tff(c_565,plain,(
    ! [A_121] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_121,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_523])).

tff(c_568,plain,(
    ! [A_121] :
      ( k4_xboole_0(k2_relat_1(k5_relat_1(A_121,k1_xboole_0)),k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_121) ) ),
    inference(resolution,[status(thm)],[c_565,c_18])).

tff(c_571,plain,(
    ! [A_122] :
      ( k2_relat_1(k5_relat_1(A_122,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_568])).

tff(c_30,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0(k2_relat_1(A_19))
      | ~ v1_relat_1(A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_586,plain,(
    ! [A_122] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_122,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_122,k1_xboole_0))
      | ~ v1_relat_1(A_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_571,c_30])).

tff(c_645,plain,(
    ! [A_126] :
      ( ~ v1_relat_1(k5_relat_1(A_126,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_126,k1_xboole_0))
      | ~ v1_relat_1(A_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_586])).

tff(c_687,plain,(
    ! [A_129] :
      ( k5_relat_1(A_129,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_129,k1_xboole_0))
      | ~ v1_relat_1(A_129) ) ),
    inference(resolution,[status(thm)],[c_645,c_8])).

tff(c_691,plain,(
    ! [A_16] :
      ( k5_relat_1(A_16,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_16) ) ),
    inference(resolution,[status(thm)],[c_26,c_687])).

tff(c_754,plain,(
    ! [A_130] :
      ( k5_relat_1(A_130,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_691])).

tff(c_763,plain,(
    k5_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_754])).

tff(c_770,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_357,c_763])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:30:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.38  
% 2.47/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.38  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.47/1.38  
% 2.47/1.38  %Foreground sorts:
% 2.47/1.38  
% 2.47/1.38  
% 2.47/1.38  %Background operators:
% 2.47/1.38  
% 2.47/1.38  
% 2.47/1.38  %Foreground operators:
% 2.47/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.47/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.47/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.38  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.47/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.47/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.47/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.47/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.47/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.47/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.47/1.38  
% 2.76/1.40  tff(f_112, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 2.76/1.40  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.76/1.40  tff(f_66, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.76/1.40  tff(f_72, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.76/1.40  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.76/1.40  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.76/1.40  tff(f_62, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.76/1.40  tff(f_105, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.76/1.40  tff(f_95, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 2.76/1.40  tff(f_58, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.76/1.40  tff(f_80, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.76/1.40  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.76/1.40  tff(f_102, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 2.76/1.40  tff(f_88, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.76/1.40  tff(c_40, plain, (k5_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.76/1.40  tff(c_68, plain, (k5_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_40])).
% 2.76/1.40  tff(c_42, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.76/1.40  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.76/1.40  tff(c_57, plain, (![A_27]: (v1_relat_1(A_27) | ~v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.76/1.40  tff(c_61, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_57])).
% 2.76/1.40  tff(c_26, plain, (![A_16, B_17]: (v1_relat_1(k5_relat_1(A_16, B_17)) | ~v1_relat_1(B_17) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.76/1.40  tff(c_99, plain, (![A_45, B_46]: (r2_hidden('#skF_2'(A_45, B_46), B_46) | r1_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.76/1.40  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.76/1.40  tff(c_109, plain, (![B_49, A_50]: (~v1_xboole_0(B_49) | r1_xboole_0(A_50, B_49))), inference(resolution, [status(thm)], [c_99, c_2])).
% 2.76/1.40  tff(c_20, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=A_13 | ~r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.76/1.40  tff(c_125, plain, (![A_54, B_55]: (k4_xboole_0(A_54, B_55)=A_54 | ~v1_xboole_0(B_55))), inference(resolution, [status(thm)], [c_109, c_20])).
% 2.76/1.40  tff(c_128, plain, (![A_54]: (k4_xboole_0(A_54, k1_xboole_0)=A_54)), inference(resolution, [status(thm)], [c_6, c_125])).
% 2.76/1.40  tff(c_38, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.76/1.40  tff(c_173, plain, (![A_65, B_66]: (r1_tarski(k1_relat_1(k5_relat_1(A_65, B_66)), k1_relat_1(A_65)) | ~v1_relat_1(B_66) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.76/1.40  tff(c_179, plain, (![B_66]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_66)), k1_xboole_0) | ~v1_relat_1(B_66) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_173])).
% 2.76/1.40  tff(c_194, plain, (![B_68]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_68)), k1_xboole_0) | ~v1_relat_1(B_68))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_179])).
% 2.76/1.40  tff(c_18, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=k1_xboole_0 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.76/1.40  tff(c_197, plain, (![B_68]: (k4_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0, B_68)), k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_68))), inference(resolution, [status(thm)], [c_194, c_18])).
% 2.76/1.40  tff(c_200, plain, (![B_69]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_69))=k1_xboole_0 | ~v1_relat_1(B_69))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_197])).
% 2.76/1.40  tff(c_28, plain, (![A_18]: (~v1_xboole_0(k1_relat_1(A_18)) | ~v1_relat_1(A_18) | v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.76/1.40  tff(c_215, plain, (![B_69]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_69)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_69)) | ~v1_relat_1(B_69))), inference(superposition, [status(thm), theory('equality')], [c_200, c_28])).
% 2.76/1.40  tff(c_303, plain, (![B_76]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_76)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_76)) | ~v1_relat_1(B_76))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_215])).
% 2.76/1.40  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.76/1.40  tff(c_333, plain, (![B_78]: (k5_relat_1(k1_xboole_0, B_78)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_78)) | ~v1_relat_1(B_78))), inference(resolution, [status(thm)], [c_303, c_8])).
% 2.76/1.40  tff(c_337, plain, (![B_17]: (k5_relat_1(k1_xboole_0, B_17)=k1_xboole_0 | ~v1_relat_1(B_17) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_333])).
% 2.76/1.40  tff(c_341, plain, (![B_79]: (k5_relat_1(k1_xboole_0, B_79)=k1_xboole_0 | ~v1_relat_1(B_79))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_337])).
% 2.76/1.40  tff(c_350, plain, (k5_relat_1(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_341])).
% 2.76/1.40  tff(c_356, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_350])).
% 2.76/1.40  tff(c_357, plain, (k5_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 2.76/1.40  tff(c_387, plain, (![A_90, B_91]: (r2_hidden('#skF_2'(A_90, B_91), B_91) | r1_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.76/1.40  tff(c_392, plain, (![B_92, A_93]: (~v1_xboole_0(B_92) | r1_xboole_0(A_93, B_92))), inference(resolution, [status(thm)], [c_387, c_2])).
% 2.76/1.40  tff(c_407, plain, (![A_98, B_99]: (k4_xboole_0(A_98, B_99)=A_98 | ~v1_xboole_0(B_99))), inference(resolution, [status(thm)], [c_392, c_20])).
% 2.76/1.40  tff(c_410, plain, (![A_98]: (k4_xboole_0(A_98, k1_xboole_0)=A_98)), inference(resolution, [status(thm)], [c_6, c_407])).
% 2.76/1.40  tff(c_36, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.76/1.40  tff(c_514, plain, (![A_118, B_119]: (r1_tarski(k2_relat_1(k5_relat_1(A_118, B_119)), k2_relat_1(B_119)) | ~v1_relat_1(B_119) | ~v1_relat_1(A_118))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.76/1.40  tff(c_523, plain, (![A_118]: (r1_tarski(k2_relat_1(k5_relat_1(A_118, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_118))), inference(superposition, [status(thm), theory('equality')], [c_36, c_514])).
% 2.76/1.40  tff(c_565, plain, (![A_121]: (r1_tarski(k2_relat_1(k5_relat_1(A_121, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_121))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_523])).
% 2.76/1.40  tff(c_568, plain, (![A_121]: (k4_xboole_0(k2_relat_1(k5_relat_1(A_121, k1_xboole_0)), k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_121))), inference(resolution, [status(thm)], [c_565, c_18])).
% 2.76/1.40  tff(c_571, plain, (![A_122]: (k2_relat_1(k5_relat_1(A_122, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_122))), inference(demodulation, [status(thm), theory('equality')], [c_410, c_568])).
% 2.76/1.40  tff(c_30, plain, (![A_19]: (~v1_xboole_0(k2_relat_1(A_19)) | ~v1_relat_1(A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.76/1.40  tff(c_586, plain, (![A_122]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_122, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_122, k1_xboole_0)) | ~v1_relat_1(A_122))), inference(superposition, [status(thm), theory('equality')], [c_571, c_30])).
% 2.76/1.40  tff(c_645, plain, (![A_126]: (~v1_relat_1(k5_relat_1(A_126, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_126, k1_xboole_0)) | ~v1_relat_1(A_126))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_586])).
% 2.76/1.40  tff(c_687, plain, (![A_129]: (k5_relat_1(A_129, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_129, k1_xboole_0)) | ~v1_relat_1(A_129))), inference(resolution, [status(thm)], [c_645, c_8])).
% 2.76/1.40  tff(c_691, plain, (![A_16]: (k5_relat_1(A_16, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_16))), inference(resolution, [status(thm)], [c_26, c_687])).
% 2.76/1.40  tff(c_754, plain, (![A_130]: (k5_relat_1(A_130, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_130))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_691])).
% 2.76/1.40  tff(c_763, plain, (k5_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_754])).
% 2.76/1.40  tff(c_770, plain, $false, inference(negUnitSimplification, [status(thm)], [c_357, c_763])).
% 2.76/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.40  
% 2.76/1.40  Inference rules
% 2.76/1.40  ----------------------
% 2.76/1.40  #Ref     : 0
% 2.76/1.40  #Sup     : 157
% 2.76/1.40  #Fact    : 0
% 2.76/1.40  #Define  : 0
% 2.76/1.40  #Split   : 2
% 2.76/1.40  #Chain   : 0
% 2.76/1.40  #Close   : 0
% 2.76/1.40  
% 2.76/1.40  Ordering : KBO
% 2.76/1.40  
% 2.76/1.40  Simplification rules
% 2.76/1.40  ----------------------
% 2.76/1.40  #Subsume      : 15
% 2.76/1.40  #Demod        : 127
% 2.76/1.40  #Tautology    : 81
% 2.76/1.40  #SimpNegUnit  : 6
% 2.76/1.40  #BackRed      : 3
% 2.76/1.40  
% 2.76/1.40  #Partial instantiations: 0
% 2.76/1.40  #Strategies tried      : 1
% 2.76/1.40  
% 2.76/1.40  Timing (in seconds)
% 2.76/1.40  ----------------------
% 2.76/1.40  Preprocessing        : 0.30
% 2.76/1.40  Parsing              : 0.17
% 2.76/1.40  CNF conversion       : 0.02
% 2.76/1.40  Main loop            : 0.33
% 2.76/1.40  Inferencing          : 0.14
% 2.76/1.40  Reduction            : 0.08
% 2.76/1.40  Demodulation         : 0.06
% 2.76/1.40  BG Simplification    : 0.02
% 2.76/1.40  Subsumption          : 0.06
% 2.76/1.40  Abstraction          : 0.01
% 2.76/1.40  MUC search           : 0.00
% 2.76/1.40  Cooper               : 0.00
% 2.76/1.40  Total                : 0.66
% 2.76/1.40  Index Insertion      : 0.00
% 2.76/1.40  Index Deletion       : 0.00
% 2.76/1.40  Index Matching       : 0.00
% 2.76/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
