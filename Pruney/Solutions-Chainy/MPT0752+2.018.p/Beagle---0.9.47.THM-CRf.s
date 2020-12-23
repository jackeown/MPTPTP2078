%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:29 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 221 expanded)
%              Number of leaves         :   32 (  85 expanded)
%              Depth                    :   16
%              Number of atoms          :  153 ( 516 expanded)
%              Number of equality atoms :   69 ( 240 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > v5_ordinal1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > np__1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(np__1,type,(
    np__1: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_35,axiom,(
    ! [A,B] :
      ( v4_relat_1(k1_xboole_0,A)
      & v5_relat_1(k1_xboole_0,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,A)
        & v1_funct_1(k1_xboole_0)
        & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).

tff(f_98,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v5_relat_1(B,A)
      & v1_funct_1(B)
      & v5_ordinal1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_ordinal1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_89,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = np__1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k2_relat_1(B))
          & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

tff(c_8,plain,(
    ! [B_4] : v5_relat_1(k1_xboole_0,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_46,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,'#skF_3')
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_48,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_46])).

tff(c_66,plain,(
    ~ v5_ordinal1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_44,plain,(
    ! [A_21] : v1_relat_1('#skF_2'(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_42,plain,(
    ! [A_21] : v5_relat_1('#skF_2'(A_21),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    ! [A_15] : k1_relat_1('#skF_1'(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_36,plain,(
    ! [A_15] : v1_relat_1('#skF_1'(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_76,plain,(
    ! [A_33] :
      ( k1_relat_1(A_33) != k1_xboole_0
      | k1_xboole_0 = A_33
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_79,plain,(
    ! [A_15] :
      ( k1_relat_1('#skF_1'(A_15)) != k1_xboole_0
      | '#skF_1'(A_15) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_36,c_76])).

tff(c_87,plain,(
    ! [A_34] :
      ( k1_xboole_0 != A_34
      | '#skF_1'(A_34) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_79])).

tff(c_97,plain,(
    ! [A_34] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_34 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_36])).

tff(c_124,plain,(
    ! [A_34] : k1_xboole_0 != A_34 ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_143,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_124])).

tff(c_144,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_6,plain,(
    ! [A_3] : v4_relat_1(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_258,plain,(
    ! [B_51,A_52] :
      ( k7_relat_1(B_51,A_52) = B_51
      | ~ v4_relat_1(B_51,A_52)
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_261,plain,(
    ! [A_3] :
      ( k7_relat_1(k1_xboole_0,A_3) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_258])).

tff(c_264,plain,(
    ! [A_3] : k7_relat_1(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_261])).

tff(c_84,plain,(
    ! [A_15] :
      ( k1_xboole_0 != A_15
      | '#skF_1'(A_15) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_79])).

tff(c_343,plain,(
    ! [B_68,A_69] :
      ( r1_xboole_0(k1_relat_1(B_68),A_69)
      | k7_relat_1(B_68,A_69) != k1_xboole_0
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_349,plain,(
    ! [A_15,A_69] :
      ( r1_xboole_0(A_15,A_69)
      | k7_relat_1('#skF_1'(A_15),A_69) != k1_xboole_0
      | ~ v1_relat_1('#skF_1'(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_343])).

tff(c_366,plain,(
    ! [A_72,A_73] :
      ( r1_xboole_0(A_72,A_73)
      | k7_relat_1('#skF_1'(A_72),A_73) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_349])).

tff(c_372,plain,(
    ! [A_15,A_73] :
      ( r1_xboole_0(A_15,A_73)
      | k7_relat_1(k1_xboole_0,A_73) != k1_xboole_0
      | k1_xboole_0 != A_15 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_366])).

tff(c_376,plain,(
    ! [A_73] : r1_xboole_0(k1_xboole_0,A_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_372])).

tff(c_155,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_32])).

tff(c_198,plain,(
    ! [A_47] :
      ( k2_relat_1(A_47) = k1_xboole_0
      | k1_relat_1(A_47) != k1_xboole_0
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_201,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_144,c_198])).

tff(c_210,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_201])).

tff(c_384,plain,(
    ! [B_76,A_77] :
      ( k10_relat_1(B_76,A_77) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_76),A_77)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_400,plain,(
    ! [A_77] :
      ( k10_relat_1(k1_xboole_0,A_77) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_77)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_384])).

tff(c_408,plain,(
    ! [A_77] : k10_relat_1(k1_xboole_0,A_77) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_376,c_400])).

tff(c_478,plain,(
    ! [B_87,A_88] :
      ( k10_relat_1(B_87,A_88) != k1_xboole_0
      | ~ r1_tarski(A_88,k2_relat_1(B_87))
      | k1_xboole_0 = A_88
      | ~ v1_relat_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_495,plain,(
    ! [A_88] :
      ( k10_relat_1(k1_xboole_0,A_88) != k1_xboole_0
      | ~ r1_tarski(A_88,k1_xboole_0)
      | k1_xboole_0 = A_88
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_478])).

tff(c_505,plain,(
    ! [A_89] :
      ( ~ r1_tarski(A_89,k1_xboole_0)
      | k1_xboole_0 = A_89 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_408,c_495])).

tff(c_517,plain,(
    ! [B_90] :
      ( k2_relat_1(B_90) = k1_xboole_0
      | ~ v5_relat_1(B_90,k1_xboole_0)
      | ~ v1_relat_1(B_90) ) ),
    inference(resolution,[status(thm)],[c_4,c_505])).

tff(c_525,plain,
    ( k2_relat_1('#skF_2'(k1_xboole_0)) = k1_xboole_0
    | ~ v1_relat_1('#skF_2'(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_42,c_517])).

tff(c_535,plain,(
    k2_relat_1('#skF_2'(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_525])).

tff(c_67,plain,(
    ! [A_32] :
      ( k2_relat_1(A_32) != k1_xboole_0
      | k1_xboole_0 = A_32
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_75,plain,(
    ! [A_21] :
      ( k2_relat_1('#skF_2'(A_21)) != k1_xboole_0
      | '#skF_2'(A_21) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_44,c_67])).

tff(c_581,plain,(
    '#skF_2'(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_535,c_75])).

tff(c_38,plain,(
    ! [A_21] : v5_ordinal1('#skF_2'(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_618,plain,(
    v5_ordinal1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_581,c_38])).

tff(c_637,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_618])).

tff(c_638,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_640,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_638])).

tff(c_641,plain,(
    ! [A_93] :
      ( k1_relat_1(A_93) != k1_xboole_0
      | k1_xboole_0 = A_93
      | ~ v1_relat_1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_644,plain,(
    ! [A_15] :
      ( k1_relat_1('#skF_1'(A_15)) != k1_xboole_0
      | '#skF_1'(A_15) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_36,c_641])).

tff(c_661,plain,(
    ! [A_95] :
      ( k1_xboole_0 != A_95
      | '#skF_1'(A_95) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_644])).

tff(c_671,plain,(
    ! [A_95] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_95 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_661,c_36])).

tff(c_676,plain,(
    ! [A_95] : k1_xboole_0 != A_95 ),
    inference(negUnitSimplification,[status(thm)],[c_640,c_671])).

tff(c_684,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_676])).

tff(c_685,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_638])).

tff(c_687,plain,(
    ! [A_96] :
      ( k1_relat_1(A_96) != k1_xboole_0
      | k1_xboole_0 = A_96
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_693,plain,(
    ! [A_15] :
      ( k1_relat_1('#skF_1'(A_15)) != k1_xboole_0
      | '#skF_1'(A_15) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_36,c_687])).

tff(c_703,plain,(
    ! [A_97] :
      ( k1_xboole_0 != A_97
      | '#skF_1'(A_97) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_693])).

tff(c_34,plain,(
    ! [A_15] : v1_funct_1('#skF_1'(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_711,plain,(
    ! [A_97] :
      ( v1_funct_1(k1_xboole_0)
      | k1_xboole_0 != A_97 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_703,c_34])).

tff(c_718,plain,(
    ! [A_97] : k1_xboole_0 != A_97 ),
    inference(negUnitSimplification,[status(thm)],[c_685,c_711])).

tff(c_726,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_718])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:25:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.35  
% 2.63/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.35  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > v5_ordinal1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > np__1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3
% 2.63/1.35  
% 2.63/1.35  %Foreground sorts:
% 2.63/1.35  
% 2.63/1.35  
% 2.63/1.35  %Background operators:
% 2.63/1.35  
% 2.63/1.35  
% 2.63/1.35  %Foreground operators:
% 2.63/1.35  tff(np__1, type, np__1: $i).
% 2.63/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.63/1.35  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.63/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.63/1.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.63/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.63/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.63/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.63/1.35  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 2.63/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.63/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.63/1.35  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.63/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.63/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.35  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.63/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.63/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.35  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.63/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.63/1.35  
% 2.63/1.37  tff(f_35, axiom, (![A, B]: (v4_relat_1(k1_xboole_0, A) & v5_relat_1(k1_xboole_0, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l222_relat_1)).
% 2.63/1.37  tff(f_107, negated_conjecture, ~(![A]: (((v1_relat_1(k1_xboole_0) & v5_relat_1(k1_xboole_0, A)) & v1_funct_1(k1_xboole_0)) & v5_ordinal1(k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_ordinal1)).
% 2.63/1.37  tff(f_98, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) & v5_ordinal1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_ordinal1)).
% 2.63/1.37  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.63/1.37  tff(f_89, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = np__1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e7_25__funct_1)).
% 2.63/1.37  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.63/1.37  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.63/1.37  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 2.63/1.37  tff(f_71, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 2.63/1.37  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 2.63/1.37  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_relat_1)).
% 2.63/1.37  tff(c_8, plain, (![B_4]: (v5_relat_1(k1_xboole_0, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.63/1.37  tff(c_46, plain, (~v1_relat_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0, '#skF_3') | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.63/1.37  tff(c_48, plain, (~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_46])).
% 2.63/1.37  tff(c_66, plain, (~v5_ordinal1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_48])).
% 2.63/1.37  tff(c_44, plain, (![A_21]: (v1_relat_1('#skF_2'(A_21)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.63/1.37  tff(c_42, plain, (![A_21]: (v5_relat_1('#skF_2'(A_21), A_21))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.63/1.37  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.63/1.37  tff(c_32, plain, (![A_15]: (k1_relat_1('#skF_1'(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.63/1.37  tff(c_36, plain, (![A_15]: (v1_relat_1('#skF_1'(A_15)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.63/1.37  tff(c_76, plain, (![A_33]: (k1_relat_1(A_33)!=k1_xboole_0 | k1_xboole_0=A_33 | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.63/1.37  tff(c_79, plain, (![A_15]: (k1_relat_1('#skF_1'(A_15))!=k1_xboole_0 | '#skF_1'(A_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_76])).
% 2.63/1.37  tff(c_87, plain, (![A_34]: (k1_xboole_0!=A_34 | '#skF_1'(A_34)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_79])).
% 2.63/1.37  tff(c_97, plain, (![A_34]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_34)), inference(superposition, [status(thm), theory('equality')], [c_87, c_36])).
% 2.63/1.37  tff(c_124, plain, (![A_34]: (k1_xboole_0!=A_34)), inference(splitLeft, [status(thm)], [c_97])).
% 2.63/1.37  tff(c_143, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_124])).
% 2.63/1.37  tff(c_144, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_97])).
% 2.63/1.37  tff(c_6, plain, (![A_3]: (v4_relat_1(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.63/1.37  tff(c_258, plain, (![B_51, A_52]: (k7_relat_1(B_51, A_52)=B_51 | ~v4_relat_1(B_51, A_52) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.63/1.37  tff(c_261, plain, (![A_3]: (k7_relat_1(k1_xboole_0, A_3)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_258])).
% 2.63/1.37  tff(c_264, plain, (![A_3]: (k7_relat_1(k1_xboole_0, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_144, c_261])).
% 2.63/1.37  tff(c_84, plain, (![A_15]: (k1_xboole_0!=A_15 | '#skF_1'(A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_79])).
% 2.63/1.37  tff(c_343, plain, (![B_68, A_69]: (r1_xboole_0(k1_relat_1(B_68), A_69) | k7_relat_1(B_68, A_69)!=k1_xboole_0 | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.63/1.37  tff(c_349, plain, (![A_15, A_69]: (r1_xboole_0(A_15, A_69) | k7_relat_1('#skF_1'(A_15), A_69)!=k1_xboole_0 | ~v1_relat_1('#skF_1'(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_343])).
% 2.63/1.37  tff(c_366, plain, (![A_72, A_73]: (r1_xboole_0(A_72, A_73) | k7_relat_1('#skF_1'(A_72), A_73)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_349])).
% 2.63/1.37  tff(c_372, plain, (![A_15, A_73]: (r1_xboole_0(A_15, A_73) | k7_relat_1(k1_xboole_0, A_73)!=k1_xboole_0 | k1_xboole_0!=A_15)), inference(superposition, [status(thm), theory('equality')], [c_84, c_366])).
% 2.63/1.37  tff(c_376, plain, (![A_73]: (r1_xboole_0(k1_xboole_0, A_73))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_372])).
% 2.63/1.37  tff(c_155, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_87, c_32])).
% 2.63/1.37  tff(c_198, plain, (![A_47]: (k2_relat_1(A_47)=k1_xboole_0 | k1_relat_1(A_47)!=k1_xboole_0 | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.63/1.37  tff(c_201, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_144, c_198])).
% 2.63/1.37  tff(c_210, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_155, c_201])).
% 2.63/1.37  tff(c_384, plain, (![B_76, A_77]: (k10_relat_1(B_76, A_77)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_76), A_77) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.63/1.37  tff(c_400, plain, (![A_77]: (k10_relat_1(k1_xboole_0, A_77)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_77) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_210, c_384])).
% 2.63/1.37  tff(c_408, plain, (![A_77]: (k10_relat_1(k1_xboole_0, A_77)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_144, c_376, c_400])).
% 2.63/1.37  tff(c_478, plain, (![B_87, A_88]: (k10_relat_1(B_87, A_88)!=k1_xboole_0 | ~r1_tarski(A_88, k2_relat_1(B_87)) | k1_xboole_0=A_88 | ~v1_relat_1(B_87))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.63/1.37  tff(c_495, plain, (![A_88]: (k10_relat_1(k1_xboole_0, A_88)!=k1_xboole_0 | ~r1_tarski(A_88, k1_xboole_0) | k1_xboole_0=A_88 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_210, c_478])).
% 2.63/1.37  tff(c_505, plain, (![A_89]: (~r1_tarski(A_89, k1_xboole_0) | k1_xboole_0=A_89)), inference(demodulation, [status(thm), theory('equality')], [c_144, c_408, c_495])).
% 2.63/1.37  tff(c_517, plain, (![B_90]: (k2_relat_1(B_90)=k1_xboole_0 | ~v5_relat_1(B_90, k1_xboole_0) | ~v1_relat_1(B_90))), inference(resolution, [status(thm)], [c_4, c_505])).
% 2.63/1.37  tff(c_525, plain, (k2_relat_1('#skF_2'(k1_xboole_0))=k1_xboole_0 | ~v1_relat_1('#skF_2'(k1_xboole_0))), inference(resolution, [status(thm)], [c_42, c_517])).
% 2.63/1.37  tff(c_535, plain, (k2_relat_1('#skF_2'(k1_xboole_0))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_525])).
% 2.63/1.37  tff(c_67, plain, (![A_32]: (k2_relat_1(A_32)!=k1_xboole_0 | k1_xboole_0=A_32 | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.63/1.37  tff(c_75, plain, (![A_21]: (k2_relat_1('#skF_2'(A_21))!=k1_xboole_0 | '#skF_2'(A_21)=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_67])).
% 2.63/1.37  tff(c_581, plain, ('#skF_2'(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_535, c_75])).
% 2.63/1.37  tff(c_38, plain, (![A_21]: (v5_ordinal1('#skF_2'(A_21)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.63/1.37  tff(c_618, plain, (v5_ordinal1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_581, c_38])).
% 2.63/1.37  tff(c_637, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_618])).
% 2.63/1.37  tff(c_638, plain, (~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_48])).
% 2.63/1.37  tff(c_640, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_638])).
% 2.63/1.37  tff(c_641, plain, (![A_93]: (k1_relat_1(A_93)!=k1_xboole_0 | k1_xboole_0=A_93 | ~v1_relat_1(A_93))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.63/1.37  tff(c_644, plain, (![A_15]: (k1_relat_1('#skF_1'(A_15))!=k1_xboole_0 | '#skF_1'(A_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_641])).
% 2.63/1.37  tff(c_661, plain, (![A_95]: (k1_xboole_0!=A_95 | '#skF_1'(A_95)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_644])).
% 2.63/1.37  tff(c_671, plain, (![A_95]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_95)), inference(superposition, [status(thm), theory('equality')], [c_661, c_36])).
% 2.63/1.37  tff(c_676, plain, (![A_95]: (k1_xboole_0!=A_95)), inference(negUnitSimplification, [status(thm)], [c_640, c_671])).
% 2.63/1.37  tff(c_684, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_676])).
% 2.63/1.37  tff(c_685, plain, (~v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_638])).
% 2.63/1.37  tff(c_687, plain, (![A_96]: (k1_relat_1(A_96)!=k1_xboole_0 | k1_xboole_0=A_96 | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.63/1.37  tff(c_693, plain, (![A_15]: (k1_relat_1('#skF_1'(A_15))!=k1_xboole_0 | '#skF_1'(A_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_687])).
% 2.63/1.37  tff(c_703, plain, (![A_97]: (k1_xboole_0!=A_97 | '#skF_1'(A_97)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_693])).
% 2.63/1.37  tff(c_34, plain, (![A_15]: (v1_funct_1('#skF_1'(A_15)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.63/1.37  tff(c_711, plain, (![A_97]: (v1_funct_1(k1_xboole_0) | k1_xboole_0!=A_97)), inference(superposition, [status(thm), theory('equality')], [c_703, c_34])).
% 2.63/1.37  tff(c_718, plain, (![A_97]: (k1_xboole_0!=A_97)), inference(negUnitSimplification, [status(thm)], [c_685, c_711])).
% 2.63/1.37  tff(c_726, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_718])).
% 2.63/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.37  
% 2.63/1.37  Inference rules
% 2.63/1.37  ----------------------
% 2.63/1.37  #Ref     : 5
% 2.63/1.37  #Sup     : 137
% 2.63/1.37  #Fact    : 0
% 2.63/1.37  #Define  : 0
% 2.63/1.37  #Split   : 4
% 2.63/1.37  #Chain   : 0
% 2.63/1.37  #Close   : 0
% 2.63/1.37  
% 2.63/1.37  Ordering : KBO
% 2.63/1.37  
% 2.63/1.37  Simplification rules
% 2.63/1.37  ----------------------
% 2.63/1.37  #Subsume      : 17
% 2.63/1.37  #Demod        : 77
% 2.63/1.37  #Tautology    : 74
% 2.63/1.37  #SimpNegUnit  : 14
% 2.63/1.37  #BackRed      : 1
% 2.63/1.37  
% 2.63/1.37  #Partial instantiations: 0
% 2.63/1.37  #Strategies tried      : 1
% 2.63/1.37  
% 2.63/1.37  Timing (in seconds)
% 2.63/1.37  ----------------------
% 2.63/1.38  Preprocessing        : 0.29
% 2.63/1.38  Parsing              : 0.17
% 2.63/1.38  CNF conversion       : 0.02
% 2.63/1.38  Main loop            : 0.30
% 2.63/1.38  Inferencing          : 0.12
% 2.63/1.38  Reduction            : 0.09
% 2.63/1.38  Demodulation         : 0.06
% 2.63/1.38  BG Simplification    : 0.02
% 2.63/1.38  Subsumption          : 0.05
% 2.63/1.38  Abstraction          : 0.01
% 2.63/1.38  MUC search           : 0.00
% 2.63/1.38  Cooper               : 0.00
% 2.63/1.38  Total                : 0.63
% 2.63/1.38  Index Insertion      : 0.00
% 2.63/1.38  Index Deletion       : 0.00
% 2.63/1.38  Index Matching       : 0.00
% 2.63/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
