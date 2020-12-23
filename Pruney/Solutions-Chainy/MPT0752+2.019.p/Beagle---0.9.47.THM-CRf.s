%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:29 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 220 expanded)
%              Number of leaves         :   31 (  84 expanded)
%              Depth                    :   16
%              Number of atoms          :  153 ( 516 expanded)
%              Number of equality atoms :   69 ( 240 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > v5_ordinal1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
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
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e9_44_1__funct_1)).

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

tff(c_125,plain,(
    ! [A_34] : k1_xboole_0 != A_34 ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_145,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_125])).

tff(c_146,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_6,plain,(
    ! [A_3] : v4_relat_1(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_260,plain,(
    ! [B_51,A_52] :
      ( k7_relat_1(B_51,A_52) = B_51
      | ~ v4_relat_1(B_51,A_52)
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_263,plain,(
    ! [A_3] :
      ( k7_relat_1(k1_xboole_0,A_3) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_260])).

tff(c_266,plain,(
    ! [A_3] : k7_relat_1(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_263])).

tff(c_84,plain,(
    ! [A_15] :
      ( k1_xboole_0 != A_15
      | '#skF_1'(A_15) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_79])).

tff(c_345,plain,(
    ! [B_68,A_69] :
      ( r1_xboole_0(k1_relat_1(B_68),A_69)
      | k7_relat_1(B_68,A_69) != k1_xboole_0
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_351,plain,(
    ! [A_15,A_69] :
      ( r1_xboole_0(A_15,A_69)
      | k7_relat_1('#skF_1'(A_15),A_69) != k1_xboole_0
      | ~ v1_relat_1('#skF_1'(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_345])).

tff(c_368,plain,(
    ! [A_72,A_73] :
      ( r1_xboole_0(A_72,A_73)
      | k7_relat_1('#skF_1'(A_72),A_73) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_351])).

tff(c_374,plain,(
    ! [A_15,A_73] :
      ( r1_xboole_0(A_15,A_73)
      | k7_relat_1(k1_xboole_0,A_73) != k1_xboole_0
      | k1_xboole_0 != A_15 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_368])).

tff(c_378,plain,(
    ! [A_73] : r1_xboole_0(k1_xboole_0,A_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_374])).

tff(c_157,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_32])).

tff(c_200,plain,(
    ! [A_47] :
      ( k2_relat_1(A_47) = k1_xboole_0
      | k1_relat_1(A_47) != k1_xboole_0
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_203,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_146,c_200])).

tff(c_212,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_203])).

tff(c_386,plain,(
    ! [B_76,A_77] :
      ( k10_relat_1(B_76,A_77) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_76),A_77)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_402,plain,(
    ! [A_77] :
      ( k10_relat_1(k1_xboole_0,A_77) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_77)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_386])).

tff(c_410,plain,(
    ! [A_77] : k10_relat_1(k1_xboole_0,A_77) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_378,c_402])).

tff(c_480,plain,(
    ! [B_87,A_88] :
      ( k10_relat_1(B_87,A_88) != k1_xboole_0
      | ~ r1_tarski(A_88,k2_relat_1(B_87))
      | k1_xboole_0 = A_88
      | ~ v1_relat_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_497,plain,(
    ! [A_88] :
      ( k10_relat_1(k1_xboole_0,A_88) != k1_xboole_0
      | ~ r1_tarski(A_88,k1_xboole_0)
      | k1_xboole_0 = A_88
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_480])).

tff(c_507,plain,(
    ! [A_89] :
      ( ~ r1_tarski(A_89,k1_xboole_0)
      | k1_xboole_0 = A_89 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_410,c_497])).

tff(c_519,plain,(
    ! [B_90] :
      ( k2_relat_1(B_90) = k1_xboole_0
      | ~ v5_relat_1(B_90,k1_xboole_0)
      | ~ v1_relat_1(B_90) ) ),
    inference(resolution,[status(thm)],[c_4,c_507])).

tff(c_527,plain,
    ( k2_relat_1('#skF_2'(k1_xboole_0)) = k1_xboole_0
    | ~ v1_relat_1('#skF_2'(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_42,c_519])).

tff(c_537,plain,(
    k2_relat_1('#skF_2'(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_527])).

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

tff(c_583,plain,(
    '#skF_2'(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_537,c_75])).

tff(c_38,plain,(
    ! [A_21] : v5_ordinal1('#skF_2'(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_620,plain,(
    v5_ordinal1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_583,c_38])).

tff(c_639,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_620])).

tff(c_640,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_642,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_640])).

tff(c_643,plain,(
    ! [A_93] :
      ( k1_relat_1(A_93) != k1_xboole_0
      | k1_xboole_0 = A_93
      | ~ v1_relat_1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_646,plain,(
    ! [A_15] :
      ( k1_relat_1('#skF_1'(A_15)) != k1_xboole_0
      | '#skF_1'(A_15) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_36,c_643])).

tff(c_663,plain,(
    ! [A_95] :
      ( k1_xboole_0 != A_95
      | '#skF_1'(A_95) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_646])).

tff(c_673,plain,(
    ! [A_95] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_95 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_663,c_36])).

tff(c_678,plain,(
    ! [A_95] : k1_xboole_0 != A_95 ),
    inference(negUnitSimplification,[status(thm)],[c_642,c_673])).

tff(c_686,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_678])).

tff(c_687,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_640])).

tff(c_689,plain,(
    ! [A_96] :
      ( k1_relat_1(A_96) != k1_xboole_0
      | k1_xboole_0 = A_96
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_695,plain,(
    ! [A_15] :
      ( k1_relat_1('#skF_1'(A_15)) != k1_xboole_0
      | '#skF_1'(A_15) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_36,c_689])).

tff(c_705,plain,(
    ! [A_97] :
      ( k1_xboole_0 != A_97
      | '#skF_1'(A_97) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_695])).

tff(c_34,plain,(
    ! [A_15] : v1_funct_1('#skF_1'(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_713,plain,(
    ! [A_97] :
      ( v1_funct_1(k1_xboole_0)
      | k1_xboole_0 != A_97 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_705,c_34])).

tff(c_720,plain,(
    ! [A_97] : k1_xboole_0 != A_97 ),
    inference(negUnitSimplification,[status(thm)],[c_687,c_713])).

tff(c_728,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_720])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:54:25 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.54  
% 2.91/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.54  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > v5_ordinal1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3
% 2.91/1.54  
% 2.91/1.54  %Foreground sorts:
% 2.91/1.54  
% 2.91/1.54  
% 2.91/1.54  %Background operators:
% 2.91/1.54  
% 2.91/1.54  
% 2.91/1.54  %Foreground operators:
% 2.91/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.91/1.54  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.91/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.91/1.54  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.91/1.54  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.91/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.91/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.91/1.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.91/1.54  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 2.91/1.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.91/1.54  tff('#skF_3', type, '#skF_3': $i).
% 2.91/1.54  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.91/1.54  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.91/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.54  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.91/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.91/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.54  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.91/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.91/1.54  
% 3.00/1.56  tff(f_35, axiom, (![A, B]: (v4_relat_1(k1_xboole_0, A) & v5_relat_1(k1_xboole_0, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l222_relat_1)).
% 3.00/1.56  tff(f_107, negated_conjecture, ~(![A]: (((v1_relat_1(k1_xboole_0) & v5_relat_1(k1_xboole_0, A)) & v1_funct_1(k1_xboole_0)) & v5_ordinal1(k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_ordinal1)).
% 3.00/1.56  tff(f_98, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) & v5_ordinal1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_ordinal1)).
% 3.00/1.56  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.00/1.56  tff(f_89, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e9_44_1__funct_1)).
% 3.00/1.56  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.00/1.56  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.00/1.56  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 3.00/1.56  tff(f_71, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 3.00/1.56  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 3.00/1.56  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_relat_1)).
% 3.00/1.56  tff(c_8, plain, (![B_4]: (v5_relat_1(k1_xboole_0, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.00/1.56  tff(c_46, plain, (~v1_relat_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0, '#skF_3') | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.00/1.56  tff(c_48, plain, (~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_46])).
% 3.00/1.56  tff(c_66, plain, (~v5_ordinal1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_48])).
% 3.00/1.56  tff(c_44, plain, (![A_21]: (v1_relat_1('#skF_2'(A_21)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.00/1.56  tff(c_42, plain, (![A_21]: (v5_relat_1('#skF_2'(A_21), A_21))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.00/1.56  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.00/1.56  tff(c_32, plain, (![A_15]: (k1_relat_1('#skF_1'(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.00/1.56  tff(c_36, plain, (![A_15]: (v1_relat_1('#skF_1'(A_15)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.00/1.56  tff(c_76, plain, (![A_33]: (k1_relat_1(A_33)!=k1_xboole_0 | k1_xboole_0=A_33 | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.00/1.56  tff(c_79, plain, (![A_15]: (k1_relat_1('#skF_1'(A_15))!=k1_xboole_0 | '#skF_1'(A_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_76])).
% 3.00/1.56  tff(c_87, plain, (![A_34]: (k1_xboole_0!=A_34 | '#skF_1'(A_34)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_79])).
% 3.00/1.56  tff(c_97, plain, (![A_34]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_34)), inference(superposition, [status(thm), theory('equality')], [c_87, c_36])).
% 3.00/1.56  tff(c_125, plain, (![A_34]: (k1_xboole_0!=A_34)), inference(splitLeft, [status(thm)], [c_97])).
% 3.00/1.56  tff(c_145, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_125])).
% 3.00/1.56  tff(c_146, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_97])).
% 3.00/1.56  tff(c_6, plain, (![A_3]: (v4_relat_1(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.00/1.56  tff(c_260, plain, (![B_51, A_52]: (k7_relat_1(B_51, A_52)=B_51 | ~v4_relat_1(B_51, A_52) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.00/1.56  tff(c_263, plain, (![A_3]: (k7_relat_1(k1_xboole_0, A_3)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_260])).
% 3.00/1.56  tff(c_266, plain, (![A_3]: (k7_relat_1(k1_xboole_0, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_146, c_263])).
% 3.00/1.56  tff(c_84, plain, (![A_15]: (k1_xboole_0!=A_15 | '#skF_1'(A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_79])).
% 3.00/1.56  tff(c_345, plain, (![B_68, A_69]: (r1_xboole_0(k1_relat_1(B_68), A_69) | k7_relat_1(B_68, A_69)!=k1_xboole_0 | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.00/1.56  tff(c_351, plain, (![A_15, A_69]: (r1_xboole_0(A_15, A_69) | k7_relat_1('#skF_1'(A_15), A_69)!=k1_xboole_0 | ~v1_relat_1('#skF_1'(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_345])).
% 3.00/1.56  tff(c_368, plain, (![A_72, A_73]: (r1_xboole_0(A_72, A_73) | k7_relat_1('#skF_1'(A_72), A_73)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_351])).
% 3.00/1.56  tff(c_374, plain, (![A_15, A_73]: (r1_xboole_0(A_15, A_73) | k7_relat_1(k1_xboole_0, A_73)!=k1_xboole_0 | k1_xboole_0!=A_15)), inference(superposition, [status(thm), theory('equality')], [c_84, c_368])).
% 3.00/1.56  tff(c_378, plain, (![A_73]: (r1_xboole_0(k1_xboole_0, A_73))), inference(demodulation, [status(thm), theory('equality')], [c_266, c_374])).
% 3.00/1.56  tff(c_157, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_87, c_32])).
% 3.00/1.56  tff(c_200, plain, (![A_47]: (k2_relat_1(A_47)=k1_xboole_0 | k1_relat_1(A_47)!=k1_xboole_0 | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.00/1.56  tff(c_203, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_146, c_200])).
% 3.00/1.56  tff(c_212, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_157, c_203])).
% 3.00/1.56  tff(c_386, plain, (![B_76, A_77]: (k10_relat_1(B_76, A_77)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_76), A_77) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.00/1.56  tff(c_402, plain, (![A_77]: (k10_relat_1(k1_xboole_0, A_77)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_77) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_212, c_386])).
% 3.00/1.56  tff(c_410, plain, (![A_77]: (k10_relat_1(k1_xboole_0, A_77)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_146, c_378, c_402])).
% 3.00/1.56  tff(c_480, plain, (![B_87, A_88]: (k10_relat_1(B_87, A_88)!=k1_xboole_0 | ~r1_tarski(A_88, k2_relat_1(B_87)) | k1_xboole_0=A_88 | ~v1_relat_1(B_87))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.00/1.56  tff(c_497, plain, (![A_88]: (k10_relat_1(k1_xboole_0, A_88)!=k1_xboole_0 | ~r1_tarski(A_88, k1_xboole_0) | k1_xboole_0=A_88 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_212, c_480])).
% 3.00/1.56  tff(c_507, plain, (![A_89]: (~r1_tarski(A_89, k1_xboole_0) | k1_xboole_0=A_89)), inference(demodulation, [status(thm), theory('equality')], [c_146, c_410, c_497])).
% 3.00/1.56  tff(c_519, plain, (![B_90]: (k2_relat_1(B_90)=k1_xboole_0 | ~v5_relat_1(B_90, k1_xboole_0) | ~v1_relat_1(B_90))), inference(resolution, [status(thm)], [c_4, c_507])).
% 3.00/1.56  tff(c_527, plain, (k2_relat_1('#skF_2'(k1_xboole_0))=k1_xboole_0 | ~v1_relat_1('#skF_2'(k1_xboole_0))), inference(resolution, [status(thm)], [c_42, c_519])).
% 3.00/1.56  tff(c_537, plain, (k2_relat_1('#skF_2'(k1_xboole_0))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_527])).
% 3.00/1.56  tff(c_67, plain, (![A_32]: (k2_relat_1(A_32)!=k1_xboole_0 | k1_xboole_0=A_32 | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.00/1.56  tff(c_75, plain, (![A_21]: (k2_relat_1('#skF_2'(A_21))!=k1_xboole_0 | '#skF_2'(A_21)=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_67])).
% 3.00/1.56  tff(c_583, plain, ('#skF_2'(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_537, c_75])).
% 3.00/1.56  tff(c_38, plain, (![A_21]: (v5_ordinal1('#skF_2'(A_21)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.00/1.56  tff(c_620, plain, (v5_ordinal1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_583, c_38])).
% 3.00/1.56  tff(c_639, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_620])).
% 3.00/1.56  tff(c_640, plain, (~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_48])).
% 3.00/1.56  tff(c_642, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_640])).
% 3.00/1.56  tff(c_643, plain, (![A_93]: (k1_relat_1(A_93)!=k1_xboole_0 | k1_xboole_0=A_93 | ~v1_relat_1(A_93))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.00/1.56  tff(c_646, plain, (![A_15]: (k1_relat_1('#skF_1'(A_15))!=k1_xboole_0 | '#skF_1'(A_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_643])).
% 3.00/1.56  tff(c_663, plain, (![A_95]: (k1_xboole_0!=A_95 | '#skF_1'(A_95)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_646])).
% 3.00/1.56  tff(c_673, plain, (![A_95]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_95)), inference(superposition, [status(thm), theory('equality')], [c_663, c_36])).
% 3.00/1.56  tff(c_678, plain, (![A_95]: (k1_xboole_0!=A_95)), inference(negUnitSimplification, [status(thm)], [c_642, c_673])).
% 3.00/1.56  tff(c_686, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_678])).
% 3.00/1.56  tff(c_687, plain, (~v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_640])).
% 3.00/1.56  tff(c_689, plain, (![A_96]: (k1_relat_1(A_96)!=k1_xboole_0 | k1_xboole_0=A_96 | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.00/1.56  tff(c_695, plain, (![A_15]: (k1_relat_1('#skF_1'(A_15))!=k1_xboole_0 | '#skF_1'(A_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_689])).
% 3.00/1.56  tff(c_705, plain, (![A_97]: (k1_xboole_0!=A_97 | '#skF_1'(A_97)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_695])).
% 3.00/1.56  tff(c_34, plain, (![A_15]: (v1_funct_1('#skF_1'(A_15)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.00/1.56  tff(c_713, plain, (![A_97]: (v1_funct_1(k1_xboole_0) | k1_xboole_0!=A_97)), inference(superposition, [status(thm), theory('equality')], [c_705, c_34])).
% 3.00/1.56  tff(c_720, plain, (![A_97]: (k1_xboole_0!=A_97)), inference(negUnitSimplification, [status(thm)], [c_687, c_713])).
% 3.00/1.56  tff(c_728, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_720])).
% 3.00/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.56  
% 3.00/1.56  Inference rules
% 3.00/1.56  ----------------------
% 3.00/1.56  #Ref     : 5
% 3.00/1.56  #Sup     : 137
% 3.00/1.56  #Fact    : 0
% 3.00/1.56  #Define  : 0
% 3.00/1.56  #Split   : 4
% 3.00/1.56  #Chain   : 0
% 3.00/1.56  #Close   : 0
% 3.00/1.56  
% 3.00/1.56  Ordering : KBO
% 3.00/1.56  
% 3.00/1.56  Simplification rules
% 3.00/1.56  ----------------------
% 3.00/1.56  #Subsume      : 17
% 3.00/1.56  #Demod        : 77
% 3.00/1.56  #Tautology    : 74
% 3.00/1.56  #SimpNegUnit  : 16
% 3.00/1.56  #BackRed      : 3
% 3.00/1.56  
% 3.00/1.56  #Partial instantiations: 0
% 3.00/1.56  #Strategies tried      : 1
% 3.00/1.56  
% 3.00/1.56  Timing (in seconds)
% 3.00/1.56  ----------------------
% 3.00/1.56  Preprocessing        : 0.33
% 3.00/1.56  Parsing              : 0.19
% 3.00/1.56  CNF conversion       : 0.02
% 3.00/1.56  Main loop            : 0.40
% 3.00/1.56  Inferencing          : 0.16
% 3.00/1.57  Reduction            : 0.12
% 3.00/1.57  Demodulation         : 0.08
% 3.00/1.57  BG Simplification    : 0.02
% 3.00/1.57  Subsumption          : 0.07
% 3.00/1.57  Abstraction          : 0.02
% 3.00/1.57  MUC search           : 0.00
% 3.00/1.57  Cooper               : 0.00
% 3.00/1.57  Total                : 0.78
% 3.00/1.57  Index Insertion      : 0.00
% 3.00/1.57  Index Deletion       : 0.00
% 3.00/1.57  Index Matching       : 0.00
% 3.00/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
