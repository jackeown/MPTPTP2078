%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:15 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 170 expanded)
%              Number of leaves         :   34 (  71 expanded)
%              Depth                    :    9
%              Number of atoms          :  133 ( 414 expanded)
%              Number of equality atoms :   67 ( 224 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_78,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_109,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_52,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_48,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_91,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_50,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(c_38,plain,(
    ! [A_19] : v1_relat_1('#skF_4'(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_36,plain,(
    ! [A_19] : v1_funct_1('#skF_4'(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_34,plain,(
    ! [A_19] : k1_relat_1('#skF_4'(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_50,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_71,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_198,plain,(
    ! [A_71,B_72] :
      ( r2_hidden('#skF_1'(A_71,B_72),B_72)
      | r2_hidden('#skF_2'(A_71,B_72),A_71)
      | B_72 = A_71 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_109,plain,(
    ! [A_54,B_55,C_56] :
      ( ~ r1_xboole_0(A_54,B_55)
      | ~ r2_hidden(C_56,k3_xboole_0(A_54,B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_112,plain,(
    ! [A_9,C_56] :
      ( ~ r1_xboole_0(A_9,k1_xboole_0)
      | ~ r2_hidden(C_56,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_109])).

tff(c_114,plain,(
    ! [C_56] : ~ r2_hidden(C_56,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_112])).

tff(c_214,plain,(
    ! [B_72] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_72),B_72)
      | k1_xboole_0 = B_72 ) ),
    inference(resolution,[status(thm)],[c_198,c_114])).

tff(c_42,plain,(
    ! [A_25,B_29] :
      ( k1_relat_1('#skF_5'(A_25,B_29)) = A_25
      | k1_xboole_0 = A_25 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_44,plain,(
    ! [A_25,B_29] :
      ( v1_funct_1('#skF_5'(A_25,B_29))
      | k1_xboole_0 = A_25 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_46,plain,(
    ! [A_25,B_29] :
      ( v1_relat_1('#skF_5'(A_25,B_29))
      | k1_xboole_0 = A_25 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(k1_tarski(A_14),B_15)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_117,plain,(
    ! [A_58,B_59] :
      ( k2_relat_1('#skF_5'(A_58,B_59)) = k1_tarski(B_59)
      | k1_xboole_0 = A_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_48,plain,(
    ! [C_32] :
      ( ~ r1_tarski(k2_relat_1(C_32),'#skF_6')
      | k1_relat_1(C_32) != '#skF_7'
      | ~ v1_funct_1(C_32)
      | ~ v1_relat_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_129,plain,(
    ! [B_60,A_61] :
      ( ~ r1_tarski(k1_tarski(B_60),'#skF_6')
      | k1_relat_1('#skF_5'(A_61,B_60)) != '#skF_7'
      | ~ v1_funct_1('#skF_5'(A_61,B_60))
      | ~ v1_relat_1('#skF_5'(A_61,B_60))
      | k1_xboole_0 = A_61 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_48])).

tff(c_216,plain,(
    ! [A_73,A_74] :
      ( k1_relat_1('#skF_5'(A_73,A_74)) != '#skF_7'
      | ~ v1_funct_1('#skF_5'(A_73,A_74))
      | ~ v1_relat_1('#skF_5'(A_73,A_74))
      | k1_xboole_0 = A_73
      | ~ r2_hidden(A_74,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_24,c_129])).

tff(c_323,plain,(
    ! [A_92,B_93] :
      ( k1_relat_1('#skF_5'(A_92,B_93)) != '#skF_7'
      | ~ v1_funct_1('#skF_5'(A_92,B_93))
      | ~ r2_hidden(B_93,'#skF_6')
      | k1_xboole_0 = A_92 ) ),
    inference(resolution,[status(thm)],[c_46,c_216])).

tff(c_328,plain,(
    ! [A_94,B_95] :
      ( k1_relat_1('#skF_5'(A_94,B_95)) != '#skF_7'
      | ~ r2_hidden(B_95,'#skF_6')
      | k1_xboole_0 = A_94 ) ),
    inference(resolution,[status(thm)],[c_44,c_323])).

tff(c_334,plain,(
    ! [A_25,B_29] :
      ( A_25 != '#skF_7'
      | ~ r2_hidden(B_29,'#skF_6')
      | k1_xboole_0 = A_25
      | k1_xboole_0 = A_25 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_328])).

tff(c_336,plain,(
    ! [B_96] : ~ r2_hidden(B_96,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_334])).

tff(c_344,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_214,c_336])).

tff(c_355,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_344])).

tff(c_357,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_334])).

tff(c_16,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_145,plain,(
    ! [A_64] :
      ( k2_relat_1(A_64) = k1_xboole_0
      | k1_relat_1(A_64) != k1_xboole_0
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_151,plain,(
    ! [A_19] :
      ( k2_relat_1('#skF_4'(A_19)) = k1_xboole_0
      | k1_relat_1('#skF_4'(A_19)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_145])).

tff(c_156,plain,(
    ! [A_65] :
      ( k2_relat_1('#skF_4'(A_65)) = k1_xboole_0
      | k1_xboole_0 != A_65 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_151])).

tff(c_165,plain,(
    ! [A_65] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_6')
      | k1_relat_1('#skF_4'(A_65)) != '#skF_7'
      | ~ v1_funct_1('#skF_4'(A_65))
      | ~ v1_relat_1('#skF_4'(A_65))
      | k1_xboole_0 != A_65 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_48])).

tff(c_172,plain,(
    ! [A_65] :
      ( A_65 != '#skF_7'
      | k1_xboole_0 != A_65 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_16,c_165])).

tff(c_177,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_172])).

tff(c_383,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_177])).

tff(c_385,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_384,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_393,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_384])).

tff(c_387,plain,(
    ! [A_10] : r1_tarski('#skF_7',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_16])).

tff(c_404,plain,(
    ! [A_10] : r1_tarski('#skF_6',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_387])).

tff(c_30,plain,(
    ! [A_18] :
      ( k2_relat_1(A_18) = k1_xboole_0
      | k1_relat_1(A_18) != k1_xboole_0
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_499,plain,(
    ! [A_125] :
      ( k2_relat_1(A_125) = '#skF_6'
      | k1_relat_1(A_125) != '#skF_6'
      | ~ v1_relat_1(A_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_385,c_30])).

tff(c_505,plain,(
    ! [A_19] :
      ( k2_relat_1('#skF_4'(A_19)) = '#skF_6'
      | k1_relat_1('#skF_4'(A_19)) != '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_38,c_499])).

tff(c_520,plain,(
    ! [A_128] :
      ( k2_relat_1('#skF_4'(A_128)) = '#skF_6'
      | A_128 != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_505])).

tff(c_406,plain,(
    ! [C_32] :
      ( ~ r1_tarski(k2_relat_1(C_32),'#skF_6')
      | k1_relat_1(C_32) != '#skF_6'
      | ~ v1_funct_1(C_32)
      | ~ v1_relat_1(C_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_48])).

tff(c_529,plain,(
    ! [A_128] :
      ( ~ r1_tarski('#skF_6','#skF_6')
      | k1_relat_1('#skF_4'(A_128)) != '#skF_6'
      | ~ v1_funct_1('#skF_4'(A_128))
      | ~ v1_relat_1('#skF_4'(A_128))
      | A_128 != '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_520,c_406])).

tff(c_536,plain,(
    ! [A_128] : A_128 != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_404,c_529])).

tff(c_386,plain,(
    ! [A_9] : k3_xboole_0(A_9,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_384,c_14])).

tff(c_408,plain,(
    ! [A_9] : k3_xboole_0(A_9,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_393,c_386])).

tff(c_550,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_536,c_408])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.33  
% 2.47/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.33  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5
% 2.47/1.33  
% 2.47/1.33  %Foreground sorts:
% 2.47/1.33  
% 2.47/1.33  
% 2.47/1.33  %Background operators:
% 2.47/1.33  
% 2.47/1.33  
% 2.47/1.33  %Foreground operators:
% 2.47/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.47/1.33  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.47/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.47/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.33  tff('#skF_7', type, '#skF_7': $i).
% 2.47/1.33  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.47/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.47/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.47/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.47/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.47/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.47/1.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.47/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.47/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.47/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.47/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.47/1.33  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.47/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.47/1.33  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.47/1.33  
% 2.47/1.35  tff(f_78, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 2.47/1.35  tff(f_109, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 2.47/1.35  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 2.47/1.35  tff(f_52, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.47/1.35  tff(f_48, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.47/1.35  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.47/1.35  tff(f_91, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 2.47/1.35  tff(f_58, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.47/1.35  tff(f_50, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.47/1.35  tff(f_66, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 2.47/1.35  tff(c_38, plain, (![A_19]: (v1_relat_1('#skF_4'(A_19)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.47/1.35  tff(c_36, plain, (![A_19]: (v1_funct_1('#skF_4'(A_19)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.47/1.35  tff(c_34, plain, (![A_19]: (k1_relat_1('#skF_4'(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.47/1.35  tff(c_50, plain, (k1_xboole_0='#skF_7' | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.47/1.35  tff(c_71, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_50])).
% 2.47/1.35  tff(c_198, plain, (![A_71, B_72]: (r2_hidden('#skF_1'(A_71, B_72), B_72) | r2_hidden('#skF_2'(A_71, B_72), A_71) | B_72=A_71)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.47/1.35  tff(c_18, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.47/1.35  tff(c_14, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.47/1.35  tff(c_109, plain, (![A_54, B_55, C_56]: (~r1_xboole_0(A_54, B_55) | ~r2_hidden(C_56, k3_xboole_0(A_54, B_55)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.47/1.35  tff(c_112, plain, (![A_9, C_56]: (~r1_xboole_0(A_9, k1_xboole_0) | ~r2_hidden(C_56, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_109])).
% 2.47/1.35  tff(c_114, plain, (![C_56]: (~r2_hidden(C_56, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_112])).
% 2.47/1.35  tff(c_214, plain, (![B_72]: (r2_hidden('#skF_1'(k1_xboole_0, B_72), B_72) | k1_xboole_0=B_72)), inference(resolution, [status(thm)], [c_198, c_114])).
% 2.47/1.35  tff(c_42, plain, (![A_25, B_29]: (k1_relat_1('#skF_5'(A_25, B_29))=A_25 | k1_xboole_0=A_25)), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.47/1.35  tff(c_44, plain, (![A_25, B_29]: (v1_funct_1('#skF_5'(A_25, B_29)) | k1_xboole_0=A_25)), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.47/1.35  tff(c_46, plain, (![A_25, B_29]: (v1_relat_1('#skF_5'(A_25, B_29)) | k1_xboole_0=A_25)), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.47/1.35  tff(c_24, plain, (![A_14, B_15]: (r1_tarski(k1_tarski(A_14), B_15) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.47/1.35  tff(c_117, plain, (![A_58, B_59]: (k2_relat_1('#skF_5'(A_58, B_59))=k1_tarski(B_59) | k1_xboole_0=A_58)), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.47/1.35  tff(c_48, plain, (![C_32]: (~r1_tarski(k2_relat_1(C_32), '#skF_6') | k1_relat_1(C_32)!='#skF_7' | ~v1_funct_1(C_32) | ~v1_relat_1(C_32))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.47/1.35  tff(c_129, plain, (![B_60, A_61]: (~r1_tarski(k1_tarski(B_60), '#skF_6') | k1_relat_1('#skF_5'(A_61, B_60))!='#skF_7' | ~v1_funct_1('#skF_5'(A_61, B_60)) | ~v1_relat_1('#skF_5'(A_61, B_60)) | k1_xboole_0=A_61)), inference(superposition, [status(thm), theory('equality')], [c_117, c_48])).
% 2.47/1.35  tff(c_216, plain, (![A_73, A_74]: (k1_relat_1('#skF_5'(A_73, A_74))!='#skF_7' | ~v1_funct_1('#skF_5'(A_73, A_74)) | ~v1_relat_1('#skF_5'(A_73, A_74)) | k1_xboole_0=A_73 | ~r2_hidden(A_74, '#skF_6'))), inference(resolution, [status(thm)], [c_24, c_129])).
% 2.47/1.35  tff(c_323, plain, (![A_92, B_93]: (k1_relat_1('#skF_5'(A_92, B_93))!='#skF_7' | ~v1_funct_1('#skF_5'(A_92, B_93)) | ~r2_hidden(B_93, '#skF_6') | k1_xboole_0=A_92)), inference(resolution, [status(thm)], [c_46, c_216])).
% 2.47/1.35  tff(c_328, plain, (![A_94, B_95]: (k1_relat_1('#skF_5'(A_94, B_95))!='#skF_7' | ~r2_hidden(B_95, '#skF_6') | k1_xboole_0=A_94)), inference(resolution, [status(thm)], [c_44, c_323])).
% 2.47/1.35  tff(c_334, plain, (![A_25, B_29]: (A_25!='#skF_7' | ~r2_hidden(B_29, '#skF_6') | k1_xboole_0=A_25 | k1_xboole_0=A_25)), inference(superposition, [status(thm), theory('equality')], [c_42, c_328])).
% 2.47/1.35  tff(c_336, plain, (![B_96]: (~r2_hidden(B_96, '#skF_6'))), inference(splitLeft, [status(thm)], [c_334])).
% 2.47/1.35  tff(c_344, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_214, c_336])).
% 2.47/1.35  tff(c_355, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_344])).
% 2.47/1.35  tff(c_357, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_334])).
% 2.47/1.35  tff(c_16, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.47/1.35  tff(c_145, plain, (![A_64]: (k2_relat_1(A_64)=k1_xboole_0 | k1_relat_1(A_64)!=k1_xboole_0 | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.47/1.35  tff(c_151, plain, (![A_19]: (k2_relat_1('#skF_4'(A_19))=k1_xboole_0 | k1_relat_1('#skF_4'(A_19))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_145])).
% 2.47/1.35  tff(c_156, plain, (![A_65]: (k2_relat_1('#skF_4'(A_65))=k1_xboole_0 | k1_xboole_0!=A_65)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_151])).
% 2.47/1.35  tff(c_165, plain, (![A_65]: (~r1_tarski(k1_xboole_0, '#skF_6') | k1_relat_1('#skF_4'(A_65))!='#skF_7' | ~v1_funct_1('#skF_4'(A_65)) | ~v1_relat_1('#skF_4'(A_65)) | k1_xboole_0!=A_65)), inference(superposition, [status(thm), theory('equality')], [c_156, c_48])).
% 2.47/1.35  tff(c_172, plain, (![A_65]: (A_65!='#skF_7' | k1_xboole_0!=A_65)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_16, c_165])).
% 2.47/1.35  tff(c_177, plain, (k1_xboole_0!='#skF_7'), inference(reflexivity, [status(thm), theory('equality')], [c_172])).
% 2.47/1.35  tff(c_383, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_357, c_177])).
% 2.47/1.35  tff(c_385, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_50])).
% 2.47/1.35  tff(c_384, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_50])).
% 2.47/1.35  tff(c_393, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_385, c_384])).
% 2.47/1.35  tff(c_387, plain, (![A_10]: (r1_tarski('#skF_7', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_384, c_16])).
% 2.47/1.35  tff(c_404, plain, (![A_10]: (r1_tarski('#skF_6', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_393, c_387])).
% 2.47/1.35  tff(c_30, plain, (![A_18]: (k2_relat_1(A_18)=k1_xboole_0 | k1_relat_1(A_18)!=k1_xboole_0 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.47/1.35  tff(c_499, plain, (![A_125]: (k2_relat_1(A_125)='#skF_6' | k1_relat_1(A_125)!='#skF_6' | ~v1_relat_1(A_125))), inference(demodulation, [status(thm), theory('equality')], [c_385, c_385, c_30])).
% 2.47/1.35  tff(c_505, plain, (![A_19]: (k2_relat_1('#skF_4'(A_19))='#skF_6' | k1_relat_1('#skF_4'(A_19))!='#skF_6')), inference(resolution, [status(thm)], [c_38, c_499])).
% 2.47/1.35  tff(c_520, plain, (![A_128]: (k2_relat_1('#skF_4'(A_128))='#skF_6' | A_128!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_505])).
% 2.47/1.35  tff(c_406, plain, (![C_32]: (~r1_tarski(k2_relat_1(C_32), '#skF_6') | k1_relat_1(C_32)!='#skF_6' | ~v1_funct_1(C_32) | ~v1_relat_1(C_32))), inference(demodulation, [status(thm), theory('equality')], [c_393, c_48])).
% 2.47/1.35  tff(c_529, plain, (![A_128]: (~r1_tarski('#skF_6', '#skF_6') | k1_relat_1('#skF_4'(A_128))!='#skF_6' | ~v1_funct_1('#skF_4'(A_128)) | ~v1_relat_1('#skF_4'(A_128)) | A_128!='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_520, c_406])).
% 2.47/1.35  tff(c_536, plain, (![A_128]: (A_128!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_404, c_529])).
% 2.47/1.35  tff(c_386, plain, (![A_9]: (k3_xboole_0(A_9, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_384, c_384, c_14])).
% 2.47/1.35  tff(c_408, plain, (![A_9]: (k3_xboole_0(A_9, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_393, c_393, c_386])).
% 2.47/1.35  tff(c_550, plain, $false, inference(negUnitSimplification, [status(thm)], [c_536, c_408])).
% 2.47/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.35  
% 2.47/1.35  Inference rules
% 2.47/1.35  ----------------------
% 2.47/1.35  #Ref     : 1
% 2.47/1.35  #Sup     : 90
% 2.47/1.35  #Fact    : 0
% 2.47/1.35  #Define  : 0
% 2.47/1.35  #Split   : 2
% 2.47/1.35  #Chain   : 0
% 2.47/1.35  #Close   : 0
% 2.47/1.35  
% 2.47/1.35  Ordering : KBO
% 2.47/1.35  
% 2.47/1.35  Simplification rules
% 2.47/1.35  ----------------------
% 2.47/1.35  #Subsume      : 14
% 2.47/1.35  #Demod        : 77
% 2.47/1.35  #Tautology    : 55
% 2.47/1.35  #SimpNegUnit  : 15
% 2.47/1.35  #BackRed      : 36
% 2.47/1.35  
% 2.47/1.35  #Partial instantiations: 0
% 2.47/1.35  #Strategies tried      : 1
% 2.47/1.35  
% 2.47/1.35  Timing (in seconds)
% 2.47/1.35  ----------------------
% 2.47/1.35  Preprocessing        : 0.32
% 2.47/1.35  Parsing              : 0.17
% 2.47/1.35  CNF conversion       : 0.02
% 2.47/1.35  Main loop            : 0.27
% 2.47/1.35  Inferencing          : 0.11
% 2.47/1.35  Reduction            : 0.08
% 2.47/1.35  Demodulation         : 0.05
% 2.47/1.35  BG Simplification    : 0.02
% 2.47/1.35  Subsumption          : 0.04
% 2.47/1.35  Abstraction          : 0.01
% 2.47/1.35  MUC search           : 0.00
% 2.47/1.35  Cooper               : 0.00
% 2.47/1.35  Total                : 0.63
% 2.47/1.35  Index Insertion      : 0.00
% 2.47/1.35  Index Deletion       : 0.00
% 2.47/1.35  Index Matching       : 0.00
% 2.47/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
