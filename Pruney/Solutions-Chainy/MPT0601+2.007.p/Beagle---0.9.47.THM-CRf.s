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
% DateTime   : Thu Dec  3 10:02:14 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   79 (  98 expanded)
%              Number of leaves         :   35 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :  132 ( 176 expanded)
%              Number of equality atoms :   50 (  66 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_110,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_60,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_62,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_88,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(c_70,plain,
    ( r2_hidden('#skF_4',k1_relat_1('#skF_5'))
    | k11_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_99,plain,(
    k11_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_62,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_38,plain,(
    ! [A_18,B_19] :
      ( r1_xboole_0(k1_tarski(A_18),B_19)
      | r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_192,plain,(
    ! [A_69,B_70] :
      ( k7_relat_1(A_69,B_70) = k1_xboole_0
      | ~ r1_xboole_0(B_70,k1_relat_1(A_69))
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_297,plain,(
    ! [A_83,A_84] :
      ( k7_relat_1(A_83,k1_tarski(A_84)) = k1_xboole_0
      | ~ v1_relat_1(A_83)
      | r2_hidden(A_84,k1_relat_1(A_83)) ) ),
    inference(resolution,[status(thm)],[c_38,c_192])).

tff(c_64,plain,
    ( k11_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | ~ r2_hidden('#skF_4',k1_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_137,plain,(
    ~ r2_hidden('#skF_4',k1_relat_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_64])).

tff(c_304,plain,
    ( k7_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_297,c_137])).

tff(c_311,plain,(
    k7_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_304])).

tff(c_60,plain,(
    ! [B_32,A_31] :
      ( r1_xboole_0(k1_relat_1(B_32),A_31)
      | k7_relat_1(B_32,A_31) != k1_xboole_0
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_213,plain,(
    ! [B_71,A_72] :
      ( k9_relat_1(B_71,A_72) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_71),A_72)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_254,plain,(
    ! [B_79,A_80] :
      ( k9_relat_1(B_79,A_80) = k1_xboole_0
      | k7_relat_1(B_79,A_80) != k1_xboole_0
      | ~ v1_relat_1(B_79) ) ),
    inference(resolution,[status(thm)],[c_60,c_213])).

tff(c_258,plain,(
    ! [A_81] :
      ( k9_relat_1('#skF_5',A_81) = k1_xboole_0
      | k7_relat_1('#skF_5',A_81) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_62,c_254])).

tff(c_40,plain,(
    ! [A_20,B_22] :
      ( k9_relat_1(A_20,k1_tarski(B_22)) = k11_relat_1(A_20,B_22)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_270,plain,(
    ! [B_22] :
      ( k11_relat_1('#skF_5',B_22) = k1_xboole_0
      | ~ v1_relat_1('#skF_5')
      | k7_relat_1('#skF_5',k1_tarski(B_22)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_40])).

tff(c_289,plain,(
    ! [B_22] :
      ( k11_relat_1('#skF_5',B_22) = k1_xboole_0
      | k7_relat_1('#skF_5',k1_tarski(B_22)) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_270])).

tff(c_316,plain,(
    k11_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_289])).

tff(c_325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_316])).

tff(c_327,plain,(
    k11_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_34,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_333,plain,(
    ! [A_87,B_88] : k1_enumset1(A_87,A_87,B_88) = k2_tarski(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_14,plain,(
    ! [E_14,A_8,C_10] : r2_hidden(E_14,k1_enumset1(A_8,E_14,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_351,plain,(
    ! [A_89,B_90] : r2_hidden(A_89,k2_tarski(A_89,B_90)) ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_14])).

tff(c_354,plain,(
    ! [A_15] : r2_hidden(A_15,k1_tarski(A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_351])).

tff(c_326,plain,(
    r2_hidden('#skF_4',k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_8,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_364,plain,(
    ! [A_94,B_95,C_96] :
      ( ~ r1_xboole_0(A_94,B_95)
      | ~ r2_hidden(C_96,k3_xboole_0(A_94,B_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_367,plain,(
    ! [A_6,C_96] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_96,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_364])).

tff(c_369,plain,(
    ! [C_96] : ~ r2_hidden(C_96,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_367])).

tff(c_50,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_409,plain,(
    ! [B_105,A_106] :
      ( r1_xboole_0(k1_relat_1(B_105),A_106)
      | k9_relat_1(B_105,A_106) != k1_xboole_0
      | ~ v1_relat_1(B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_58,plain,(
    ! [B_32,A_31] :
      ( k7_relat_1(B_32,A_31) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_32),A_31)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_472,plain,(
    ! [B_114,A_115] :
      ( k7_relat_1(B_114,A_115) = k1_xboole_0
      | k9_relat_1(B_114,A_115) != k1_xboole_0
      | ~ v1_relat_1(B_114) ) ),
    inference(resolution,[status(thm)],[c_409,c_58])).

tff(c_476,plain,(
    ! [A_20,B_22] :
      ( k7_relat_1(A_20,k1_tarski(B_22)) = k1_xboole_0
      | k11_relat_1(A_20,B_22) != k1_xboole_0
      | ~ v1_relat_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_472])).

tff(c_614,plain,(
    ! [A_139,C_140,B_141] :
      ( r2_hidden(A_139,k1_relat_1(k7_relat_1(C_140,B_141)))
      | ~ r2_hidden(A_139,k1_relat_1(C_140))
      | ~ r2_hidden(A_139,B_141)
      | ~ v1_relat_1(C_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_623,plain,(
    ! [A_139,A_20,B_22] :
      ( r2_hidden(A_139,k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(A_139,k1_relat_1(A_20))
      | ~ r2_hidden(A_139,k1_tarski(B_22))
      | ~ v1_relat_1(A_20)
      | k11_relat_1(A_20,B_22) != k1_xboole_0
      | ~ v1_relat_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_476,c_614])).

tff(c_629,plain,(
    ! [A_139,A_20,B_22] :
      ( r2_hidden(A_139,k1_xboole_0)
      | ~ r2_hidden(A_139,k1_relat_1(A_20))
      | ~ r2_hidden(A_139,k1_tarski(B_22))
      | ~ v1_relat_1(A_20)
      | k11_relat_1(A_20,B_22) != k1_xboole_0
      | ~ v1_relat_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_623])).

tff(c_791,plain,(
    ! [A_165,A_166,B_167] :
      ( ~ r2_hidden(A_165,k1_relat_1(A_166))
      | ~ r2_hidden(A_165,k1_tarski(B_167))
      | ~ v1_relat_1(A_166)
      | k11_relat_1(A_166,B_167) != k1_xboole_0
      | ~ v1_relat_1(A_166)
      | ~ v1_relat_1(A_166) ) ),
    inference(negUnitSimplification,[status(thm)],[c_369,c_629])).

tff(c_797,plain,(
    ! [B_167] :
      ( ~ r2_hidden('#skF_4',k1_tarski(B_167))
      | k11_relat_1('#skF_5',B_167) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_326,c_791])).

tff(c_805,plain,(
    ! [B_168] :
      ( ~ r2_hidden('#skF_4',k1_tarski(B_168))
      | k11_relat_1('#skF_5',B_168) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_797])).

tff(c_809,plain,(
    k11_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_354,c_805])).

tff(c_813,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_809])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:14:36 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.43  
% 2.73/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.43  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.73/1.43  
% 2.73/1.43  %Foreground sorts:
% 2.73/1.43  
% 2.73/1.43  
% 2.73/1.43  %Background operators:
% 2.73/1.43  
% 2.73/1.43  
% 2.73/1.43  %Foreground operators:
% 2.73/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.73/1.43  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.73/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.73/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.73/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.73/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.73/1.43  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.73/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.73/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.73/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.73/1.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.73/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.73/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.73/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.73/1.43  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.73/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.73/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.73/1.43  
% 2.73/1.45  tff(f_110, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 2.73/1.45  tff(f_67, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.73/1.45  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 2.73/1.45  tff(f_102, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 2.73/1.45  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 2.73/1.45  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 2.73/1.45  tff(f_60, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.73/1.45  tff(f_62, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.73/1.45  tff(f_58, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.73/1.45  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.73/1.45  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.73/1.45  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.73/1.45  tff(f_88, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.73/1.45  tff(f_96, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 2.73/1.45  tff(c_70, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_5')) | k11_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.73/1.45  tff(c_99, plain, (k11_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_70])).
% 2.73/1.45  tff(c_62, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.73/1.45  tff(c_38, plain, (![A_18, B_19]: (r1_xboole_0(k1_tarski(A_18), B_19) | r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.73/1.45  tff(c_192, plain, (![A_69, B_70]: (k7_relat_1(A_69, B_70)=k1_xboole_0 | ~r1_xboole_0(B_70, k1_relat_1(A_69)) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.73/1.45  tff(c_297, plain, (![A_83, A_84]: (k7_relat_1(A_83, k1_tarski(A_84))=k1_xboole_0 | ~v1_relat_1(A_83) | r2_hidden(A_84, k1_relat_1(A_83)))), inference(resolution, [status(thm)], [c_38, c_192])).
% 2.73/1.45  tff(c_64, plain, (k11_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | ~r2_hidden('#skF_4', k1_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.73/1.45  tff(c_137, plain, (~r2_hidden('#skF_4', k1_relat_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_99, c_64])).
% 2.73/1.45  tff(c_304, plain, (k7_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_297, c_137])).
% 2.73/1.45  tff(c_311, plain, (k7_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_62, c_304])).
% 2.73/1.45  tff(c_60, plain, (![B_32, A_31]: (r1_xboole_0(k1_relat_1(B_32), A_31) | k7_relat_1(B_32, A_31)!=k1_xboole_0 | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.73/1.45  tff(c_213, plain, (![B_71, A_72]: (k9_relat_1(B_71, A_72)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_71), A_72) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.73/1.45  tff(c_254, plain, (![B_79, A_80]: (k9_relat_1(B_79, A_80)=k1_xboole_0 | k7_relat_1(B_79, A_80)!=k1_xboole_0 | ~v1_relat_1(B_79))), inference(resolution, [status(thm)], [c_60, c_213])).
% 2.73/1.45  tff(c_258, plain, (![A_81]: (k9_relat_1('#skF_5', A_81)=k1_xboole_0 | k7_relat_1('#skF_5', A_81)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_62, c_254])).
% 2.73/1.45  tff(c_40, plain, (![A_20, B_22]: (k9_relat_1(A_20, k1_tarski(B_22))=k11_relat_1(A_20, B_22) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.73/1.45  tff(c_270, plain, (![B_22]: (k11_relat_1('#skF_5', B_22)=k1_xboole_0 | ~v1_relat_1('#skF_5') | k7_relat_1('#skF_5', k1_tarski(B_22))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_258, c_40])).
% 2.73/1.45  tff(c_289, plain, (![B_22]: (k11_relat_1('#skF_5', B_22)=k1_xboole_0 | k7_relat_1('#skF_5', k1_tarski(B_22))!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_270])).
% 2.73/1.45  tff(c_316, plain, (k11_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_311, c_289])).
% 2.73/1.45  tff(c_325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_316])).
% 2.73/1.45  tff(c_327, plain, (k11_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_70])).
% 2.73/1.45  tff(c_34, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.73/1.45  tff(c_333, plain, (![A_87, B_88]: (k1_enumset1(A_87, A_87, B_88)=k2_tarski(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.73/1.45  tff(c_14, plain, (![E_14, A_8, C_10]: (r2_hidden(E_14, k1_enumset1(A_8, E_14, C_10)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.73/1.45  tff(c_351, plain, (![A_89, B_90]: (r2_hidden(A_89, k2_tarski(A_89, B_90)))), inference(superposition, [status(thm), theory('equality')], [c_333, c_14])).
% 2.73/1.45  tff(c_354, plain, (![A_15]: (r2_hidden(A_15, k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_351])).
% 2.73/1.45  tff(c_326, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_70])).
% 2.73/1.45  tff(c_8, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.73/1.45  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.73/1.45  tff(c_364, plain, (![A_94, B_95, C_96]: (~r1_xboole_0(A_94, B_95) | ~r2_hidden(C_96, k3_xboole_0(A_94, B_95)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.73/1.45  tff(c_367, plain, (![A_6, C_96]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_96, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_364])).
% 2.73/1.45  tff(c_369, plain, (![C_96]: (~r2_hidden(C_96, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_367])).
% 2.73/1.45  tff(c_50, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.73/1.45  tff(c_409, plain, (![B_105, A_106]: (r1_xboole_0(k1_relat_1(B_105), A_106) | k9_relat_1(B_105, A_106)!=k1_xboole_0 | ~v1_relat_1(B_105))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.73/1.45  tff(c_58, plain, (![B_32, A_31]: (k7_relat_1(B_32, A_31)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_32), A_31) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.73/1.45  tff(c_472, plain, (![B_114, A_115]: (k7_relat_1(B_114, A_115)=k1_xboole_0 | k9_relat_1(B_114, A_115)!=k1_xboole_0 | ~v1_relat_1(B_114))), inference(resolution, [status(thm)], [c_409, c_58])).
% 2.73/1.45  tff(c_476, plain, (![A_20, B_22]: (k7_relat_1(A_20, k1_tarski(B_22))=k1_xboole_0 | k11_relat_1(A_20, B_22)!=k1_xboole_0 | ~v1_relat_1(A_20) | ~v1_relat_1(A_20))), inference(superposition, [status(thm), theory('equality')], [c_40, c_472])).
% 2.73/1.45  tff(c_614, plain, (![A_139, C_140, B_141]: (r2_hidden(A_139, k1_relat_1(k7_relat_1(C_140, B_141))) | ~r2_hidden(A_139, k1_relat_1(C_140)) | ~r2_hidden(A_139, B_141) | ~v1_relat_1(C_140))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.73/1.45  tff(c_623, plain, (![A_139, A_20, B_22]: (r2_hidden(A_139, k1_relat_1(k1_xboole_0)) | ~r2_hidden(A_139, k1_relat_1(A_20)) | ~r2_hidden(A_139, k1_tarski(B_22)) | ~v1_relat_1(A_20) | k11_relat_1(A_20, B_22)!=k1_xboole_0 | ~v1_relat_1(A_20) | ~v1_relat_1(A_20))), inference(superposition, [status(thm), theory('equality')], [c_476, c_614])).
% 2.73/1.45  tff(c_629, plain, (![A_139, A_20, B_22]: (r2_hidden(A_139, k1_xboole_0) | ~r2_hidden(A_139, k1_relat_1(A_20)) | ~r2_hidden(A_139, k1_tarski(B_22)) | ~v1_relat_1(A_20) | k11_relat_1(A_20, B_22)!=k1_xboole_0 | ~v1_relat_1(A_20) | ~v1_relat_1(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_623])).
% 2.73/1.45  tff(c_791, plain, (![A_165, A_166, B_167]: (~r2_hidden(A_165, k1_relat_1(A_166)) | ~r2_hidden(A_165, k1_tarski(B_167)) | ~v1_relat_1(A_166) | k11_relat_1(A_166, B_167)!=k1_xboole_0 | ~v1_relat_1(A_166) | ~v1_relat_1(A_166))), inference(negUnitSimplification, [status(thm)], [c_369, c_629])).
% 2.73/1.45  tff(c_797, plain, (![B_167]: (~r2_hidden('#skF_4', k1_tarski(B_167)) | k11_relat_1('#skF_5', B_167)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_326, c_791])).
% 2.73/1.45  tff(c_805, plain, (![B_168]: (~r2_hidden('#skF_4', k1_tarski(B_168)) | k11_relat_1('#skF_5', B_168)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_797])).
% 2.73/1.45  tff(c_809, plain, (k11_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_354, c_805])).
% 2.73/1.45  tff(c_813, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_327, c_809])).
% 2.73/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.45  
% 2.73/1.45  Inference rules
% 2.73/1.45  ----------------------
% 2.73/1.45  #Ref     : 0
% 2.73/1.45  #Sup     : 165
% 2.73/1.45  #Fact    : 0
% 2.73/1.45  #Define  : 0
% 2.73/1.45  #Split   : 3
% 2.73/1.45  #Chain   : 0
% 2.73/1.45  #Close   : 0
% 2.73/1.45  
% 2.73/1.45  Ordering : KBO
% 2.73/1.45  
% 2.73/1.45  Simplification rules
% 2.73/1.45  ----------------------
% 2.73/1.45  #Subsume      : 28
% 2.73/1.45  #Demod        : 53
% 2.73/1.45  #Tautology    : 75
% 2.73/1.45  #SimpNegUnit  : 13
% 2.73/1.45  #BackRed      : 0
% 2.73/1.45  
% 2.73/1.45  #Partial instantiations: 0
% 2.73/1.45  #Strategies tried      : 1
% 2.73/1.45  
% 2.73/1.45  Timing (in seconds)
% 2.73/1.45  ----------------------
% 2.73/1.45  Preprocessing        : 0.33
% 2.73/1.45  Parsing              : 0.17
% 2.73/1.45  CNF conversion       : 0.03
% 2.73/1.45  Main loop            : 0.35
% 2.73/1.45  Inferencing          : 0.13
% 2.73/1.45  Reduction            : 0.10
% 2.73/1.45  Demodulation         : 0.07
% 2.73/1.45  BG Simplification    : 0.02
% 2.73/1.45  Subsumption          : 0.07
% 2.73/1.45  Abstraction          : 0.02
% 2.73/1.45  MUC search           : 0.00
% 2.73/1.45  Cooper               : 0.00
% 2.73/1.45  Total                : 0.71
% 2.73/1.45  Index Insertion      : 0.00
% 2.73/1.45  Index Deletion       : 0.00
% 2.73/1.45  Index Matching       : 0.00
% 2.73/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
