%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:14 EST 2020

% Result     : Theorem 3.87s
% Output     : CNFRefutation 4.10s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 117 expanded)
%              Number of leaves         :   39 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :  108 ( 198 expanded)
%              Number of equality atoms :   28 (  54 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_14 > #skF_2 > #skF_13 > #skF_8 > #skF_11 > #skF_3 > #skF_12 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_11',type,(
    '#skF_11': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_113,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_105,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_62,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_60,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(c_66,plain,(
    v1_relat_1('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_74,plain,
    ( r2_hidden('#skF_13',k1_relat_1('#skF_14'))
    | k11_relat_1('#skF_14','#skF_13') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_111,plain,(
    k11_relat_1('#skF_14','#skF_13') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_42,plain,(
    ! [A_19] :
      ( r2_hidden('#skF_4'(A_19),A_19)
      | v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_348,plain,(
    ! [A_138,B_139,C_140] :
      ( r2_hidden(k4_tarski(A_138,B_139),C_140)
      | ~ r2_hidden(B_139,k11_relat_1(C_140,A_138))
      | ~ v1_relat_1(C_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_46,plain,(
    ! [C_52,A_37,D_55] :
      ( r2_hidden(C_52,k1_relat_1(A_37))
      | ~ r2_hidden(k4_tarski(C_52,D_55),A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_357,plain,(
    ! [A_141,C_142,B_143] :
      ( r2_hidden(A_141,k1_relat_1(C_142))
      | ~ r2_hidden(B_143,k11_relat_1(C_142,A_141))
      | ~ v1_relat_1(C_142) ) ),
    inference(resolution,[status(thm)],[c_348,c_46])).

tff(c_381,plain,(
    ! [A_144,C_145] :
      ( r2_hidden(A_144,k1_relat_1(C_145))
      | ~ v1_relat_1(C_145)
      | v1_relat_1(k11_relat_1(C_145,A_144)) ) ),
    inference(resolution,[status(thm)],[c_42,c_357])).

tff(c_68,plain,
    ( k11_relat_1('#skF_14','#skF_13') = k1_xboole_0
    | ~ r2_hidden('#skF_13',k1_relat_1('#skF_14')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_119,plain,(
    ~ r2_hidden('#skF_13',k1_relat_1('#skF_14')) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_68])).

tff(c_392,plain,
    ( ~ v1_relat_1('#skF_14')
    | v1_relat_1(k11_relat_1('#skF_14','#skF_13')) ),
    inference(resolution,[status(thm)],[c_381,c_119])).

tff(c_397,plain,(
    v1_relat_1(k11_relat_1('#skF_14','#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_392])).

tff(c_64,plain,(
    ! [A_61] :
      ( k1_xboole_0 = A_61
      | r2_hidden(k4_tarski('#skF_11'(A_61),'#skF_12'(A_61)),A_61)
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_89,plain,(
    ! [A_78,B_79] : k1_enumset1(A_78,A_78,B_79) = k2_tarski(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_14,plain,(
    ! [E_12,B_7,C_8] : r2_hidden(E_12,k1_enumset1(E_12,B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_101,plain,(
    ! [A_78,B_79] : r2_hidden(A_78,k2_tarski(A_78,B_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_14])).

tff(c_132,plain,(
    ! [C_94,A_95,D_96] :
      ( r2_hidden(C_94,k1_relat_1(A_95))
      | ~ r2_hidden(k4_tarski(C_94,D_96),A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_169,plain,(
    ! [C_99,D_100,B_101] : r2_hidden(C_99,k1_relat_1(k2_tarski(k4_tarski(C_99,D_100),B_101))) ),
    inference(resolution,[status(thm)],[c_101,c_132])).

tff(c_178,plain,(
    ! [C_52,D_55,D_100,B_101] : r2_hidden(C_52,k1_relat_1(k1_relat_1(k2_tarski(k4_tarski(k4_tarski(C_52,D_55),D_100),B_101)))) ),
    inference(resolution,[status(thm)],[c_169,c_46])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_554,plain,(
    ! [A_162,C_163,B_164] :
      ( r2_hidden(A_162,k1_relat_1(C_163))
      | ~ v1_relat_1(C_163)
      | r1_xboole_0(k11_relat_1(C_163,A_162),B_164) ) ),
    inference(resolution,[status(thm)],[c_6,c_357])).

tff(c_565,plain,(
    ! [B_164] :
      ( ~ v1_relat_1('#skF_14')
      | r1_xboole_0(k11_relat_1('#skF_14','#skF_13'),B_164) ) ),
    inference(resolution,[status(thm)],[c_554,c_119])).

tff(c_574,plain,(
    ! [B_165] : r1_xboole_0(k11_relat_1('#skF_14','#skF_13'),B_165) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_565])).

tff(c_2,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_578,plain,(
    ! [C_166,B_167] :
      ( ~ r2_hidden(C_166,B_167)
      | ~ r2_hidden(C_166,k11_relat_1('#skF_14','#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_574,c_2])).

tff(c_654,plain,(
    ! [C_168] : ~ r2_hidden(C_168,k11_relat_1('#skF_14','#skF_13')) ),
    inference(resolution,[status(thm)],[c_178,c_578])).

tff(c_666,plain,
    ( k11_relat_1('#skF_14','#skF_13') = k1_xboole_0
    | ~ v1_relat_1(k11_relat_1('#skF_14','#skF_13')) ),
    inference(resolution,[status(thm)],[c_64,c_654])).

tff(c_685,plain,(
    k11_relat_1('#skF_14','#skF_13') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_666])).

tff(c_687,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_685])).

tff(c_689,plain,(
    k11_relat_1('#skF_14','#skF_13') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_36,plain,(
    ! [A_16,B_18] :
      ( k9_relat_1(A_16,k1_tarski(B_18)) = k11_relat_1(A_16,B_18)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_688,plain,(
    r2_hidden('#skF_13',k1_relat_1('#skF_14')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_32,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10,plain,(
    ! [E_12,A_6,B_7] : r2_hidden(E_12,k1_enumset1(A_6,B_7,E_12)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_107,plain,(
    ! [B_80,A_81] : r2_hidden(B_80,k2_tarski(A_81,B_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_10])).

tff(c_110,plain,(
    ! [A_13] : r2_hidden(A_13,k1_tarski(A_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_107])).

tff(c_808,plain,(
    ! [B_206,A_207] :
      ( r1_xboole_0(k1_relat_1(B_206),A_207)
      | k9_relat_1(B_206,A_207) != k1_xboole_0
      | ~ v1_relat_1(B_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2249,plain,(
    ! [C_388,A_389,B_390] :
      ( ~ r2_hidden(C_388,A_389)
      | ~ r2_hidden(C_388,k1_relat_1(B_390))
      | k9_relat_1(B_390,A_389) != k1_xboole_0
      | ~ v1_relat_1(B_390) ) ),
    inference(resolution,[status(thm)],[c_808,c_2])).

tff(c_2434,plain,(
    ! [A_393,B_394] :
      ( ~ r2_hidden(A_393,k1_relat_1(B_394))
      | k9_relat_1(B_394,k1_tarski(A_393)) != k1_xboole_0
      | ~ v1_relat_1(B_394) ) ),
    inference(resolution,[status(thm)],[c_110,c_2249])).

tff(c_2512,plain,
    ( k9_relat_1('#skF_14',k1_tarski('#skF_13')) != k1_xboole_0
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_688,c_2434])).

tff(c_2542,plain,(
    k9_relat_1('#skF_14',k1_tarski('#skF_13')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2512])).

tff(c_2546,plain,
    ( k11_relat_1('#skF_14','#skF_13') != k1_xboole_0
    | ~ v1_relat_1('#skF_14') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2542])).

tff(c_2549,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_689,c_2546])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:25:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.87/1.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.10/1.73  
% 4.10/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.10/1.73  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_14 > #skF_2 > #skF_13 > #skF_8 > #skF_11 > #skF_3 > #skF_12 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_10
% 4.10/1.73  
% 4.10/1.73  %Foreground sorts:
% 4.10/1.73  
% 4.10/1.73  
% 4.10/1.73  %Background operators:
% 4.10/1.73  
% 4.10/1.73  
% 4.10/1.73  %Foreground operators:
% 4.10/1.73  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.10/1.73  tff('#skF_4', type, '#skF_4': $i > $i).
% 4.10/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.10/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.10/1.73  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.10/1.73  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.10/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.10/1.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.10/1.73  tff('#skF_14', type, '#skF_14': $i).
% 4.10/1.73  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 4.10/1.73  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.10/1.73  tff('#skF_13', type, '#skF_13': $i).
% 4.10/1.73  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.10/1.73  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.10/1.73  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.10/1.73  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 4.10/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.10/1.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.10/1.73  tff('#skF_11', type, '#skF_11': $i > $i).
% 4.10/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.10/1.73  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.10/1.73  tff('#skF_12', type, '#skF_12': $i > $i).
% 4.10/1.73  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 4.10/1.73  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.10/1.73  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 4.10/1.73  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.10/1.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.10/1.73  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 4.10/1.73  
% 4.10/1.75  tff(f_113, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 4.10/1.75  tff(f_77, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 4.10/1.75  tff(f_97, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 4.10/1.75  tff(f_85, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 4.10/1.75  tff(f_105, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_relat_1)).
% 4.10/1.75  tff(f_62, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.10/1.75  tff(f_58, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 4.10/1.75  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.10/1.75  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 4.10/1.75  tff(f_60, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.10/1.75  tff(f_91, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 4.10/1.75  tff(c_66, plain, (v1_relat_1('#skF_14')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.10/1.75  tff(c_74, plain, (r2_hidden('#skF_13', k1_relat_1('#skF_14')) | k11_relat_1('#skF_14', '#skF_13')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.10/1.75  tff(c_111, plain, (k11_relat_1('#skF_14', '#skF_13')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_74])).
% 4.10/1.75  tff(c_42, plain, (![A_19]: (r2_hidden('#skF_4'(A_19), A_19) | v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.10/1.75  tff(c_348, plain, (![A_138, B_139, C_140]: (r2_hidden(k4_tarski(A_138, B_139), C_140) | ~r2_hidden(B_139, k11_relat_1(C_140, A_138)) | ~v1_relat_1(C_140))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.10/1.75  tff(c_46, plain, (![C_52, A_37, D_55]: (r2_hidden(C_52, k1_relat_1(A_37)) | ~r2_hidden(k4_tarski(C_52, D_55), A_37))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.10/1.75  tff(c_357, plain, (![A_141, C_142, B_143]: (r2_hidden(A_141, k1_relat_1(C_142)) | ~r2_hidden(B_143, k11_relat_1(C_142, A_141)) | ~v1_relat_1(C_142))), inference(resolution, [status(thm)], [c_348, c_46])).
% 4.10/1.75  tff(c_381, plain, (![A_144, C_145]: (r2_hidden(A_144, k1_relat_1(C_145)) | ~v1_relat_1(C_145) | v1_relat_1(k11_relat_1(C_145, A_144)))), inference(resolution, [status(thm)], [c_42, c_357])).
% 4.10/1.75  tff(c_68, plain, (k11_relat_1('#skF_14', '#skF_13')=k1_xboole_0 | ~r2_hidden('#skF_13', k1_relat_1('#skF_14'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.10/1.75  tff(c_119, plain, (~r2_hidden('#skF_13', k1_relat_1('#skF_14'))), inference(negUnitSimplification, [status(thm)], [c_111, c_68])).
% 4.10/1.75  tff(c_392, plain, (~v1_relat_1('#skF_14') | v1_relat_1(k11_relat_1('#skF_14', '#skF_13'))), inference(resolution, [status(thm)], [c_381, c_119])).
% 4.10/1.75  tff(c_397, plain, (v1_relat_1(k11_relat_1('#skF_14', '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_392])).
% 4.10/1.75  tff(c_64, plain, (![A_61]: (k1_xboole_0=A_61 | r2_hidden(k4_tarski('#skF_11'(A_61), '#skF_12'(A_61)), A_61) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.10/1.75  tff(c_89, plain, (![A_78, B_79]: (k1_enumset1(A_78, A_78, B_79)=k2_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.10/1.75  tff(c_14, plain, (![E_12, B_7, C_8]: (r2_hidden(E_12, k1_enumset1(E_12, B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.10/1.75  tff(c_101, plain, (![A_78, B_79]: (r2_hidden(A_78, k2_tarski(A_78, B_79)))), inference(superposition, [status(thm), theory('equality')], [c_89, c_14])).
% 4.10/1.75  tff(c_132, plain, (![C_94, A_95, D_96]: (r2_hidden(C_94, k1_relat_1(A_95)) | ~r2_hidden(k4_tarski(C_94, D_96), A_95))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.10/1.75  tff(c_169, plain, (![C_99, D_100, B_101]: (r2_hidden(C_99, k1_relat_1(k2_tarski(k4_tarski(C_99, D_100), B_101))))), inference(resolution, [status(thm)], [c_101, c_132])).
% 4.10/1.75  tff(c_178, plain, (![C_52, D_55, D_100, B_101]: (r2_hidden(C_52, k1_relat_1(k1_relat_1(k2_tarski(k4_tarski(k4_tarski(C_52, D_55), D_100), B_101)))))), inference(resolution, [status(thm)], [c_169, c_46])).
% 4.10/1.75  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.10/1.75  tff(c_554, plain, (![A_162, C_163, B_164]: (r2_hidden(A_162, k1_relat_1(C_163)) | ~v1_relat_1(C_163) | r1_xboole_0(k11_relat_1(C_163, A_162), B_164))), inference(resolution, [status(thm)], [c_6, c_357])).
% 4.10/1.75  tff(c_565, plain, (![B_164]: (~v1_relat_1('#skF_14') | r1_xboole_0(k11_relat_1('#skF_14', '#skF_13'), B_164))), inference(resolution, [status(thm)], [c_554, c_119])).
% 4.10/1.75  tff(c_574, plain, (![B_165]: (r1_xboole_0(k11_relat_1('#skF_14', '#skF_13'), B_165))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_565])).
% 4.10/1.75  tff(c_2, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.10/1.75  tff(c_578, plain, (![C_166, B_167]: (~r2_hidden(C_166, B_167) | ~r2_hidden(C_166, k11_relat_1('#skF_14', '#skF_13')))), inference(resolution, [status(thm)], [c_574, c_2])).
% 4.10/1.75  tff(c_654, plain, (![C_168]: (~r2_hidden(C_168, k11_relat_1('#skF_14', '#skF_13')))), inference(resolution, [status(thm)], [c_178, c_578])).
% 4.10/1.75  tff(c_666, plain, (k11_relat_1('#skF_14', '#skF_13')=k1_xboole_0 | ~v1_relat_1(k11_relat_1('#skF_14', '#skF_13'))), inference(resolution, [status(thm)], [c_64, c_654])).
% 4.10/1.75  tff(c_685, plain, (k11_relat_1('#skF_14', '#skF_13')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_397, c_666])).
% 4.10/1.75  tff(c_687, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111, c_685])).
% 4.10/1.75  tff(c_689, plain, (k11_relat_1('#skF_14', '#skF_13')=k1_xboole_0), inference(splitRight, [status(thm)], [c_74])).
% 4.10/1.75  tff(c_36, plain, (![A_16, B_18]: (k9_relat_1(A_16, k1_tarski(B_18))=k11_relat_1(A_16, B_18) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.10/1.75  tff(c_688, plain, (r2_hidden('#skF_13', k1_relat_1('#skF_14'))), inference(splitRight, [status(thm)], [c_74])).
% 4.10/1.75  tff(c_32, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.10/1.75  tff(c_10, plain, (![E_12, A_6, B_7]: (r2_hidden(E_12, k1_enumset1(A_6, B_7, E_12)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.10/1.75  tff(c_107, plain, (![B_80, A_81]: (r2_hidden(B_80, k2_tarski(A_81, B_80)))), inference(superposition, [status(thm), theory('equality')], [c_89, c_10])).
% 4.10/1.75  tff(c_110, plain, (![A_13]: (r2_hidden(A_13, k1_tarski(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_107])).
% 4.10/1.75  tff(c_808, plain, (![B_206, A_207]: (r1_xboole_0(k1_relat_1(B_206), A_207) | k9_relat_1(B_206, A_207)!=k1_xboole_0 | ~v1_relat_1(B_206))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.10/1.75  tff(c_2249, plain, (![C_388, A_389, B_390]: (~r2_hidden(C_388, A_389) | ~r2_hidden(C_388, k1_relat_1(B_390)) | k9_relat_1(B_390, A_389)!=k1_xboole_0 | ~v1_relat_1(B_390))), inference(resolution, [status(thm)], [c_808, c_2])).
% 4.10/1.75  tff(c_2434, plain, (![A_393, B_394]: (~r2_hidden(A_393, k1_relat_1(B_394)) | k9_relat_1(B_394, k1_tarski(A_393))!=k1_xboole_0 | ~v1_relat_1(B_394))), inference(resolution, [status(thm)], [c_110, c_2249])).
% 4.10/1.75  tff(c_2512, plain, (k9_relat_1('#skF_14', k1_tarski('#skF_13'))!=k1_xboole_0 | ~v1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_688, c_2434])).
% 4.10/1.75  tff(c_2542, plain, (k9_relat_1('#skF_14', k1_tarski('#skF_13'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2512])).
% 4.10/1.75  tff(c_2546, plain, (k11_relat_1('#skF_14', '#skF_13')!=k1_xboole_0 | ~v1_relat_1('#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_36, c_2542])).
% 4.10/1.75  tff(c_2549, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_689, c_2546])).
% 4.10/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.10/1.75  
% 4.10/1.75  Inference rules
% 4.10/1.75  ----------------------
% 4.10/1.75  #Ref     : 1
% 4.10/1.75  #Sup     : 559
% 4.10/1.75  #Fact    : 0
% 4.10/1.75  #Define  : 0
% 4.10/1.75  #Split   : 1
% 4.10/1.75  #Chain   : 0
% 4.10/1.75  #Close   : 0
% 4.10/1.75  
% 4.10/1.75  Ordering : KBO
% 4.10/1.75  
% 4.10/1.75  Simplification rules
% 4.10/1.75  ----------------------
% 4.10/1.75  #Subsume      : 48
% 4.10/1.75  #Demod        : 63
% 4.10/1.75  #Tautology    : 126
% 4.10/1.75  #SimpNegUnit  : 2
% 4.10/1.75  #BackRed      : 0
% 4.10/1.75  
% 4.10/1.75  #Partial instantiations: 0
% 4.10/1.75  #Strategies tried      : 1
% 4.10/1.75  
% 4.10/1.75  Timing (in seconds)
% 4.10/1.75  ----------------------
% 4.17/1.75  Preprocessing        : 0.31
% 4.17/1.75  Parsing              : 0.15
% 4.17/1.75  CNF conversion       : 0.03
% 4.17/1.75  Main loop            : 0.64
% 4.17/1.75  Inferencing          : 0.24
% 4.17/1.75  Reduction            : 0.19
% 4.17/1.75  Demodulation         : 0.15
% 4.17/1.75  BG Simplification    : 0.03
% 4.17/1.75  Subsumption          : 0.12
% 4.17/1.75  Abstraction          : 0.04
% 4.17/1.75  MUC search           : 0.00
% 4.17/1.75  Cooper               : 0.00
% 4.17/1.75  Total                : 0.98
% 4.17/1.75  Index Insertion      : 0.00
% 4.17/1.75  Index Deletion       : 0.00
% 4.17/1.75  Index Matching       : 0.00
% 4.17/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
