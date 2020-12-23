%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:52 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 119 expanded)
%              Number of leaves         :   40 (  58 expanded)
%              Depth                    :   14
%              Number of atoms          :  128 ( 218 expanded)
%              Number of equality atoms :   59 ( 110 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_119,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_96,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_100,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_47,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_60,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_107,plain,(
    ! [A_54] :
      ( k2_relat_1(A_54) = k1_xboole_0
      | k1_relat_1(A_54) != k1_xboole_0
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_116,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_107])).

tff(c_117,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_118,plain,(
    ! [A_55] :
      ( k1_relat_1(A_55) = k1_xboole_0
      | k2_relat_1(A_55) != k1_xboole_0
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_127,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_118])).

tff(c_128,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_127])).

tff(c_26,plain,(
    ! [A_25,B_26] :
      ( r2_hidden('#skF_1'(A_25,B_26),A_25)
      | k1_xboole_0 = A_25
      | k1_tarski(B_26) = A_25 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_58,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    ! [A_31] : v1_relat_1(k6_relat_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_46,plain,(
    ! [A_42] : k2_relat_1(k6_relat_1(A_42)) = A_42 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_257,plain,(
    ! [B_105,A_106] :
      ( k2_relat_1(k5_relat_1(B_105,A_106)) = k2_relat_1(A_106)
      | ~ r1_tarski(k1_relat_1(A_106),k2_relat_1(B_105))
      | ~ v1_relat_1(B_105)
      | ~ v1_relat_1(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_263,plain,(
    ! [A_42,A_106] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_42),A_106)) = k2_relat_1(A_106)
      | ~ r1_tarski(k1_relat_1(A_106),A_42)
      | ~ v1_relat_1(k6_relat_1(A_42))
      | ~ v1_relat_1(A_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_257])).

tff(c_421,plain,(
    ! [A_119,A_120] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_119),A_120)) = k2_relat_1(A_120)
      | ~ r1_tarski(k1_relat_1(A_120),A_119)
      | ~ v1_relat_1(A_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_263])).

tff(c_178,plain,(
    ! [B_75,A_76] :
      ( k9_relat_1(B_75,k2_relat_1(A_76)) = k2_relat_1(k5_relat_1(A_76,B_75))
      | ~ v1_relat_1(B_75)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_187,plain,(
    ! [A_42,B_75] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_42),B_75)) = k9_relat_1(B_75,A_42)
      | ~ v1_relat_1(B_75)
      | ~ v1_relat_1(k6_relat_1(A_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_178])).

tff(c_191,plain,(
    ! [A_42,B_75] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_42),B_75)) = k9_relat_1(B_75,A_42)
      | ~ v1_relat_1(B_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_187])).

tff(c_454,plain,(
    ! [A_121,A_122] :
      ( k9_relat_1(A_121,A_122) = k2_relat_1(A_121)
      | ~ v1_relat_1(A_121)
      | ~ r1_tarski(k1_relat_1(A_121),A_122)
      | ~ v1_relat_1(A_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_421,c_191])).

tff(c_465,plain,(
    ! [A_123] :
      ( k9_relat_1(A_123,k1_relat_1(A_123)) = k2_relat_1(A_123)
      | ~ v1_relat_1(A_123) ) ),
    inference(resolution,[status(thm)],[c_8,c_454])).

tff(c_56,plain,(
    k1_tarski('#skF_2') = k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_136,plain,(
    ! [A_58,B_59] :
      ( k9_relat_1(A_58,k1_tarski(B_59)) = k11_relat_1(A_58,B_59)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_145,plain,(
    ! [A_58] :
      ( k9_relat_1(A_58,k1_relat_1('#skF_3')) = k11_relat_1(A_58,'#skF_2')
      | ~ v1_relat_1(A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_136])).

tff(c_476,plain,
    ( k11_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_145])).

tff(c_495,plain,(
    k11_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_60,c_476])).

tff(c_34,plain,(
    ! [A_35,B_36,C_37] :
      ( r2_hidden(k4_tarski(A_35,B_36),C_37)
      | ~ r2_hidden(B_36,k11_relat_1(C_37,A_35))
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_223,plain,(
    ! [C_90,A_91,B_92] :
      ( k1_funct_1(C_90,A_91) = B_92
      | ~ r2_hidden(k4_tarski(A_91,B_92),C_90)
      | ~ v1_funct_1(C_90)
      | ~ v1_relat_1(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_227,plain,(
    ! [C_37,A_35,B_36] :
      ( k1_funct_1(C_37,A_35) = B_36
      | ~ v1_funct_1(C_37)
      | ~ r2_hidden(B_36,k11_relat_1(C_37,A_35))
      | ~ v1_relat_1(C_37) ) ),
    inference(resolution,[status(thm)],[c_34,c_223])).

tff(c_506,plain,(
    ! [B_36] :
      ( k1_funct_1('#skF_3','#skF_2') = B_36
      | ~ v1_funct_1('#skF_3')
      | ~ r2_hidden(B_36,k2_relat_1('#skF_3'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_495,c_227])).

tff(c_622,plain,(
    ! [B_128] :
      ( k1_funct_1('#skF_3','#skF_2') = B_128
      | ~ r2_hidden(B_128,k2_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_506])).

tff(c_634,plain,(
    ! [B_26] :
      ( '#skF_1'(k2_relat_1('#skF_3'),B_26) = k1_funct_1('#skF_3','#skF_2')
      | k2_relat_1('#skF_3') = k1_xboole_0
      | k2_relat_1('#skF_3') = k1_tarski(B_26) ) ),
    inference(resolution,[status(thm)],[c_26,c_622])).

tff(c_773,plain,(
    ! [B_131] :
      ( '#skF_1'(k2_relat_1('#skF_3'),B_131) = k1_funct_1('#skF_3','#skF_2')
      | k2_relat_1('#skF_3') = k1_tarski(B_131) ) ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_634])).

tff(c_24,plain,(
    ! [A_25,B_26] :
      ( '#skF_1'(A_25,B_26) != B_26
      | k1_xboole_0 = A_25
      | k1_tarski(B_26) = A_25 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_781,plain,(
    ! [B_131] :
      ( k1_funct_1('#skF_3','#skF_2') != B_131
      | k2_relat_1('#skF_3') = k1_xboole_0
      | k2_relat_1('#skF_3') = k1_tarski(B_131)
      | k2_relat_1('#skF_3') = k1_tarski(B_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_773,c_24])).

tff(c_790,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) = k2_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_781])).

tff(c_54,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) != k2_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_793,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_54])).

tff(c_795,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_22,plain,(
    ! [A_24] : ~ v1_xboole_0(k1_tarski(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_67,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_22])).

tff(c_801,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_795,c_67])).

tff(c_805,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_801])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:15:17 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.51  
% 2.87/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.51  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.87/1.51  
% 2.87/1.51  %Foreground sorts:
% 2.87/1.51  
% 2.87/1.51  
% 2.87/1.51  %Background operators:
% 2.87/1.51  
% 2.87/1.51  
% 2.87/1.51  %Foreground operators:
% 2.87/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.87/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.87/1.51  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.87/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.87/1.51  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.87/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.87/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.87/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.87/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.87/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.87/1.51  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.87/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.87/1.51  tff('#skF_2', type, '#skF_2': $i).
% 2.87/1.51  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.87/1.51  tff('#skF_3', type, '#skF_3': $i).
% 2.87/1.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.87/1.51  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.87/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.87/1.51  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.87/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.87/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.87/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.87/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.87/1.51  
% 2.98/1.52  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.98/1.52  tff(f_119, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 2.98/1.52  tff(f_96, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 2.98/1.52  tff(f_61, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 2.98/1.52  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.98/1.52  tff(f_68, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.98/1.52  tff(f_100, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.98/1.52  tff(f_90, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 2.98/1.52  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 2.98/1.52  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 2.98/1.52  tff(f_81, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 2.98/1.52  tff(f_110, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.98/1.52  tff(f_47, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.98/1.52  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.98/1.52  tff(c_60, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.98/1.52  tff(c_107, plain, (![A_54]: (k2_relat_1(A_54)=k1_xboole_0 | k1_relat_1(A_54)!=k1_xboole_0 | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.98/1.52  tff(c_116, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_60, c_107])).
% 2.98/1.52  tff(c_117, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_116])).
% 2.98/1.52  tff(c_118, plain, (![A_55]: (k1_relat_1(A_55)=k1_xboole_0 | k2_relat_1(A_55)!=k1_xboole_0 | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.98/1.52  tff(c_127, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_60, c_118])).
% 2.98/1.52  tff(c_128, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_117, c_127])).
% 2.98/1.52  tff(c_26, plain, (![A_25, B_26]: (r2_hidden('#skF_1'(A_25, B_26), A_25) | k1_xboole_0=A_25 | k1_tarski(B_26)=A_25)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.98/1.52  tff(c_58, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.98/1.52  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.98/1.52  tff(c_30, plain, (![A_31]: (v1_relat_1(k6_relat_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.98/1.52  tff(c_46, plain, (![A_42]: (k2_relat_1(k6_relat_1(A_42))=A_42)), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.98/1.52  tff(c_257, plain, (![B_105, A_106]: (k2_relat_1(k5_relat_1(B_105, A_106))=k2_relat_1(A_106) | ~r1_tarski(k1_relat_1(A_106), k2_relat_1(B_105)) | ~v1_relat_1(B_105) | ~v1_relat_1(A_106))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.98/1.52  tff(c_263, plain, (![A_42, A_106]: (k2_relat_1(k5_relat_1(k6_relat_1(A_42), A_106))=k2_relat_1(A_106) | ~r1_tarski(k1_relat_1(A_106), A_42) | ~v1_relat_1(k6_relat_1(A_42)) | ~v1_relat_1(A_106))), inference(superposition, [status(thm), theory('equality')], [c_46, c_257])).
% 2.98/1.52  tff(c_421, plain, (![A_119, A_120]: (k2_relat_1(k5_relat_1(k6_relat_1(A_119), A_120))=k2_relat_1(A_120) | ~r1_tarski(k1_relat_1(A_120), A_119) | ~v1_relat_1(A_120))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_263])).
% 2.98/1.52  tff(c_178, plain, (![B_75, A_76]: (k9_relat_1(B_75, k2_relat_1(A_76))=k2_relat_1(k5_relat_1(A_76, B_75)) | ~v1_relat_1(B_75) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.98/1.52  tff(c_187, plain, (![A_42, B_75]: (k2_relat_1(k5_relat_1(k6_relat_1(A_42), B_75))=k9_relat_1(B_75, A_42) | ~v1_relat_1(B_75) | ~v1_relat_1(k6_relat_1(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_178])).
% 2.98/1.52  tff(c_191, plain, (![A_42, B_75]: (k2_relat_1(k5_relat_1(k6_relat_1(A_42), B_75))=k9_relat_1(B_75, A_42) | ~v1_relat_1(B_75))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_187])).
% 2.98/1.52  tff(c_454, plain, (![A_121, A_122]: (k9_relat_1(A_121, A_122)=k2_relat_1(A_121) | ~v1_relat_1(A_121) | ~r1_tarski(k1_relat_1(A_121), A_122) | ~v1_relat_1(A_121))), inference(superposition, [status(thm), theory('equality')], [c_421, c_191])).
% 2.98/1.52  tff(c_465, plain, (![A_123]: (k9_relat_1(A_123, k1_relat_1(A_123))=k2_relat_1(A_123) | ~v1_relat_1(A_123))), inference(resolution, [status(thm)], [c_8, c_454])).
% 2.98/1.52  tff(c_56, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.98/1.52  tff(c_136, plain, (![A_58, B_59]: (k9_relat_1(A_58, k1_tarski(B_59))=k11_relat_1(A_58, B_59) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.98/1.52  tff(c_145, plain, (![A_58]: (k9_relat_1(A_58, k1_relat_1('#skF_3'))=k11_relat_1(A_58, '#skF_2') | ~v1_relat_1(A_58))), inference(superposition, [status(thm), theory('equality')], [c_56, c_136])).
% 2.98/1.52  tff(c_476, plain, (k11_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_465, c_145])).
% 2.98/1.52  tff(c_495, plain, (k11_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_60, c_476])).
% 2.98/1.52  tff(c_34, plain, (![A_35, B_36, C_37]: (r2_hidden(k4_tarski(A_35, B_36), C_37) | ~r2_hidden(B_36, k11_relat_1(C_37, A_35)) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.98/1.52  tff(c_223, plain, (![C_90, A_91, B_92]: (k1_funct_1(C_90, A_91)=B_92 | ~r2_hidden(k4_tarski(A_91, B_92), C_90) | ~v1_funct_1(C_90) | ~v1_relat_1(C_90))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.98/1.52  tff(c_227, plain, (![C_37, A_35, B_36]: (k1_funct_1(C_37, A_35)=B_36 | ~v1_funct_1(C_37) | ~r2_hidden(B_36, k11_relat_1(C_37, A_35)) | ~v1_relat_1(C_37))), inference(resolution, [status(thm)], [c_34, c_223])).
% 2.98/1.52  tff(c_506, plain, (![B_36]: (k1_funct_1('#skF_3', '#skF_2')=B_36 | ~v1_funct_1('#skF_3') | ~r2_hidden(B_36, k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_495, c_227])).
% 2.98/1.52  tff(c_622, plain, (![B_128]: (k1_funct_1('#skF_3', '#skF_2')=B_128 | ~r2_hidden(B_128, k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_506])).
% 2.98/1.52  tff(c_634, plain, (![B_26]: ('#skF_1'(k2_relat_1('#skF_3'), B_26)=k1_funct_1('#skF_3', '#skF_2') | k2_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')=k1_tarski(B_26))), inference(resolution, [status(thm)], [c_26, c_622])).
% 2.98/1.52  tff(c_773, plain, (![B_131]: ('#skF_1'(k2_relat_1('#skF_3'), B_131)=k1_funct_1('#skF_3', '#skF_2') | k2_relat_1('#skF_3')=k1_tarski(B_131))), inference(negUnitSimplification, [status(thm)], [c_128, c_634])).
% 2.98/1.52  tff(c_24, plain, (![A_25, B_26]: ('#skF_1'(A_25, B_26)!=B_26 | k1_xboole_0=A_25 | k1_tarski(B_26)=A_25)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.98/1.52  tff(c_781, plain, (![B_131]: (k1_funct_1('#skF_3', '#skF_2')!=B_131 | k2_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')=k1_tarski(B_131) | k2_relat_1('#skF_3')=k1_tarski(B_131))), inference(superposition, [status(thm), theory('equality')], [c_773, c_24])).
% 2.98/1.52  tff(c_790, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))=k2_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_128, c_781])).
% 2.98/1.52  tff(c_54, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))!=k2_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.98/1.52  tff(c_793, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_790, c_54])).
% 2.98/1.52  tff(c_795, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_116])).
% 2.98/1.52  tff(c_22, plain, (![A_24]: (~v1_xboole_0(k1_tarski(A_24)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.98/1.52  tff(c_67, plain, (~v1_xboole_0(k1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_22])).
% 2.98/1.52  tff(c_801, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_795, c_67])).
% 2.98/1.52  tff(c_805, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_801])).
% 2.98/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.52  
% 2.98/1.52  Inference rules
% 2.98/1.52  ----------------------
% 2.98/1.52  #Ref     : 0
% 2.98/1.52  #Sup     : 153
% 2.98/1.52  #Fact    : 0
% 2.98/1.52  #Define  : 0
% 2.98/1.52  #Split   : 3
% 2.98/1.52  #Chain   : 0
% 2.98/1.52  #Close   : 0
% 2.98/1.52  
% 2.98/1.52  Ordering : KBO
% 2.98/1.52  
% 2.98/1.52  Simplification rules
% 2.98/1.52  ----------------------
% 2.98/1.52  #Subsume      : 12
% 2.98/1.52  #Demod        : 139
% 2.98/1.52  #Tautology    : 85
% 2.98/1.52  #SimpNegUnit  : 5
% 2.98/1.52  #BackRed      : 5
% 2.98/1.52  
% 2.98/1.52  #Partial instantiations: 0
% 2.98/1.52  #Strategies tried      : 1
% 2.98/1.52  
% 2.98/1.52  Timing (in seconds)
% 2.98/1.52  ----------------------
% 2.98/1.53  Preprocessing        : 0.35
% 2.98/1.53  Parsing              : 0.19
% 2.98/1.53  CNF conversion       : 0.02
% 2.98/1.53  Main loop            : 0.31
% 2.98/1.53  Inferencing          : 0.12
% 2.98/1.53  Reduction            : 0.10
% 2.98/1.53  Demodulation         : 0.07
% 2.98/1.53  BG Simplification    : 0.02
% 2.98/1.53  Subsumption          : 0.04
% 2.98/1.53  Abstraction          : 0.02
% 2.98/1.53  MUC search           : 0.00
% 2.98/1.53  Cooper               : 0.00
% 2.98/1.53  Total                : 0.70
% 2.98/1.53  Index Insertion      : 0.00
% 2.98/1.53  Index Deletion       : 0.00
% 2.98/1.53  Index Matching       : 0.00
% 2.98/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
