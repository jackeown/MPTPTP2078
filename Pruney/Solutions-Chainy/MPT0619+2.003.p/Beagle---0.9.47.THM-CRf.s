%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:52 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 107 expanded)
%              Number of leaves         :   42 (  55 expanded)
%              Depth                    :   15
%              Number of atoms          :  123 ( 191 expanded)
%              Number of equality atoms :   55 (  92 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_120,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_93,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_101,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_68,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_97,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_47,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_62,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_109,plain,(
    ! [A_55] :
      ( k1_relat_1(A_55) = k1_xboole_0
      | k2_relat_1(A_55) != k1_xboole_0
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_118,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_62,c_109])).

tff(c_119,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_26,plain,(
    ! [A_25,B_26] :
      ( r2_hidden('#skF_1'(A_25,B_26),A_25)
      | k1_xboole_0 = A_25
      | k1_tarski(B_26) = A_25 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_60,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_48,plain,(
    ! [A_42,B_43] :
      ( k5_relat_1(k6_relat_1(A_42),B_43) = k7_relat_1(B_43,A_42)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_30,plain,(
    ! [A_31] : v1_relat_1(k6_relat_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_46,plain,(
    ! [A_41] : k2_relat_1(k6_relat_1(A_41)) = A_41 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_242,plain,(
    ! [B_100,A_101] :
      ( k2_relat_1(k5_relat_1(B_100,A_101)) = k2_relat_1(A_101)
      | ~ r1_tarski(k1_relat_1(A_101),k2_relat_1(B_100))
      | ~ v1_relat_1(B_100)
      | ~ v1_relat_1(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_248,plain,(
    ! [A_41,A_101] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_41),A_101)) = k2_relat_1(A_101)
      | ~ r1_tarski(k1_relat_1(A_101),A_41)
      | ~ v1_relat_1(k6_relat_1(A_41))
      | ~ v1_relat_1(A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_242])).

tff(c_418,plain,(
    ! [A_122,A_123] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_122),A_123)) = k2_relat_1(A_123)
      | ~ r1_tarski(k1_relat_1(A_123),A_122)
      | ~ v1_relat_1(A_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_248])).

tff(c_445,plain,(
    ! [B_124,A_125] :
      ( k2_relat_1(k7_relat_1(B_124,A_125)) = k2_relat_1(B_124)
      | ~ r1_tarski(k1_relat_1(B_124),A_125)
      | ~ v1_relat_1(B_124)
      | ~ v1_relat_1(B_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_418])).

tff(c_456,plain,(
    ! [B_126] :
      ( k2_relat_1(k7_relat_1(B_126,k1_relat_1(B_126))) = k2_relat_1(B_126)
      | ~ v1_relat_1(B_126) ) ),
    inference(resolution,[status(thm)],[c_8,c_445])).

tff(c_32,plain,(
    ! [B_33,A_32] :
      ( k2_relat_1(k7_relat_1(B_33,A_32)) = k9_relat_1(B_33,A_32)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_594,plain,(
    ! [B_131] :
      ( k9_relat_1(B_131,k1_relat_1(B_131)) = k2_relat_1(B_131)
      | ~ v1_relat_1(B_131)
      | ~ v1_relat_1(B_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_456,c_32])).

tff(c_58,plain,(
    k1_tarski('#skF_2') = k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_157,plain,(
    ! [A_66,B_67] :
      ( k9_relat_1(A_66,k1_tarski(B_67)) = k11_relat_1(A_66,B_67)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_166,plain,(
    ! [A_66] :
      ( k9_relat_1(A_66,k1_relat_1('#skF_3')) = k11_relat_1(A_66,'#skF_2')
      | ~ v1_relat_1(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_157])).

tff(c_605,plain,
    ( k11_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_594,c_166])).

tff(c_624,plain,(
    k11_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_62,c_62,c_605])).

tff(c_34,plain,(
    ! [A_34,B_35,C_36] :
      ( r2_hidden(k4_tarski(A_34,B_35),C_36)
      | ~ r2_hidden(B_35,k11_relat_1(C_36,A_34))
      | ~ v1_relat_1(C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_203,plain,(
    ! [C_83,A_84,B_85] :
      ( k1_funct_1(C_83,A_84) = B_85
      | ~ r2_hidden(k4_tarski(A_84,B_85),C_83)
      | ~ v1_funct_1(C_83)
      | ~ v1_relat_1(C_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_207,plain,(
    ! [C_36,A_34,B_35] :
      ( k1_funct_1(C_36,A_34) = B_35
      | ~ v1_funct_1(C_36)
      | ~ r2_hidden(B_35,k11_relat_1(C_36,A_34))
      | ~ v1_relat_1(C_36) ) ),
    inference(resolution,[status(thm)],[c_34,c_203])).

tff(c_640,plain,(
    ! [B_35] :
      ( k1_funct_1('#skF_3','#skF_2') = B_35
      | ~ v1_funct_1('#skF_3')
      | ~ r2_hidden(B_35,k2_relat_1('#skF_3'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_624,c_207])).

tff(c_699,plain,(
    ! [B_136] :
      ( k1_funct_1('#skF_3','#skF_2') = B_136
      | ~ r2_hidden(B_136,k2_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_640])).

tff(c_711,plain,(
    ! [B_26] :
      ( '#skF_1'(k2_relat_1('#skF_3'),B_26) = k1_funct_1('#skF_3','#skF_2')
      | k2_relat_1('#skF_3') = k1_xboole_0
      | k2_relat_1('#skF_3') = k1_tarski(B_26) ) ),
    inference(resolution,[status(thm)],[c_26,c_699])).

tff(c_717,plain,(
    ! [B_137] :
      ( '#skF_1'(k2_relat_1('#skF_3'),B_137) = k1_funct_1('#skF_3','#skF_2')
      | k2_relat_1('#skF_3') = k1_tarski(B_137) ) ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_711])).

tff(c_24,plain,(
    ! [A_25,B_26] :
      ( '#skF_1'(A_25,B_26) != B_26
      | k1_xboole_0 = A_25
      | k1_tarski(B_26) = A_25 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_725,plain,(
    ! [B_137] :
      ( k1_funct_1('#skF_3','#skF_2') != B_137
      | k2_relat_1('#skF_3') = k1_xboole_0
      | k2_relat_1('#skF_3') = k1_tarski(B_137)
      | k2_relat_1('#skF_3') = k1_tarski(B_137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_717,c_24])).

tff(c_740,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) = k2_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_725])).

tff(c_56,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) != k2_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_743,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_740,c_56])).

tff(c_744,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_22,plain,(
    ! [A_24] : ~ v1_xboole_0(k1_tarski(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_69,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_22])).

tff(c_746,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_744,c_69])).

tff(c_750,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_746])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:42:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.40  
% 2.78/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.40  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.78/1.40  
% 2.78/1.40  %Foreground sorts:
% 2.78/1.40  
% 2.78/1.40  
% 2.78/1.40  %Background operators:
% 2.78/1.40  
% 2.78/1.40  
% 2.78/1.40  %Foreground operators:
% 2.78/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.78/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.78/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.78/1.40  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.78/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.78/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.78/1.40  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.78/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.78/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.78/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.78/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.78/1.40  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.78/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.78/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.78/1.40  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.78/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.78/1.40  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.78/1.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.78/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.78/1.40  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.78/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.78/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.78/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.78/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.78/1.40  
% 2.78/1.42  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.78/1.42  tff(f_120, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 2.78/1.42  tff(f_93, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 2.78/1.42  tff(f_61, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 2.78/1.42  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.78/1.42  tff(f_101, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.78/1.42  tff(f_68, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.78/1.42  tff(f_97, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.78/1.42  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 2.78/1.42  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.78/1.42  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 2.78/1.42  tff(f_78, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 2.78/1.42  tff(f_111, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.78/1.42  tff(f_47, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.78/1.42  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.78/1.42  tff(c_62, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.78/1.42  tff(c_109, plain, (![A_55]: (k1_relat_1(A_55)=k1_xboole_0 | k2_relat_1(A_55)!=k1_xboole_0 | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.78/1.42  tff(c_118, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_62, c_109])).
% 2.78/1.42  tff(c_119, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_118])).
% 2.78/1.42  tff(c_26, plain, (![A_25, B_26]: (r2_hidden('#skF_1'(A_25, B_26), A_25) | k1_xboole_0=A_25 | k1_tarski(B_26)=A_25)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.78/1.42  tff(c_60, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.78/1.42  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.78/1.42  tff(c_48, plain, (![A_42, B_43]: (k5_relat_1(k6_relat_1(A_42), B_43)=k7_relat_1(B_43, A_42) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.78/1.42  tff(c_30, plain, (![A_31]: (v1_relat_1(k6_relat_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.78/1.42  tff(c_46, plain, (![A_41]: (k2_relat_1(k6_relat_1(A_41))=A_41)), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.78/1.42  tff(c_242, plain, (![B_100, A_101]: (k2_relat_1(k5_relat_1(B_100, A_101))=k2_relat_1(A_101) | ~r1_tarski(k1_relat_1(A_101), k2_relat_1(B_100)) | ~v1_relat_1(B_100) | ~v1_relat_1(A_101))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.78/1.42  tff(c_248, plain, (![A_41, A_101]: (k2_relat_1(k5_relat_1(k6_relat_1(A_41), A_101))=k2_relat_1(A_101) | ~r1_tarski(k1_relat_1(A_101), A_41) | ~v1_relat_1(k6_relat_1(A_41)) | ~v1_relat_1(A_101))), inference(superposition, [status(thm), theory('equality')], [c_46, c_242])).
% 2.78/1.42  tff(c_418, plain, (![A_122, A_123]: (k2_relat_1(k5_relat_1(k6_relat_1(A_122), A_123))=k2_relat_1(A_123) | ~r1_tarski(k1_relat_1(A_123), A_122) | ~v1_relat_1(A_123))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_248])).
% 2.78/1.42  tff(c_445, plain, (![B_124, A_125]: (k2_relat_1(k7_relat_1(B_124, A_125))=k2_relat_1(B_124) | ~r1_tarski(k1_relat_1(B_124), A_125) | ~v1_relat_1(B_124) | ~v1_relat_1(B_124))), inference(superposition, [status(thm), theory('equality')], [c_48, c_418])).
% 2.78/1.42  tff(c_456, plain, (![B_126]: (k2_relat_1(k7_relat_1(B_126, k1_relat_1(B_126)))=k2_relat_1(B_126) | ~v1_relat_1(B_126))), inference(resolution, [status(thm)], [c_8, c_445])).
% 2.78/1.42  tff(c_32, plain, (![B_33, A_32]: (k2_relat_1(k7_relat_1(B_33, A_32))=k9_relat_1(B_33, A_32) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.78/1.42  tff(c_594, plain, (![B_131]: (k9_relat_1(B_131, k1_relat_1(B_131))=k2_relat_1(B_131) | ~v1_relat_1(B_131) | ~v1_relat_1(B_131))), inference(superposition, [status(thm), theory('equality')], [c_456, c_32])).
% 2.78/1.42  tff(c_58, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.78/1.42  tff(c_157, plain, (![A_66, B_67]: (k9_relat_1(A_66, k1_tarski(B_67))=k11_relat_1(A_66, B_67) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.78/1.42  tff(c_166, plain, (![A_66]: (k9_relat_1(A_66, k1_relat_1('#skF_3'))=k11_relat_1(A_66, '#skF_2') | ~v1_relat_1(A_66))), inference(superposition, [status(thm), theory('equality')], [c_58, c_157])).
% 2.78/1.42  tff(c_605, plain, (k11_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_594, c_166])).
% 2.78/1.42  tff(c_624, plain, (k11_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_62, c_62, c_605])).
% 2.78/1.42  tff(c_34, plain, (![A_34, B_35, C_36]: (r2_hidden(k4_tarski(A_34, B_35), C_36) | ~r2_hidden(B_35, k11_relat_1(C_36, A_34)) | ~v1_relat_1(C_36))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.78/1.42  tff(c_203, plain, (![C_83, A_84, B_85]: (k1_funct_1(C_83, A_84)=B_85 | ~r2_hidden(k4_tarski(A_84, B_85), C_83) | ~v1_funct_1(C_83) | ~v1_relat_1(C_83))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.78/1.42  tff(c_207, plain, (![C_36, A_34, B_35]: (k1_funct_1(C_36, A_34)=B_35 | ~v1_funct_1(C_36) | ~r2_hidden(B_35, k11_relat_1(C_36, A_34)) | ~v1_relat_1(C_36))), inference(resolution, [status(thm)], [c_34, c_203])).
% 2.78/1.42  tff(c_640, plain, (![B_35]: (k1_funct_1('#skF_3', '#skF_2')=B_35 | ~v1_funct_1('#skF_3') | ~r2_hidden(B_35, k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_624, c_207])).
% 2.78/1.42  tff(c_699, plain, (![B_136]: (k1_funct_1('#skF_3', '#skF_2')=B_136 | ~r2_hidden(B_136, k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_640])).
% 2.78/1.42  tff(c_711, plain, (![B_26]: ('#skF_1'(k2_relat_1('#skF_3'), B_26)=k1_funct_1('#skF_3', '#skF_2') | k2_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')=k1_tarski(B_26))), inference(resolution, [status(thm)], [c_26, c_699])).
% 2.78/1.42  tff(c_717, plain, (![B_137]: ('#skF_1'(k2_relat_1('#skF_3'), B_137)=k1_funct_1('#skF_3', '#skF_2') | k2_relat_1('#skF_3')=k1_tarski(B_137))), inference(negUnitSimplification, [status(thm)], [c_119, c_711])).
% 2.78/1.42  tff(c_24, plain, (![A_25, B_26]: ('#skF_1'(A_25, B_26)!=B_26 | k1_xboole_0=A_25 | k1_tarski(B_26)=A_25)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.78/1.42  tff(c_725, plain, (![B_137]: (k1_funct_1('#skF_3', '#skF_2')!=B_137 | k2_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')=k1_tarski(B_137) | k2_relat_1('#skF_3')=k1_tarski(B_137))), inference(superposition, [status(thm), theory('equality')], [c_717, c_24])).
% 2.78/1.42  tff(c_740, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))=k2_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_119, c_725])).
% 2.78/1.42  tff(c_56, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))!=k2_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.78/1.42  tff(c_743, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_740, c_56])).
% 2.78/1.42  tff(c_744, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_118])).
% 2.78/1.42  tff(c_22, plain, (![A_24]: (~v1_xboole_0(k1_tarski(A_24)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.78/1.42  tff(c_69, plain, (~v1_xboole_0(k1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_22])).
% 2.78/1.42  tff(c_746, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_744, c_69])).
% 2.78/1.42  tff(c_750, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_746])).
% 2.78/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.42  
% 2.78/1.42  Inference rules
% 2.78/1.42  ----------------------
% 2.78/1.42  #Ref     : 0
% 2.78/1.42  #Sup     : 140
% 2.78/1.42  #Fact    : 0
% 2.78/1.42  #Define  : 0
% 2.78/1.42  #Split   : 4
% 2.78/1.42  #Chain   : 0
% 2.78/1.42  #Close   : 0
% 2.78/1.42  
% 2.78/1.42  Ordering : KBO
% 2.78/1.42  
% 2.78/1.42  Simplification rules
% 2.78/1.42  ----------------------
% 2.78/1.42  #Subsume      : 9
% 2.78/1.42  #Demod        : 107
% 2.78/1.42  #Tautology    : 78
% 2.78/1.42  #SimpNegUnit  : 5
% 2.78/1.42  #BackRed      : 4
% 2.78/1.42  
% 2.78/1.42  #Partial instantiations: 0
% 2.78/1.42  #Strategies tried      : 1
% 2.78/1.42  
% 2.78/1.42  Timing (in seconds)
% 2.78/1.42  ----------------------
% 2.78/1.42  Preprocessing        : 0.33
% 2.78/1.42  Parsing              : 0.17
% 2.78/1.42  CNF conversion       : 0.02
% 2.78/1.42  Main loop            : 0.32
% 2.78/1.42  Inferencing          : 0.12
% 2.78/1.42  Reduction            : 0.10
% 2.78/1.42  Demodulation         : 0.07
% 2.78/1.42  BG Simplification    : 0.02
% 2.78/1.42  Subsumption          : 0.05
% 2.78/1.42  Abstraction          : 0.02
% 2.78/1.42  MUC search           : 0.00
% 2.78/1.42  Cooper               : 0.00
% 2.78/1.42  Total                : 0.68
% 2.78/1.42  Index Insertion      : 0.00
% 2.78/1.42  Index Deletion       : 0.00
% 2.78/1.42  Index Matching       : 0.00
% 2.78/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
