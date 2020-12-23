%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:53 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 166 expanded)
%              Number of leaves         :   37 (  72 expanded)
%              Depth                    :   12
%              Number of atoms          :  144 ( 332 expanded)
%              Number of equality atoms :   71 ( 174 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_116,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_85,plain,(
    ! [A_50] :
      ( k2_relat_1(A_50) = k1_xboole_0
      | k1_relat_1(A_50) != k1_xboole_0
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_89,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_85])).

tff(c_90,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_146,plain,(
    ! [A_67] :
      ( k1_relat_1(A_67) = k1_xboole_0
      | k2_relat_1(A_67) != k1_xboole_0
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_149,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_146])).

tff(c_152,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_149])).

tff(c_28,plain,(
    ! [A_27,B_28] :
      ( r2_hidden('#skF_1'(A_27,B_28),A_27)
      | k1_xboole_0 = A_27
      | k1_tarski(B_28) = A_27 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_58,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_206,plain,(
    ! [B_82,A_83] :
      ( k7_relat_1(B_82,A_83) = B_82
      | ~ r1_tarski(k1_relat_1(B_82),A_83)
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_212,plain,(
    ! [B_84] :
      ( k7_relat_1(B_84,k1_relat_1(B_84)) = B_84
      | ~ v1_relat_1(B_84) ) ),
    inference(resolution,[status(thm)],[c_6,c_206])).

tff(c_32,plain,(
    ! [B_34,A_33] :
      ( k2_relat_1(k7_relat_1(B_34,A_33)) = k9_relat_1(B_34,A_33)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_229,plain,(
    ! [B_87] :
      ( k9_relat_1(B_87,k1_relat_1(B_87)) = k2_relat_1(B_87)
      | ~ v1_relat_1(B_87)
      | ~ v1_relat_1(B_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_32])).

tff(c_56,plain,(
    k1_tarski('#skF_2') = k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_163,plain,(
    ! [A_73,B_74] :
      ( k9_relat_1(A_73,k1_tarski(B_74)) = k11_relat_1(A_73,B_74)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_172,plain,(
    ! [A_73] :
      ( k9_relat_1(A_73,k1_relat_1('#skF_3')) = k11_relat_1(A_73,'#skF_2')
      | ~ v1_relat_1(A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_163])).

tff(c_236,plain,
    ( k11_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_172])).

tff(c_246,plain,(
    k11_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_60,c_60,c_236])).

tff(c_34,plain,(
    ! [A_35,B_36,C_37] :
      ( r2_hidden(k4_tarski(A_35,B_36),C_37)
      | ~ r2_hidden(B_36,k11_relat_1(C_37,A_35))
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1215,plain,(
    ! [C_143,A_144,B_145] :
      ( k1_funct_1(C_143,A_144) = B_145
      | ~ r2_hidden(k4_tarski(A_144,B_145),C_143)
      | ~ v1_funct_1(C_143)
      | ~ v1_relat_1(C_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1370,plain,(
    ! [C_153,A_154,B_155] :
      ( k1_funct_1(C_153,A_154) = B_155
      | ~ v1_funct_1(C_153)
      | ~ r2_hidden(B_155,k11_relat_1(C_153,A_154))
      | ~ v1_relat_1(C_153) ) ),
    inference(resolution,[status(thm)],[c_34,c_1215])).

tff(c_1377,plain,(
    ! [B_155] :
      ( k1_funct_1('#skF_3','#skF_2') = B_155
      | ~ v1_funct_1('#skF_3')
      | ~ r2_hidden(B_155,k2_relat_1('#skF_3'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_1370])).

tff(c_1386,plain,(
    ! [B_156] :
      ( k1_funct_1('#skF_3','#skF_2') = B_156
      | ~ r2_hidden(B_156,k2_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1377])).

tff(c_1394,plain,(
    ! [B_28] :
      ( '#skF_1'(k2_relat_1('#skF_3'),B_28) = k1_funct_1('#skF_3','#skF_2')
      | k2_relat_1('#skF_3') = k1_xboole_0
      | k2_relat_1('#skF_3') = k1_tarski(B_28) ) ),
    inference(resolution,[status(thm)],[c_28,c_1386])).

tff(c_1399,plain,(
    ! [B_157] :
      ( '#skF_1'(k2_relat_1('#skF_3'),B_157) = k1_funct_1('#skF_3','#skF_2')
      | k2_relat_1('#skF_3') = k1_tarski(B_157) ) ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_1394])).

tff(c_26,plain,(
    ! [A_27,B_28] :
      ( '#skF_1'(A_27,B_28) != B_28
      | k1_xboole_0 = A_27
      | k1_tarski(B_28) = A_27 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1407,plain,(
    ! [B_157] :
      ( k1_funct_1('#skF_3','#skF_2') != B_157
      | k2_relat_1('#skF_3') = k1_xboole_0
      | k2_relat_1('#skF_3') = k1_tarski(B_157)
      | k2_relat_1('#skF_3') = k1_tarski(B_157) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1399,c_26])).

tff(c_1415,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) = k2_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_1407])).

tff(c_54,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) != k2_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1418,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1415,c_54])).

tff(c_1420,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_1435,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1420,c_56])).

tff(c_8,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1421,plain,(
    ! [A_158,C_159,B_160] :
      ( r2_hidden(A_158,C_159)
      | ~ r1_tarski(k2_tarski(A_158,B_160),C_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1452,plain,(
    ! [A_164,C_165] :
      ( r2_hidden(A_164,C_165)
      | ~ r1_tarski(k1_tarski(A_164),C_165) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1421])).

tff(c_1455,plain,(
    ! [C_165] :
      ( r2_hidden('#skF_2',C_165)
      | ~ r1_tarski(k1_xboole_0,C_165) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1435,c_1452])).

tff(c_1531,plain,(
    ! [B_185,A_186] :
      ( k11_relat_1(B_185,A_186) != k1_xboole_0
      | ~ r2_hidden(A_186,k1_relat_1(B_185))
      | ~ v1_relat_1(B_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1538,plain,(
    ! [A_186] :
      ( k11_relat_1('#skF_3',A_186) != k1_xboole_0
      | ~ r2_hidden(A_186,k1_xboole_0)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1420,c_1531])).

tff(c_1542,plain,(
    ! [A_187] :
      ( k11_relat_1('#skF_3',A_187) != k1_xboole_0
      | ~ r2_hidden(A_187,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1538])).

tff(c_1546,plain,
    ( k11_relat_1('#skF_3','#skF_2') != k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1455,c_1542])).

tff(c_1552,plain,(
    k11_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1546])).

tff(c_1509,plain,(
    ! [A_180,B_181] :
      ( k9_relat_1(A_180,k1_tarski(B_181)) = k11_relat_1(A_180,B_181)
      | ~ v1_relat_1(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1521,plain,(
    ! [A_182] :
      ( k9_relat_1(A_182,k1_xboole_0) = k11_relat_1(A_182,'#skF_2')
      | ~ v1_relat_1(A_182) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1435,c_1509])).

tff(c_1525,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) = k11_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_1521])).

tff(c_1419,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_1560,plain,(
    ! [B_189,A_190] :
      ( k7_relat_1(B_189,A_190) = B_189
      | ~ r1_tarski(k1_relat_1(B_189),A_190)
      | ~ v1_relat_1(B_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1571,plain,(
    ! [B_191] :
      ( k7_relat_1(B_191,k1_relat_1(B_191)) = B_191
      | ~ v1_relat_1(B_191) ) ),
    inference(resolution,[status(thm)],[c_6,c_1560])).

tff(c_1583,plain,
    ( k7_relat_1('#skF_3',k1_xboole_0) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1420,c_1571])).

tff(c_1587,plain,(
    k7_relat_1('#skF_3',k1_xboole_0) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1583])).

tff(c_1591,plain,
    ( k9_relat_1('#skF_3',k1_xboole_0) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1587,c_32])).

tff(c_1595,plain,(
    k11_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1525,c_1419,c_1591])).

tff(c_1597,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1552,c_1595])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:53:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.19/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.53  
% 3.19/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/1.53  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.40/1.53  
% 3.40/1.53  %Foreground sorts:
% 3.40/1.53  
% 3.40/1.53  
% 3.40/1.53  %Background operators:
% 3.40/1.53  
% 3.40/1.53  
% 3.40/1.53  %Foreground operators:
% 3.40/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.40/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.40/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.40/1.53  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.40/1.53  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.40/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.40/1.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.40/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.40/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.40/1.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.40/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.40/1.53  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.40/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.40/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.40/1.53  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.40/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.40/1.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.40/1.53  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.40/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.40/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.53  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.40/1.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.40/1.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.40/1.53  
% 3.45/1.55  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.45/1.55  tff(f_116, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.45/1.55  tff(f_91, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 3.45/1.55  tff(f_63, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 3.45/1.55  tff(f_97, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 3.45/1.55  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.45/1.55  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 3.45/1.55  tff(f_78, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 3.45/1.55  tff(f_107, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 3.45/1.55  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.45/1.55  tff(f_49, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.45/1.55  tff(f_85, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 3.45/1.55  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.45/1.55  tff(c_60, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.45/1.55  tff(c_85, plain, (![A_50]: (k2_relat_1(A_50)=k1_xboole_0 | k1_relat_1(A_50)!=k1_xboole_0 | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.45/1.55  tff(c_89, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_60, c_85])).
% 3.45/1.55  tff(c_90, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_89])).
% 3.45/1.55  tff(c_146, plain, (![A_67]: (k1_relat_1(A_67)=k1_xboole_0 | k2_relat_1(A_67)!=k1_xboole_0 | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.45/1.55  tff(c_149, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_60, c_146])).
% 3.45/1.55  tff(c_152, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_90, c_149])).
% 3.45/1.55  tff(c_28, plain, (![A_27, B_28]: (r2_hidden('#skF_1'(A_27, B_28), A_27) | k1_xboole_0=A_27 | k1_tarski(B_28)=A_27)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.45/1.55  tff(c_58, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.45/1.55  tff(c_206, plain, (![B_82, A_83]: (k7_relat_1(B_82, A_83)=B_82 | ~r1_tarski(k1_relat_1(B_82), A_83) | ~v1_relat_1(B_82))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.45/1.55  tff(c_212, plain, (![B_84]: (k7_relat_1(B_84, k1_relat_1(B_84))=B_84 | ~v1_relat_1(B_84))), inference(resolution, [status(thm)], [c_6, c_206])).
% 3.45/1.55  tff(c_32, plain, (![B_34, A_33]: (k2_relat_1(k7_relat_1(B_34, A_33))=k9_relat_1(B_34, A_33) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.45/1.55  tff(c_229, plain, (![B_87]: (k9_relat_1(B_87, k1_relat_1(B_87))=k2_relat_1(B_87) | ~v1_relat_1(B_87) | ~v1_relat_1(B_87))), inference(superposition, [status(thm), theory('equality')], [c_212, c_32])).
% 3.45/1.55  tff(c_56, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.45/1.55  tff(c_163, plain, (![A_73, B_74]: (k9_relat_1(A_73, k1_tarski(B_74))=k11_relat_1(A_73, B_74) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.45/1.55  tff(c_172, plain, (![A_73]: (k9_relat_1(A_73, k1_relat_1('#skF_3'))=k11_relat_1(A_73, '#skF_2') | ~v1_relat_1(A_73))), inference(superposition, [status(thm), theory('equality')], [c_56, c_163])).
% 3.45/1.55  tff(c_236, plain, (k11_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_229, c_172])).
% 3.45/1.55  tff(c_246, plain, (k11_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_60, c_60, c_236])).
% 3.45/1.55  tff(c_34, plain, (![A_35, B_36, C_37]: (r2_hidden(k4_tarski(A_35, B_36), C_37) | ~r2_hidden(B_36, k11_relat_1(C_37, A_35)) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.45/1.55  tff(c_1215, plain, (![C_143, A_144, B_145]: (k1_funct_1(C_143, A_144)=B_145 | ~r2_hidden(k4_tarski(A_144, B_145), C_143) | ~v1_funct_1(C_143) | ~v1_relat_1(C_143))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.45/1.55  tff(c_1370, plain, (![C_153, A_154, B_155]: (k1_funct_1(C_153, A_154)=B_155 | ~v1_funct_1(C_153) | ~r2_hidden(B_155, k11_relat_1(C_153, A_154)) | ~v1_relat_1(C_153))), inference(resolution, [status(thm)], [c_34, c_1215])).
% 3.45/1.55  tff(c_1377, plain, (![B_155]: (k1_funct_1('#skF_3', '#skF_2')=B_155 | ~v1_funct_1('#skF_3') | ~r2_hidden(B_155, k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_246, c_1370])).
% 3.45/1.55  tff(c_1386, plain, (![B_156]: (k1_funct_1('#skF_3', '#skF_2')=B_156 | ~r2_hidden(B_156, k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1377])).
% 3.45/1.55  tff(c_1394, plain, (![B_28]: ('#skF_1'(k2_relat_1('#skF_3'), B_28)=k1_funct_1('#skF_3', '#skF_2') | k2_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')=k1_tarski(B_28))), inference(resolution, [status(thm)], [c_28, c_1386])).
% 3.45/1.55  tff(c_1399, plain, (![B_157]: ('#skF_1'(k2_relat_1('#skF_3'), B_157)=k1_funct_1('#skF_3', '#skF_2') | k2_relat_1('#skF_3')=k1_tarski(B_157))), inference(negUnitSimplification, [status(thm)], [c_152, c_1394])).
% 3.45/1.55  tff(c_26, plain, (![A_27, B_28]: ('#skF_1'(A_27, B_28)!=B_28 | k1_xboole_0=A_27 | k1_tarski(B_28)=A_27)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.45/1.55  tff(c_1407, plain, (![B_157]: (k1_funct_1('#skF_3', '#skF_2')!=B_157 | k2_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')=k1_tarski(B_157) | k2_relat_1('#skF_3')=k1_tarski(B_157))), inference(superposition, [status(thm), theory('equality')], [c_1399, c_26])).
% 3.45/1.55  tff(c_1415, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))=k2_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_152, c_1407])).
% 3.45/1.55  tff(c_54, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))!=k2_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.45/1.55  tff(c_1418, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1415, c_54])).
% 3.45/1.55  tff(c_1420, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_89])).
% 3.45/1.55  tff(c_1435, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1420, c_56])).
% 3.45/1.55  tff(c_8, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.45/1.55  tff(c_1421, plain, (![A_158, C_159, B_160]: (r2_hidden(A_158, C_159) | ~r1_tarski(k2_tarski(A_158, B_160), C_159))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.45/1.55  tff(c_1452, plain, (![A_164, C_165]: (r2_hidden(A_164, C_165) | ~r1_tarski(k1_tarski(A_164), C_165))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1421])).
% 3.45/1.55  tff(c_1455, plain, (![C_165]: (r2_hidden('#skF_2', C_165) | ~r1_tarski(k1_xboole_0, C_165))), inference(superposition, [status(thm), theory('equality')], [c_1435, c_1452])).
% 3.45/1.55  tff(c_1531, plain, (![B_185, A_186]: (k11_relat_1(B_185, A_186)!=k1_xboole_0 | ~r2_hidden(A_186, k1_relat_1(B_185)) | ~v1_relat_1(B_185))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.45/1.55  tff(c_1538, plain, (![A_186]: (k11_relat_1('#skF_3', A_186)!=k1_xboole_0 | ~r2_hidden(A_186, k1_xboole_0) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1420, c_1531])).
% 3.45/1.55  tff(c_1542, plain, (![A_187]: (k11_relat_1('#skF_3', A_187)!=k1_xboole_0 | ~r2_hidden(A_187, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1538])).
% 3.45/1.55  tff(c_1546, plain, (k11_relat_1('#skF_3', '#skF_2')!=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_1455, c_1542])).
% 3.45/1.55  tff(c_1552, plain, (k11_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1546])).
% 3.45/1.55  tff(c_1509, plain, (![A_180, B_181]: (k9_relat_1(A_180, k1_tarski(B_181))=k11_relat_1(A_180, B_181) | ~v1_relat_1(A_180))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.45/1.55  tff(c_1521, plain, (![A_182]: (k9_relat_1(A_182, k1_xboole_0)=k11_relat_1(A_182, '#skF_2') | ~v1_relat_1(A_182))), inference(superposition, [status(thm), theory('equality')], [c_1435, c_1509])).
% 3.45/1.55  tff(c_1525, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k11_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_1521])).
% 3.45/1.55  tff(c_1419, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_89])).
% 3.45/1.55  tff(c_1560, plain, (![B_189, A_190]: (k7_relat_1(B_189, A_190)=B_189 | ~r1_tarski(k1_relat_1(B_189), A_190) | ~v1_relat_1(B_189))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.45/1.55  tff(c_1571, plain, (![B_191]: (k7_relat_1(B_191, k1_relat_1(B_191))=B_191 | ~v1_relat_1(B_191))), inference(resolution, [status(thm)], [c_6, c_1560])).
% 3.45/1.55  tff(c_1583, plain, (k7_relat_1('#skF_3', k1_xboole_0)='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1420, c_1571])).
% 3.45/1.55  tff(c_1587, plain, (k7_relat_1('#skF_3', k1_xboole_0)='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1583])).
% 3.45/1.55  tff(c_1591, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1587, c_32])).
% 3.45/1.55  tff(c_1595, plain, (k11_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1525, c_1419, c_1591])).
% 3.45/1.55  tff(c_1597, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1552, c_1595])).
% 3.45/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/1.55  
% 3.45/1.55  Inference rules
% 3.45/1.55  ----------------------
% 3.45/1.55  #Ref     : 0
% 3.45/1.55  #Sup     : 326
% 3.45/1.55  #Fact    : 0
% 3.45/1.55  #Define  : 0
% 3.45/1.55  #Split   : 1
% 3.45/1.55  #Chain   : 0
% 3.45/1.55  #Close   : 0
% 3.45/1.55  
% 3.45/1.55  Ordering : KBO
% 3.45/1.55  
% 3.45/1.55  Simplification rules
% 3.45/1.55  ----------------------
% 3.45/1.55  #Subsume      : 52
% 3.45/1.55  #Demod        : 197
% 3.45/1.55  #Tautology    : 162
% 3.45/1.55  #SimpNegUnit  : 49
% 3.45/1.55  #BackRed      : 4
% 3.45/1.55  
% 3.45/1.55  #Partial instantiations: 0
% 3.45/1.55  #Strategies tried      : 1
% 3.45/1.55  
% 3.45/1.55  Timing (in seconds)
% 3.45/1.55  ----------------------
% 3.45/1.55  Preprocessing        : 0.33
% 3.45/1.55  Parsing              : 0.18
% 3.45/1.55  CNF conversion       : 0.02
% 3.45/1.55  Main loop            : 0.42
% 3.45/1.55  Inferencing          : 0.16
% 3.45/1.55  Reduction            : 0.14
% 3.45/1.55  Demodulation         : 0.09
% 3.45/1.55  BG Simplification    : 0.02
% 3.45/1.55  Subsumption          : 0.07
% 3.45/1.55  Abstraction          : 0.02
% 3.45/1.55  MUC search           : 0.00
% 3.45/1.55  Cooper               : 0.00
% 3.45/1.55  Total                : 0.79
% 3.45/1.55  Index Insertion      : 0.00
% 3.45/1.55  Index Deletion       : 0.00
% 3.45/1.55  Index Matching       : 0.00
% 3.45/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
