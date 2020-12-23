%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:06 EST 2020

% Result     : Theorem 4.02s
% Output     : CNFRefutation 4.02s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 132 expanded)
%              Number of leaves         :   31 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :  121 ( 255 expanded)
%              Number of equality atoms :   25 (  49 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_62,axiom,(
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

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_88,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_30,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_3'(A_13,B_14),B_14)
      | r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_32,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_3'(A_13,B_14),A_13)
      | r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_312,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_3'(A_63,B_64),A_63)
      | r1_xboole_0(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_60,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_107,plain,(
    ! [B_38,A_39] :
      ( r1_xboole_0(B_38,A_39)
      | ~ r1_xboole_0(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_110,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_107])).

tff(c_146,plain,(
    ! [A_46,B_47] :
      ( k3_xboole_0(A_46,B_47) = k1_xboole_0
      | ~ r1_xboole_0(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_153,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_110,c_146])).

tff(c_271,plain,(
    ! [D_58,B_59,A_60] :
      ( r2_hidden(D_58,B_59)
      | ~ r2_hidden(D_58,k3_xboole_0(A_60,B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_274,plain,(
    ! [D_58] :
      ( r2_hidden(D_58,'#skF_6')
      | ~ r2_hidden(D_58,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_271])).

tff(c_1183,plain,(
    ! [B_128] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_128),'#skF_6')
      | r1_xboole_0(k1_xboole_0,B_128) ) ),
    inference(resolution,[status(thm)],[c_312,c_274])).

tff(c_154,plain,(
    k3_xboole_0('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_146])).

tff(c_277,plain,(
    ! [D_58] :
      ( r2_hidden(D_58,'#skF_5')
      | ~ r2_hidden(D_58,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_271])).

tff(c_1162,plain,(
    ! [B_124] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_124),'#skF_5')
      | r1_xboole_0(k1_xboole_0,B_124) ) ),
    inference(resolution,[status(thm)],[c_312,c_277])).

tff(c_823,plain,(
    ! [A_104,B_105,C_106] :
      ( ~ r1_xboole_0(A_104,B_105)
      | ~ r2_hidden(C_106,B_105)
      | ~ r2_hidden(C_106,A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_841,plain,(
    ! [C_106] :
      ( ~ r2_hidden(C_106,'#skF_5')
      | ~ r2_hidden(C_106,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_60,c_823])).

tff(c_1166,plain,(
    ! [B_124] :
      ( ~ r2_hidden('#skF_3'(k1_xboole_0,B_124),'#skF_6')
      | r1_xboole_0(k1_xboole_0,B_124) ) ),
    inference(resolution,[status(thm)],[c_1162,c_841])).

tff(c_1202,plain,(
    ! [B_129] : r1_xboole_0(k1_xboole_0,B_129) ),
    inference(resolution,[status(thm)],[c_1183,c_1166])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = k1_xboole_0
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1323,plain,(
    ! [B_134] : k3_xboole_0(k1_xboole_0,B_134) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1202,c_22])).

tff(c_159,plain,(
    ! [A_48,B_49] :
      ( r1_xboole_0(A_48,B_49)
      | k3_xboole_0(A_48,B_49) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_44,plain,(
    ! [A_25,B_26] :
      ( k4_xboole_0(A_25,B_26) = A_25
      | ~ r1_xboole_0(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_464,plain,(
    ! [A_82,B_83] :
      ( k4_xboole_0(A_82,B_83) = A_82
      | k3_xboole_0(A_82,B_83) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_159,c_44])).

tff(c_54,plain,(
    ! [B_34,A_33] :
      ( ~ r2_hidden(B_34,A_33)
      | k4_xboole_0(A_33,k1_tarski(B_34)) != A_33 ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_502,plain,(
    ! [B_34,A_82] :
      ( ~ r2_hidden(B_34,A_82)
      | k3_xboole_0(A_82,k1_tarski(B_34)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_464,c_54])).

tff(c_1374,plain,(
    ! [B_34] : ~ r2_hidden(B_34,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1323,c_502])).

tff(c_62,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_64,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_141,plain,(
    ! [A_44,B_45] :
      ( k3_xboole_0(A_44,B_45) = A_44
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_145,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_7')) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_141])).

tff(c_56,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(A_33,k1_tarski(B_34)) = A_33
      | r2_hidden(B_34,A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_196,plain,(
    ! [A_50,B_51] :
      ( r1_xboole_0(A_50,B_51)
      | k4_xboole_0(A_50,B_51) != A_50 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_537,plain,(
    ! [A_84,B_85] :
      ( k3_xboole_0(A_84,B_85) = k1_xboole_0
      | k4_xboole_0(A_84,B_85) != A_84 ) ),
    inference(resolution,[status(thm)],[c_196,c_22])).

tff(c_592,plain,(
    ! [A_93,B_94] :
      ( k3_xboole_0(A_93,k1_tarski(B_94)) = k1_xboole_0
      | r2_hidden(B_94,A_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_537])).

tff(c_625,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0
    | r2_hidden('#skF_7',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_592])).

tff(c_1685,plain,(
    r2_hidden('#skF_7',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_625])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1697,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_1685,c_6])).

tff(c_1700,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_1697,c_841])).

tff(c_1704,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1700])).

tff(c_1705,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_625])).

tff(c_4,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,k3_xboole_0(A_3,B_4))
      | ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1716,plain,(
    ! [D_8] :
      ( r2_hidden(D_8,k1_xboole_0)
      | ~ r2_hidden(D_8,'#skF_5')
      | ~ r2_hidden(D_8,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1705,c_4])).

tff(c_1887,plain,(
    ! [D_149] :
      ( ~ r2_hidden(D_149,'#skF_5')
      | ~ r2_hidden(D_149,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1374,c_1716])).

tff(c_1922,plain,(
    ! [B_153] :
      ( ~ r2_hidden('#skF_3'('#skF_5',B_153),'#skF_4')
      | r1_xboole_0('#skF_5',B_153) ) ),
    inference(resolution,[status(thm)],[c_32,c_1887])).

tff(c_1927,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_1922])).

tff(c_888,plain,(
    ! [A_112,C_113,B_114] :
      ( ~ r1_xboole_0(A_112,C_113)
      | ~ r1_xboole_0(A_112,B_114)
      | r1_xboole_0(A_112,k2_xboole_0(B_114,C_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_26,plain,(
    ! [B_12,A_11] :
      ( r1_xboole_0(B_12,A_11)
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2640,plain,(
    ! [B_211,C_212,A_213] :
      ( r1_xboole_0(k2_xboole_0(B_211,C_212),A_213)
      | ~ r1_xboole_0(A_213,C_212)
      | ~ r1_xboole_0(A_213,B_211) ) ),
    inference(resolution,[status(thm)],[c_888,c_26])).

tff(c_58,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2661,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_6')
    | ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_2640,c_58])).

tff(c_2671,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1927,c_110,c_2661])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:31:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.02/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.02/1.71  
% 4.02/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.02/1.72  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 4.02/1.72  
% 4.02/1.72  %Foreground sorts:
% 4.02/1.72  
% 4.02/1.72  
% 4.02/1.72  %Background operators:
% 4.02/1.72  
% 4.02/1.72  
% 4.02/1.72  %Foreground operators:
% 4.02/1.72  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.02/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.02/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.02/1.72  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.02/1.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.02/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.02/1.72  tff('#skF_7', type, '#skF_7': $i).
% 4.02/1.72  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.02/1.72  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.02/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.02/1.72  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.02/1.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.02/1.72  tff('#skF_5', type, '#skF_5': $i).
% 4.02/1.72  tff('#skF_6', type, '#skF_6': $i).
% 4.02/1.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.02/1.72  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.02/1.72  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.02/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.02/1.72  tff('#skF_4', type, '#skF_4': $i).
% 4.02/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.02/1.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.02/1.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.02/1.72  
% 4.02/1.73  tff(f_62, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.02/1.73  tff(f_108, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 4.02/1.73  tff(f_44, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.02/1.73  tff(f_40, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.02/1.73  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.02/1.73  tff(f_88, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.02/1.73  tff(f_99, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 4.02/1.73  tff(f_68, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.02/1.73  tff(f_84, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 4.02/1.73  tff(c_30, plain, (![A_13, B_14]: (r2_hidden('#skF_3'(A_13, B_14), B_14) | r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.02/1.73  tff(c_32, plain, (![A_13, B_14]: (r2_hidden('#skF_3'(A_13, B_14), A_13) | r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.02/1.73  tff(c_312, plain, (![A_63, B_64]: (r2_hidden('#skF_3'(A_63, B_64), A_63) | r1_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.02/1.73  tff(c_60, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.02/1.73  tff(c_107, plain, (![B_38, A_39]: (r1_xboole_0(B_38, A_39) | ~r1_xboole_0(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.02/1.73  tff(c_110, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_60, c_107])).
% 4.02/1.73  tff(c_146, plain, (![A_46, B_47]: (k3_xboole_0(A_46, B_47)=k1_xboole_0 | ~r1_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.02/1.73  tff(c_153, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_110, c_146])).
% 4.02/1.73  tff(c_271, plain, (![D_58, B_59, A_60]: (r2_hidden(D_58, B_59) | ~r2_hidden(D_58, k3_xboole_0(A_60, B_59)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.02/1.73  tff(c_274, plain, (![D_58]: (r2_hidden(D_58, '#skF_6') | ~r2_hidden(D_58, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_153, c_271])).
% 4.02/1.73  tff(c_1183, plain, (![B_128]: (r2_hidden('#skF_3'(k1_xboole_0, B_128), '#skF_6') | r1_xboole_0(k1_xboole_0, B_128))), inference(resolution, [status(thm)], [c_312, c_274])).
% 4.02/1.73  tff(c_154, plain, (k3_xboole_0('#skF_6', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_60, c_146])).
% 4.02/1.73  tff(c_277, plain, (![D_58]: (r2_hidden(D_58, '#skF_5') | ~r2_hidden(D_58, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_154, c_271])).
% 4.02/1.73  tff(c_1162, plain, (![B_124]: (r2_hidden('#skF_3'(k1_xboole_0, B_124), '#skF_5') | r1_xboole_0(k1_xboole_0, B_124))), inference(resolution, [status(thm)], [c_312, c_277])).
% 4.02/1.73  tff(c_823, plain, (![A_104, B_105, C_106]: (~r1_xboole_0(A_104, B_105) | ~r2_hidden(C_106, B_105) | ~r2_hidden(C_106, A_104))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.02/1.73  tff(c_841, plain, (![C_106]: (~r2_hidden(C_106, '#skF_5') | ~r2_hidden(C_106, '#skF_6'))), inference(resolution, [status(thm)], [c_60, c_823])).
% 4.02/1.73  tff(c_1166, plain, (![B_124]: (~r2_hidden('#skF_3'(k1_xboole_0, B_124), '#skF_6') | r1_xboole_0(k1_xboole_0, B_124))), inference(resolution, [status(thm)], [c_1162, c_841])).
% 4.02/1.73  tff(c_1202, plain, (![B_129]: (r1_xboole_0(k1_xboole_0, B_129))), inference(resolution, [status(thm)], [c_1183, c_1166])).
% 4.02/1.73  tff(c_22, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=k1_xboole_0 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.02/1.73  tff(c_1323, plain, (![B_134]: (k3_xboole_0(k1_xboole_0, B_134)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1202, c_22])).
% 4.02/1.73  tff(c_159, plain, (![A_48, B_49]: (r1_xboole_0(A_48, B_49) | k3_xboole_0(A_48, B_49)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.02/1.73  tff(c_44, plain, (![A_25, B_26]: (k4_xboole_0(A_25, B_26)=A_25 | ~r1_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.02/1.73  tff(c_464, plain, (![A_82, B_83]: (k4_xboole_0(A_82, B_83)=A_82 | k3_xboole_0(A_82, B_83)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_159, c_44])).
% 4.02/1.73  tff(c_54, plain, (![B_34, A_33]: (~r2_hidden(B_34, A_33) | k4_xboole_0(A_33, k1_tarski(B_34))!=A_33)), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.02/1.73  tff(c_502, plain, (![B_34, A_82]: (~r2_hidden(B_34, A_82) | k3_xboole_0(A_82, k1_tarski(B_34))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_464, c_54])).
% 4.02/1.73  tff(c_1374, plain, (![B_34]: (~r2_hidden(B_34, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1323, c_502])).
% 4.02/1.73  tff(c_62, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.02/1.73  tff(c_64, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.02/1.73  tff(c_141, plain, (![A_44, B_45]: (k3_xboole_0(A_44, B_45)=A_44 | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.02/1.73  tff(c_145, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_7'))=k3_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_64, c_141])).
% 4.02/1.73  tff(c_56, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k1_tarski(B_34))=A_33 | r2_hidden(B_34, A_33))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.02/1.73  tff(c_196, plain, (![A_50, B_51]: (r1_xboole_0(A_50, B_51) | k4_xboole_0(A_50, B_51)!=A_50)), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.02/1.73  tff(c_537, plain, (![A_84, B_85]: (k3_xboole_0(A_84, B_85)=k1_xboole_0 | k4_xboole_0(A_84, B_85)!=A_84)), inference(resolution, [status(thm)], [c_196, c_22])).
% 4.02/1.73  tff(c_592, plain, (![A_93, B_94]: (k3_xboole_0(A_93, k1_tarski(B_94))=k1_xboole_0 | r2_hidden(B_94, A_93))), inference(superposition, [status(thm), theory('equality')], [c_56, c_537])).
% 4.02/1.73  tff(c_625, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0 | r2_hidden('#skF_7', k3_xboole_0('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_145, c_592])).
% 4.02/1.73  tff(c_1685, plain, (r2_hidden('#skF_7', k3_xboole_0('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_625])).
% 4.02/1.73  tff(c_6, plain, (![D_8, B_4, A_3]: (r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.02/1.73  tff(c_1697, plain, (r2_hidden('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_1685, c_6])).
% 4.02/1.73  tff(c_1700, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_1697, c_841])).
% 4.02/1.73  tff(c_1704, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_1700])).
% 4.02/1.73  tff(c_1705, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_625])).
% 4.02/1.73  tff(c_4, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, k3_xboole_0(A_3, B_4)) | ~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.02/1.73  tff(c_1716, plain, (![D_8]: (r2_hidden(D_8, k1_xboole_0) | ~r2_hidden(D_8, '#skF_5') | ~r2_hidden(D_8, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1705, c_4])).
% 4.02/1.73  tff(c_1887, plain, (![D_149]: (~r2_hidden(D_149, '#skF_5') | ~r2_hidden(D_149, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1374, c_1716])).
% 4.02/1.73  tff(c_1922, plain, (![B_153]: (~r2_hidden('#skF_3'('#skF_5', B_153), '#skF_4') | r1_xboole_0('#skF_5', B_153))), inference(resolution, [status(thm)], [c_32, c_1887])).
% 4.02/1.73  tff(c_1927, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_1922])).
% 4.02/1.73  tff(c_888, plain, (![A_112, C_113, B_114]: (~r1_xboole_0(A_112, C_113) | ~r1_xboole_0(A_112, B_114) | r1_xboole_0(A_112, k2_xboole_0(B_114, C_113)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.02/1.73  tff(c_26, plain, (![B_12, A_11]: (r1_xboole_0(B_12, A_11) | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.02/1.73  tff(c_2640, plain, (![B_211, C_212, A_213]: (r1_xboole_0(k2_xboole_0(B_211, C_212), A_213) | ~r1_xboole_0(A_213, C_212) | ~r1_xboole_0(A_213, B_211))), inference(resolution, [status(thm)], [c_888, c_26])).
% 4.02/1.73  tff(c_58, plain, (~r1_xboole_0(k2_xboole_0('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.02/1.73  tff(c_2661, plain, (~r1_xboole_0('#skF_5', '#skF_6') | ~r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_2640, c_58])).
% 4.02/1.73  tff(c_2671, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1927, c_110, c_2661])).
% 4.02/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.02/1.73  
% 4.02/1.73  Inference rules
% 4.02/1.73  ----------------------
% 4.02/1.73  #Ref     : 0
% 4.02/1.73  #Sup     : 599
% 4.02/1.73  #Fact    : 0
% 4.02/1.73  #Define  : 0
% 4.02/1.73  #Split   : 5
% 4.02/1.73  #Chain   : 0
% 4.02/1.73  #Close   : 0
% 4.02/1.73  
% 4.02/1.73  Ordering : KBO
% 4.02/1.73  
% 4.02/1.73  Simplification rules
% 4.02/1.73  ----------------------
% 4.02/1.73  #Subsume      : 95
% 4.02/1.73  #Demod        : 211
% 4.02/1.73  #Tautology    : 281
% 4.02/1.73  #SimpNegUnit  : 15
% 4.02/1.73  #BackRed      : 4
% 4.02/1.73  
% 4.02/1.73  #Partial instantiations: 0
% 4.02/1.73  #Strategies tried      : 1
% 4.02/1.73  
% 4.02/1.73  Timing (in seconds)
% 4.02/1.73  ----------------------
% 4.02/1.73  Preprocessing        : 0.33
% 4.02/1.73  Parsing              : 0.17
% 4.02/1.73  CNF conversion       : 0.02
% 4.02/1.73  Main loop            : 0.65
% 4.02/1.73  Inferencing          : 0.22
% 4.02/1.74  Reduction            : 0.21
% 4.02/1.74  Demodulation         : 0.16
% 4.02/1.74  BG Simplification    : 0.03
% 4.02/1.74  Subsumption          : 0.13
% 4.02/1.74  Abstraction          : 0.03
% 4.02/1.74  MUC search           : 0.00
% 4.02/1.74  Cooper               : 0.00
% 4.02/1.74  Total                : 1.01
% 4.02/1.74  Index Insertion      : 0.00
% 4.02/1.74  Index Deletion       : 0.00
% 4.02/1.74  Index Matching       : 0.00
% 4.02/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
