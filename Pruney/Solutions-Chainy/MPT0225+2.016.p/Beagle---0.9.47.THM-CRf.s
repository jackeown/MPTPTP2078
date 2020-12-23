%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:33 EST 2020

% Result     : Theorem 3.41s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 161 expanded)
%              Number of leaves         :   32 (  67 expanded)
%              Depth                    :   11
%              Number of atoms          :  104 ( 272 expanded)
%              Number of equality atoms :   50 ( 138 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_7 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_76,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_78,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_103,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_47,axiom,(
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

tff(f_92,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_46,plain,(
    ! [A_21] : k2_tarski(A_21,A_21) = k1_tarski(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1268,plain,(
    ! [A_3825,B_3826] : k1_enumset1(A_3825,A_3825,B_3826) = k2_tarski(A_3825,B_3826) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_26,plain,(
    ! [E_20,A_14,C_16] : r2_hidden(E_20,k1_enumset1(A_14,E_20,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1286,plain,(
    ! [A_3827,B_3828] : r2_hidden(A_3827,k2_tarski(A_3827,B_3828)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1268,c_26])).

tff(c_1289,plain,(
    ! [A_21] : r2_hidden(A_21,k1_tarski(A_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1286])).

tff(c_124,plain,(
    ! [A_61,B_62] : k1_enumset1(A_61,A_61,B_62) = k2_tarski(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_142,plain,(
    ! [A_63,B_64] : r2_hidden(A_63,k2_tarski(A_63,B_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_26])).

tff(c_145,plain,(
    ! [A_21] : r2_hidden(A_21,k1_tarski(A_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_142])).

tff(c_70,plain,
    ( '#skF_7' != '#skF_6'
    | '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_77,plain,(
    '#skF_7' != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_106,plain,(
    ! [A_57,B_58] :
      ( r1_xboole_0(k1_tarski(A_57),B_58)
      | r2_hidden(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_167,plain,(
    ! [B_70,A_71] :
      ( r1_xboole_0(B_70,k1_tarski(A_71))
      | r2_hidden(A_71,B_70) ) ),
    inference(resolution,[status(thm)],[c_106,c_2])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = A_12
      | ~ r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_178,plain,(
    ! [B_70,A_71] :
      ( k4_xboole_0(B_70,k1_tarski(A_71)) = B_70
      | r2_hidden(A_71,B_70) ) ),
    inference(resolution,[status(thm)],[c_167,c_18])).

tff(c_208,plain,(
    ! [B_80,A_81] :
      ( k4_xboole_0(B_80,k1_tarski(A_81)) = B_80
      | r2_hidden(A_81,B_80) ) ),
    inference(resolution,[status(thm)],[c_167,c_18])).

tff(c_68,plain,
    ( k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) != k1_tarski('#skF_6')
    | '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_152,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) != k1_tarski('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_219,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_152])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( r1_xboole_0(A_12,B_13)
      | k4_xboole_0(A_12,B_13) != A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_259,plain,(
    ! [A_91,B_92,C_93] :
      ( ~ r1_xboole_0(A_91,B_92)
      | ~ r2_hidden(C_93,B_92)
      | ~ r2_hidden(C_93,A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_550,plain,(
    ! [C_133,B_134,A_135] :
      ( ~ r2_hidden(C_133,B_134)
      | ~ r2_hidden(C_133,A_135)
      | k4_xboole_0(A_135,B_134) != A_135 ) ),
    inference(resolution,[status(thm)],[c_20,c_259])).

tff(c_599,plain,(
    ! [A_136] :
      ( ~ r2_hidden('#skF_7',A_136)
      | k4_xboole_0(A_136,k1_tarski('#skF_6')) != A_136 ) ),
    inference(resolution,[status(thm)],[c_219,c_550])).

tff(c_610,plain,(
    ! [B_137] :
      ( ~ r2_hidden('#skF_7',B_137)
      | r2_hidden('#skF_6',B_137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_599])).

tff(c_664,plain,(
    ! [A_138,C_139] : r2_hidden('#skF_6',k1_enumset1(A_138,'#skF_7',C_139)) ),
    inference(resolution,[status(thm)],[c_26,c_610])).

tff(c_22,plain,(
    ! [E_20,C_16,B_15,A_14] :
      ( E_20 = C_16
      | E_20 = B_15
      | E_20 = A_14
      | ~ r2_hidden(E_20,k1_enumset1(A_14,B_15,C_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_671,plain,(
    ! [C_139,A_138] :
      ( C_139 = '#skF_6'
      | '#skF_7' = '#skF_6'
      | A_138 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_664,c_22])).

tff(c_680,plain,(
    ! [C_139,A_138] :
      ( C_139 = '#skF_6'
      | A_138 = '#skF_6' ) ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_671])).

tff(c_683,plain,(
    ! [A_140] : A_140 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_680])).

tff(c_895,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_683,c_77])).

tff(c_897,plain,(
    ! [C_1985] : C_1985 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_680])).

tff(c_1109,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_897,c_77])).

tff(c_1110,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_1111,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_72,plain,
    ( k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) != k1_tarski('#skF_6')
    | k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_9')) = k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1135,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1110,c_1111,c_72])).

tff(c_92,plain,(
    ! [A_51,B_52] :
      ( r1_xboole_0(A_51,B_52)
      | k4_xboole_0(A_51,B_52) != A_51 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1121,plain,(
    ! [B_3784,A_3785] :
      ( r1_xboole_0(B_3784,A_3785)
      | k4_xboole_0(A_3785,B_3784) != A_3785 ) ),
    inference(resolution,[status(thm)],[c_92,c_2])).

tff(c_64,plain,(
    ! [A_32,B_33] :
      ( ~ r2_hidden(A_32,B_33)
      | ~ r1_xboole_0(k1_tarski(A_32),B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1194,plain,(
    ! [A_3799,A_3800] :
      ( ~ r2_hidden(A_3799,A_3800)
      | k4_xboole_0(A_3800,k1_tarski(A_3799)) != A_3800 ) ),
    inference(resolution,[status(thm)],[c_1121,c_64])).

tff(c_1197,plain,(
    ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1135,c_1194])).

tff(c_1204,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_1197])).

tff(c_1205,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_1206,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_74,plain,
    ( '#skF_7' != '#skF_6'
    | k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_9')) = k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1257,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1205,c_1206,c_74])).

tff(c_1231,plain,(
    ! [A_3817,B_3818] :
      ( r1_xboole_0(A_3817,B_3818)
      | k4_xboole_0(A_3817,B_3818) != A_3817 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1317,plain,(
    ! [B_3836,A_3837] :
      ( r1_xboole_0(B_3836,A_3837)
      | k4_xboole_0(A_3837,B_3836) != A_3837 ) ),
    inference(resolution,[status(thm)],[c_1231,c_2])).

tff(c_1397,plain,(
    ! [A_3851,A_3852] :
      ( ~ r2_hidden(A_3851,A_3852)
      | k4_xboole_0(A_3852,k1_tarski(A_3851)) != A_3852 ) ),
    inference(resolution,[status(thm)],[c_1317,c_64])).

tff(c_1403,plain,(
    ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1257,c_1397])).

tff(c_1408,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1289,c_1403])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:38:20 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.41/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.68  
% 3.69/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.68  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_7 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 3.69/1.68  
% 3.69/1.68  %Foreground sorts:
% 3.69/1.68  
% 3.69/1.68  
% 3.69/1.68  %Background operators:
% 3.69/1.68  
% 3.69/1.68  
% 3.69/1.68  %Foreground operators:
% 3.69/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.69/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.69/1.68  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.69/1.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.69/1.68  tff('#skF_7', type, '#skF_7': $i).
% 3.69/1.68  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.69/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.69/1.68  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.69/1.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.69/1.68  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.69/1.68  tff('#skF_6', type, '#skF_6': $i).
% 3.69/1.68  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.69/1.68  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.69/1.68  tff('#skF_9', type, '#skF_9': $i).
% 3.69/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.69/1.68  tff('#skF_8', type, '#skF_8': $i).
% 3.69/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.69/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.69/1.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.69/1.68  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.69/1.68  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.69/1.68  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.69/1.68  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.69/1.68  
% 3.69/1.69  tff(f_76, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.69/1.69  tff(f_78, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.69/1.69  tff(f_74, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.69/1.69  tff(f_103, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.69/1.69  tff(f_97, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.69/1.69  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.69/1.69  tff(f_59, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.69/1.69  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.69/1.69  tff(f_92, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 3.69/1.69  tff(c_46, plain, (![A_21]: (k2_tarski(A_21, A_21)=k1_tarski(A_21))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.69/1.69  tff(c_1268, plain, (![A_3825, B_3826]: (k1_enumset1(A_3825, A_3825, B_3826)=k2_tarski(A_3825, B_3826))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.69/1.69  tff(c_26, plain, (![E_20, A_14, C_16]: (r2_hidden(E_20, k1_enumset1(A_14, E_20, C_16)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.69/1.69  tff(c_1286, plain, (![A_3827, B_3828]: (r2_hidden(A_3827, k2_tarski(A_3827, B_3828)))), inference(superposition, [status(thm), theory('equality')], [c_1268, c_26])).
% 3.69/1.69  tff(c_1289, plain, (![A_21]: (r2_hidden(A_21, k1_tarski(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1286])).
% 3.69/1.69  tff(c_124, plain, (![A_61, B_62]: (k1_enumset1(A_61, A_61, B_62)=k2_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.69/1.69  tff(c_142, plain, (![A_63, B_64]: (r2_hidden(A_63, k2_tarski(A_63, B_64)))), inference(superposition, [status(thm), theory('equality')], [c_124, c_26])).
% 3.69/1.69  tff(c_145, plain, (![A_21]: (r2_hidden(A_21, k1_tarski(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_142])).
% 3.69/1.69  tff(c_70, plain, ('#skF_7'!='#skF_6' | '#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.69/1.69  tff(c_77, plain, ('#skF_7'!='#skF_6'), inference(splitLeft, [status(thm)], [c_70])).
% 3.69/1.69  tff(c_106, plain, (![A_57, B_58]: (r1_xboole_0(k1_tarski(A_57), B_58) | r2_hidden(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.69/1.69  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.69/1.69  tff(c_167, plain, (![B_70, A_71]: (r1_xboole_0(B_70, k1_tarski(A_71)) | r2_hidden(A_71, B_70))), inference(resolution, [status(thm)], [c_106, c_2])).
% 3.69/1.69  tff(c_18, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=A_12 | ~r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.69/1.69  tff(c_178, plain, (![B_70, A_71]: (k4_xboole_0(B_70, k1_tarski(A_71))=B_70 | r2_hidden(A_71, B_70))), inference(resolution, [status(thm)], [c_167, c_18])).
% 3.69/1.69  tff(c_208, plain, (![B_80, A_81]: (k4_xboole_0(B_80, k1_tarski(A_81))=B_80 | r2_hidden(A_81, B_80))), inference(resolution, [status(thm)], [c_167, c_18])).
% 3.69/1.69  tff(c_68, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))!=k1_tarski('#skF_6') | '#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.69/1.69  tff(c_152, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))!=k1_tarski('#skF_6')), inference(splitLeft, [status(thm)], [c_68])).
% 3.69/1.69  tff(c_219, plain, (r2_hidden('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_208, c_152])).
% 3.69/1.69  tff(c_20, plain, (![A_12, B_13]: (r1_xboole_0(A_12, B_13) | k4_xboole_0(A_12, B_13)!=A_12)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.69/1.69  tff(c_259, plain, (![A_91, B_92, C_93]: (~r1_xboole_0(A_91, B_92) | ~r2_hidden(C_93, B_92) | ~r2_hidden(C_93, A_91))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.69/1.69  tff(c_550, plain, (![C_133, B_134, A_135]: (~r2_hidden(C_133, B_134) | ~r2_hidden(C_133, A_135) | k4_xboole_0(A_135, B_134)!=A_135)), inference(resolution, [status(thm)], [c_20, c_259])).
% 3.69/1.69  tff(c_599, plain, (![A_136]: (~r2_hidden('#skF_7', A_136) | k4_xboole_0(A_136, k1_tarski('#skF_6'))!=A_136)), inference(resolution, [status(thm)], [c_219, c_550])).
% 3.69/1.69  tff(c_610, plain, (![B_137]: (~r2_hidden('#skF_7', B_137) | r2_hidden('#skF_6', B_137))), inference(superposition, [status(thm), theory('equality')], [c_178, c_599])).
% 3.69/1.69  tff(c_664, plain, (![A_138, C_139]: (r2_hidden('#skF_6', k1_enumset1(A_138, '#skF_7', C_139)))), inference(resolution, [status(thm)], [c_26, c_610])).
% 3.69/1.69  tff(c_22, plain, (![E_20, C_16, B_15, A_14]: (E_20=C_16 | E_20=B_15 | E_20=A_14 | ~r2_hidden(E_20, k1_enumset1(A_14, B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.69/1.69  tff(c_671, plain, (![C_139, A_138]: (C_139='#skF_6' | '#skF_7'='#skF_6' | A_138='#skF_6')), inference(resolution, [status(thm)], [c_664, c_22])).
% 3.69/1.69  tff(c_680, plain, (![C_139, A_138]: (C_139='#skF_6' | A_138='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_77, c_671])).
% 3.69/1.69  tff(c_683, plain, (![A_140]: (A_140='#skF_6')), inference(splitLeft, [status(thm)], [c_680])).
% 3.69/1.69  tff(c_895, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_683, c_77])).
% 3.69/1.69  tff(c_897, plain, (![C_1985]: (C_1985='#skF_6')), inference(splitRight, [status(thm)], [c_680])).
% 3.69/1.69  tff(c_1109, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_897, c_77])).
% 3.69/1.69  tff(c_1110, plain, ('#skF_9'='#skF_8'), inference(splitRight, [status(thm)], [c_68])).
% 3.69/1.69  tff(c_1111, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_68])).
% 3.69/1.69  tff(c_72, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))!=k1_tarski('#skF_6') | k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_9'))=k1_tarski('#skF_8')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.69/1.69  tff(c_1135, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1110, c_1111, c_72])).
% 3.69/1.69  tff(c_92, plain, (![A_51, B_52]: (r1_xboole_0(A_51, B_52) | k4_xboole_0(A_51, B_52)!=A_51)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.69/1.69  tff(c_1121, plain, (![B_3784, A_3785]: (r1_xboole_0(B_3784, A_3785) | k4_xboole_0(A_3785, B_3784)!=A_3785)), inference(resolution, [status(thm)], [c_92, c_2])).
% 3.69/1.69  tff(c_64, plain, (![A_32, B_33]: (~r2_hidden(A_32, B_33) | ~r1_xboole_0(k1_tarski(A_32), B_33))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.69/1.69  tff(c_1194, plain, (![A_3799, A_3800]: (~r2_hidden(A_3799, A_3800) | k4_xboole_0(A_3800, k1_tarski(A_3799))!=A_3800)), inference(resolution, [status(thm)], [c_1121, c_64])).
% 3.69/1.69  tff(c_1197, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1135, c_1194])).
% 3.69/1.69  tff(c_1204, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_145, c_1197])).
% 3.69/1.69  tff(c_1205, plain, ('#skF_9'='#skF_8'), inference(splitRight, [status(thm)], [c_70])).
% 3.69/1.69  tff(c_1206, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_70])).
% 3.69/1.69  tff(c_74, plain, ('#skF_7'!='#skF_6' | k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_9'))=k1_tarski('#skF_8')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.69/1.69  tff(c_1257, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1205, c_1206, c_74])).
% 3.69/1.69  tff(c_1231, plain, (![A_3817, B_3818]: (r1_xboole_0(A_3817, B_3818) | k4_xboole_0(A_3817, B_3818)!=A_3817)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.69/1.69  tff(c_1317, plain, (![B_3836, A_3837]: (r1_xboole_0(B_3836, A_3837) | k4_xboole_0(A_3837, B_3836)!=A_3837)), inference(resolution, [status(thm)], [c_1231, c_2])).
% 3.69/1.69  tff(c_1397, plain, (![A_3851, A_3852]: (~r2_hidden(A_3851, A_3852) | k4_xboole_0(A_3852, k1_tarski(A_3851))!=A_3852)), inference(resolution, [status(thm)], [c_1317, c_64])).
% 3.69/1.69  tff(c_1403, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1257, c_1397])).
% 3.69/1.69  tff(c_1408, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1289, c_1403])).
% 3.69/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.69  
% 3.69/1.69  Inference rules
% 3.69/1.69  ----------------------
% 3.69/1.69  #Ref     : 0
% 3.69/1.69  #Sup     : 391
% 3.69/1.69  #Fact    : 0
% 3.69/1.69  #Define  : 0
% 3.69/1.69  #Split   : 3
% 3.69/1.69  #Chain   : 0
% 3.69/1.69  #Close   : 0
% 3.69/1.69  
% 3.69/1.69  Ordering : KBO
% 3.69/1.69  
% 3.69/1.69  Simplification rules
% 3.69/1.69  ----------------------
% 3.69/1.69  #Subsume      : 33
% 3.69/1.69  #Demod        : 65
% 3.69/1.69  #Tautology    : 106
% 3.69/1.69  #SimpNegUnit  : 1
% 3.69/1.69  #BackRed      : 0
% 3.69/1.69  
% 3.69/1.69  #Partial instantiations: 232
% 3.69/1.69  #Strategies tried      : 1
% 3.69/1.69  
% 3.69/1.69  Timing (in seconds)
% 3.69/1.69  ----------------------
% 3.69/1.70  Preprocessing        : 0.37
% 3.69/1.70  Parsing              : 0.18
% 3.69/1.70  CNF conversion       : 0.03
% 3.69/1.70  Main loop            : 0.48
% 3.69/1.70  Inferencing          : 0.19
% 3.69/1.70  Reduction            : 0.13
% 3.69/1.70  Demodulation         : 0.10
% 3.69/1.70  BG Simplification    : 0.03
% 3.69/1.70  Subsumption          : 0.09
% 3.69/1.70  Abstraction          : 0.02
% 3.69/1.70  MUC search           : 0.00
% 3.69/1.70  Cooper               : 0.00
% 3.69/1.70  Total                : 0.89
% 3.69/1.70  Index Insertion      : 0.00
% 3.69/1.70  Index Deletion       : 0.00
% 3.69/1.70  Index Matching       : 0.00
% 3.69/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
