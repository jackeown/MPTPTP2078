%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:43 EST 2020

% Result     : Theorem 4.07s
% Output     : CNFRefutation 4.07s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 108 expanded)
%              Number of leaves         :   31 (  49 expanded)
%              Depth                    :    9
%              Number of atoms          :  103 ( 154 expanded)
%              Number of equality atoms :   28 (  46 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_68,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_64,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_56,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_48,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_76,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_32,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_453,plain,(
    ! [A_95,B_96,C_97] :
      ( r2_hidden('#skF_1'(A_95,B_96,C_97),B_96)
      | r2_hidden('#skF_2'(A_95,B_96,C_97),C_97)
      | k3_xboole_0(A_95,B_96) = C_97 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_601,plain,(
    ! [A_103,B_104] :
      ( r2_hidden('#skF_2'(A_103,B_104,B_104),B_104)
      | k3_xboole_0(A_103,B_104) = B_104 ) ),
    inference(resolution,[status(thm)],[c_453,c_14])).

tff(c_71,plain,(
    ! [A_33,B_34] : r1_xboole_0(k4_xboole_0(A_33,B_34),B_34) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_74,plain,(
    ! [A_18] : r1_xboole_0(A_18,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_71])).

tff(c_104,plain,(
    ! [A_44,B_45] :
      ( ~ r2_hidden(A_44,B_45)
      | ~ r1_xboole_0(k1_tarski(A_44),B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_118,plain,(
    ! [A_44] : ~ r2_hidden(A_44,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_74,c_104])).

tff(c_629,plain,(
    ! [A_105] : k3_xboole_0(A_105,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_601,c_118])).

tff(c_30,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_643,plain,(
    ! [A_105] : k5_xboole_0(A_105,k1_xboole_0) = k4_xboole_0(A_105,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_629,c_30])).

tff(c_659,plain,(
    ! [A_105] : k5_xboole_0(A_105,k1_xboole_0) = A_105 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_643])).

tff(c_28,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_4'(A_14),A_14)
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_151,plain,(
    ! [D_56,B_57,A_58] :
      ( r2_hidden(D_56,B_57)
      | ~ r2_hidden(D_56,k3_xboole_0(A_58,B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_156,plain,(
    ! [A_58,B_57] :
      ( r2_hidden('#skF_4'(k3_xboole_0(A_58,B_57)),B_57)
      | k3_xboole_0(A_58,B_57) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_151])).

tff(c_44,plain,(
    ! [A_29,B_30] :
      ( r1_xboole_0(k1_tarski(A_29),B_30)
      | r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_213,plain,(
    ! [A_67,B_68,C_69] :
      ( ~ r1_xboole_0(A_67,B_68)
      | ~ r2_hidden(C_69,B_68)
      | ~ r2_hidden(C_69,A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_283,plain,(
    ! [C_80,B_81,A_82] :
      ( ~ r2_hidden(C_80,B_81)
      | ~ r2_hidden(C_80,k1_tarski(A_82))
      | r2_hidden(A_82,B_81) ) ),
    inference(resolution,[status(thm)],[c_44,c_213])).

tff(c_842,plain,(
    ! [A_122,A_123] :
      ( ~ r2_hidden('#skF_4'(A_122),k1_tarski(A_123))
      | r2_hidden(A_123,A_122)
      | k1_xboole_0 = A_122 ) ),
    inference(resolution,[status(thm)],[c_28,c_283])).

tff(c_2116,plain,(
    ! [A_183,A_184] :
      ( r2_hidden(A_183,k3_xboole_0(A_184,k1_tarski(A_183)))
      | k3_xboole_0(A_184,k1_tarski(A_183)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_156,c_842])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2162,plain,(
    ! [A_185,A_186] :
      ( r2_hidden(A_185,A_186)
      | k3_xboole_0(A_186,k1_tarski(A_185)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2116,c_6])).

tff(c_2231,plain,(
    ! [A_186,A_185] :
      ( k4_xboole_0(A_186,k1_tarski(A_185)) = k5_xboole_0(A_186,k1_xboole_0)
      | r2_hidden(A_185,A_186) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2162,c_30])).

tff(c_2355,plain,(
    ! [A_190,A_191] :
      ( k4_xboole_0(A_190,k1_tarski(A_191)) = A_190
      | r2_hidden(A_191,A_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_659,c_2231])).

tff(c_46,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_90,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_2388,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2355,c_90])).

tff(c_2419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2388])).

tff(c_2420,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_2421,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_50,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2502,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2421,c_50])).

tff(c_34,plain,(
    ! [A_19,B_20] : r1_xboole_0(k4_xboole_0(A_19,B_20),B_20) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_78,plain,(
    ! [B_37,A_38] :
      ( r1_xboole_0(B_37,A_38)
      | ~ r1_xboole_0(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_84,plain,(
    ! [B_20,A_19] : r1_xboole_0(B_20,k4_xboole_0(A_19,B_20)) ),
    inference(resolution,[status(thm)],[c_34,c_78])).

tff(c_2462,plain,(
    ! [A_198,B_199] :
      ( ~ r2_hidden(A_198,B_199)
      | ~ r1_xboole_0(k1_tarski(A_198),B_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2478,plain,(
    ! [A_198,A_19] : ~ r2_hidden(A_198,k4_xboole_0(A_19,k1_tarski(A_198))) ),
    inference(resolution,[status(thm)],[c_84,c_2462])).

tff(c_2506,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2502,c_2478])).

tff(c_2517,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2420,c_2506])).

tff(c_2518,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2519,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_52,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2628,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2519,c_52])).

tff(c_2520,plain,(
    ! [B_205,A_206] :
      ( r1_xboole_0(B_205,A_206)
      | ~ r1_xboole_0(A_206,B_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2526,plain,(
    ! [B_20,A_19] : r1_xboole_0(B_20,k4_xboole_0(A_19,B_20)) ),
    inference(resolution,[status(thm)],[c_34,c_2520])).

tff(c_2542,plain,(
    ! [A_211,B_212] :
      ( ~ r2_hidden(A_211,B_212)
      | ~ r1_xboole_0(k1_tarski(A_211),B_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2551,plain,(
    ! [A_211,A_19] : ~ r2_hidden(A_211,k4_xboole_0(A_19,k1_tarski(A_211))) ),
    inference(resolution,[status(thm)],[c_2526,c_2542])).

tff(c_2632,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2628,c_2551])).

tff(c_2643,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2518,c_2632])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:24:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.07/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.07/1.68  
% 4.07/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.07/1.69  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8
% 4.07/1.69  
% 4.07/1.69  %Foreground sorts:
% 4.07/1.69  
% 4.07/1.69  
% 4.07/1.69  %Background operators:
% 4.07/1.69  
% 4.07/1.69  
% 4.07/1.69  %Foreground operators:
% 4.07/1.69  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.07/1.69  tff('#skF_4', type, '#skF_4': $i > $i).
% 4.07/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.07/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.07/1.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.07/1.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.07/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.07/1.69  tff('#skF_7', type, '#skF_7': $i).
% 4.07/1.69  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.07/1.69  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.07/1.69  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.07/1.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.07/1.69  tff('#skF_5', type, '#skF_5': $i).
% 4.07/1.69  tff('#skF_6', type, '#skF_6': $i).
% 4.07/1.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.07/1.69  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.07/1.69  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.07/1.69  tff('#skF_8', type, '#skF_8': $i).
% 4.07/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.07/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.07/1.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.07/1.69  
% 4.07/1.70  tff(f_92, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 4.07/1.70  tff(f_68, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.07/1.70  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.07/1.70  tff(f_70, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.07/1.70  tff(f_81, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 4.07/1.70  tff(f_66, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.07/1.70  tff(f_64, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.07/1.70  tff(f_86, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 4.07/1.70  tff(f_56, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.07/1.70  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.07/1.70  tff(c_48, plain, (~r2_hidden('#skF_6', '#skF_5') | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.07/1.70  tff(c_76, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_48])).
% 4.07/1.70  tff(c_32, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.07/1.70  tff(c_453, plain, (![A_95, B_96, C_97]: (r2_hidden('#skF_1'(A_95, B_96, C_97), B_96) | r2_hidden('#skF_2'(A_95, B_96, C_97), C_97) | k3_xboole_0(A_95, B_96)=C_97)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.07/1.70  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.07/1.70  tff(c_601, plain, (![A_103, B_104]: (r2_hidden('#skF_2'(A_103, B_104, B_104), B_104) | k3_xboole_0(A_103, B_104)=B_104)), inference(resolution, [status(thm)], [c_453, c_14])).
% 4.07/1.70  tff(c_71, plain, (![A_33, B_34]: (r1_xboole_0(k4_xboole_0(A_33, B_34), B_34))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.07/1.70  tff(c_74, plain, (![A_18]: (r1_xboole_0(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_71])).
% 4.07/1.70  tff(c_104, plain, (![A_44, B_45]: (~r2_hidden(A_44, B_45) | ~r1_xboole_0(k1_tarski(A_44), B_45))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.07/1.70  tff(c_118, plain, (![A_44]: (~r2_hidden(A_44, k1_xboole_0))), inference(resolution, [status(thm)], [c_74, c_104])).
% 4.07/1.70  tff(c_629, plain, (![A_105]: (k3_xboole_0(A_105, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_601, c_118])).
% 4.07/1.70  tff(c_30, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.07/1.70  tff(c_643, plain, (![A_105]: (k5_xboole_0(A_105, k1_xboole_0)=k4_xboole_0(A_105, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_629, c_30])).
% 4.07/1.70  tff(c_659, plain, (![A_105]: (k5_xboole_0(A_105, k1_xboole_0)=A_105)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_643])).
% 4.07/1.70  tff(c_28, plain, (![A_14]: (r2_hidden('#skF_4'(A_14), A_14) | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.07/1.70  tff(c_151, plain, (![D_56, B_57, A_58]: (r2_hidden(D_56, B_57) | ~r2_hidden(D_56, k3_xboole_0(A_58, B_57)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.07/1.70  tff(c_156, plain, (![A_58, B_57]: (r2_hidden('#skF_4'(k3_xboole_0(A_58, B_57)), B_57) | k3_xboole_0(A_58, B_57)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_151])).
% 4.07/1.70  tff(c_44, plain, (![A_29, B_30]: (r1_xboole_0(k1_tarski(A_29), B_30) | r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.07/1.70  tff(c_213, plain, (![A_67, B_68, C_69]: (~r1_xboole_0(A_67, B_68) | ~r2_hidden(C_69, B_68) | ~r2_hidden(C_69, A_67))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.07/1.70  tff(c_283, plain, (![C_80, B_81, A_82]: (~r2_hidden(C_80, B_81) | ~r2_hidden(C_80, k1_tarski(A_82)) | r2_hidden(A_82, B_81))), inference(resolution, [status(thm)], [c_44, c_213])).
% 4.07/1.70  tff(c_842, plain, (![A_122, A_123]: (~r2_hidden('#skF_4'(A_122), k1_tarski(A_123)) | r2_hidden(A_123, A_122) | k1_xboole_0=A_122)), inference(resolution, [status(thm)], [c_28, c_283])).
% 4.07/1.70  tff(c_2116, plain, (![A_183, A_184]: (r2_hidden(A_183, k3_xboole_0(A_184, k1_tarski(A_183))) | k3_xboole_0(A_184, k1_tarski(A_183))=k1_xboole_0)), inference(resolution, [status(thm)], [c_156, c_842])).
% 4.07/1.70  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.07/1.70  tff(c_2162, plain, (![A_185, A_186]: (r2_hidden(A_185, A_186) | k3_xboole_0(A_186, k1_tarski(A_185))=k1_xboole_0)), inference(resolution, [status(thm)], [c_2116, c_6])).
% 4.07/1.70  tff(c_2231, plain, (![A_186, A_185]: (k4_xboole_0(A_186, k1_tarski(A_185))=k5_xboole_0(A_186, k1_xboole_0) | r2_hidden(A_185, A_186))), inference(superposition, [status(thm), theory('equality')], [c_2162, c_30])).
% 4.07/1.70  tff(c_2355, plain, (![A_190, A_191]: (k4_xboole_0(A_190, k1_tarski(A_191))=A_190 | r2_hidden(A_191, A_190))), inference(demodulation, [status(thm), theory('equality')], [c_659, c_2231])).
% 4.07/1.70  tff(c_46, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.07/1.70  tff(c_90, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_46])).
% 4.07/1.70  tff(c_2388, plain, (r2_hidden('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2355, c_90])).
% 4.07/1.70  tff(c_2419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_2388])).
% 4.07/1.70  tff(c_2420, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_46])).
% 4.07/1.70  tff(c_2421, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_46])).
% 4.07/1.70  tff(c_50, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.07/1.70  tff(c_2502, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2421, c_50])).
% 4.07/1.70  tff(c_34, plain, (![A_19, B_20]: (r1_xboole_0(k4_xboole_0(A_19, B_20), B_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.07/1.70  tff(c_78, plain, (![B_37, A_38]: (r1_xboole_0(B_37, A_38) | ~r1_xboole_0(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.07/1.70  tff(c_84, plain, (![B_20, A_19]: (r1_xboole_0(B_20, k4_xboole_0(A_19, B_20)))), inference(resolution, [status(thm)], [c_34, c_78])).
% 4.07/1.70  tff(c_2462, plain, (![A_198, B_199]: (~r2_hidden(A_198, B_199) | ~r1_xboole_0(k1_tarski(A_198), B_199))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.07/1.70  tff(c_2478, plain, (![A_198, A_19]: (~r2_hidden(A_198, k4_xboole_0(A_19, k1_tarski(A_198))))), inference(resolution, [status(thm)], [c_84, c_2462])).
% 4.07/1.70  tff(c_2506, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2502, c_2478])).
% 4.07/1.70  tff(c_2517, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2420, c_2506])).
% 4.07/1.70  tff(c_2518, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_48])).
% 4.07/1.70  tff(c_2519, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_48])).
% 4.07/1.70  tff(c_52, plain, (~r2_hidden('#skF_6', '#skF_5') | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.07/1.70  tff(c_2628, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2519, c_52])).
% 4.07/1.70  tff(c_2520, plain, (![B_205, A_206]: (r1_xboole_0(B_205, A_206) | ~r1_xboole_0(A_206, B_205))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.07/1.70  tff(c_2526, plain, (![B_20, A_19]: (r1_xboole_0(B_20, k4_xboole_0(A_19, B_20)))), inference(resolution, [status(thm)], [c_34, c_2520])).
% 4.07/1.70  tff(c_2542, plain, (![A_211, B_212]: (~r2_hidden(A_211, B_212) | ~r1_xboole_0(k1_tarski(A_211), B_212))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.07/1.70  tff(c_2551, plain, (![A_211, A_19]: (~r2_hidden(A_211, k4_xboole_0(A_19, k1_tarski(A_211))))), inference(resolution, [status(thm)], [c_2526, c_2542])).
% 4.07/1.70  tff(c_2632, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2628, c_2551])).
% 4.07/1.70  tff(c_2643, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2518, c_2632])).
% 4.07/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.07/1.70  
% 4.07/1.70  Inference rules
% 4.07/1.70  ----------------------
% 4.07/1.70  #Ref     : 0
% 4.07/1.70  #Sup     : 640
% 4.07/1.70  #Fact    : 0
% 4.07/1.70  #Define  : 0
% 4.07/1.70  #Split   : 2
% 4.07/1.70  #Chain   : 0
% 4.07/1.70  #Close   : 0
% 4.07/1.70  
% 4.07/1.70  Ordering : KBO
% 4.07/1.70  
% 4.07/1.70  Simplification rules
% 4.07/1.70  ----------------------
% 4.07/1.70  #Subsume      : 223
% 4.07/1.70  #Demod        : 99
% 4.07/1.70  #Tautology    : 173
% 4.07/1.70  #SimpNegUnit  : 33
% 4.07/1.70  #BackRed      : 2
% 4.07/1.70  
% 4.07/1.70  #Partial instantiations: 0
% 4.07/1.70  #Strategies tried      : 1
% 4.07/1.70  
% 4.07/1.70  Timing (in seconds)
% 4.07/1.70  ----------------------
% 4.07/1.71  Preprocessing        : 0.33
% 4.07/1.71  Parsing              : 0.17
% 4.07/1.71  CNF conversion       : 0.02
% 4.07/1.71  Main loop            : 0.61
% 4.07/1.71  Inferencing          : 0.24
% 4.07/1.71  Reduction            : 0.17
% 4.07/1.71  Demodulation         : 0.11
% 4.07/1.71  BG Simplification    : 0.03
% 4.07/1.71  Subsumption          : 0.13
% 4.07/1.71  Abstraction          : 0.03
% 4.07/1.71  MUC search           : 0.00
% 4.07/1.71  Cooper               : 0.00
% 4.07/1.71  Total                : 0.97
% 4.07/1.71  Index Insertion      : 0.00
% 4.07/1.71  Index Deletion       : 0.00
% 4.07/1.71  Index Matching       : 0.00
% 4.07/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
