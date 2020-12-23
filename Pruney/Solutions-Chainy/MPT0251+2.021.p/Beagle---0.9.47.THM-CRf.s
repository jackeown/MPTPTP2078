%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:49 EST 2020

% Result     : Theorem 7.24s
% Output     : CNFRefutation 7.24s
% Verified   : 
% Statistics : Number of formulae       :   76 (  91 expanded)
%              Number of leaves         :   36 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :   87 ( 119 expanded)
%              Number of equality atoms :   34 (  41 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_59,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_49,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_55,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_83,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_66,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_40,plain,(
    ! [A_20] : k2_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_457,plain,(
    ! [D_88,A_89,B_90] :
      ( r2_hidden(D_88,A_89)
      | ~ r2_hidden(D_88,k4_xboole_0(A_89,B_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1281,plain,(
    ! [A_165,B_166] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_165,B_166)),A_165)
      | v1_xboole_0(k4_xboole_0(A_165,B_166)) ) ),
    inference(resolution,[status(thm)],[c_4,c_457])).

tff(c_209,plain,(
    ! [D_65,B_66,A_67] :
      ( ~ r2_hidden(D_65,B_66)
      | ~ r2_hidden(D_65,k4_xboole_0(A_67,B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_214,plain,(
    ! [A_67,B_66] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_67,B_66)),B_66)
      | v1_xboole_0(k4_xboole_0(A_67,B_66)) ) ),
    inference(resolution,[status(thm)],[c_4,c_209])).

tff(c_1319,plain,(
    ! [A_167] : v1_xboole_0(k4_xboole_0(A_167,A_167)) ),
    inference(resolution,[status(thm)],[c_1281,c_214])).

tff(c_30,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_341,plain,(
    ! [A_75,B_76] :
      ( r2_hidden('#skF_2'(A_75,B_76),A_75)
      | r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_350,plain,(
    ! [A_75,B_76] :
      ( ~ v1_xboole_0(A_75)
      | r1_tarski(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_341,c_2])).

tff(c_413,plain,(
    ! [B_84,A_85] :
      ( B_84 = A_85
      | ~ r1_tarski(B_84,A_85)
      | ~ r1_tarski(A_85,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_479,plain,(
    ! [B_91,A_92] :
      ( B_91 = A_92
      | ~ r1_tarski(B_91,A_92)
      | ~ v1_xboole_0(A_92) ) ),
    inference(resolution,[status(thm)],[c_350,c_413])).

tff(c_493,plain,(
    ! [B_93,A_94] :
      ( B_93 = A_94
      | ~ v1_xboole_0(B_93)
      | ~ v1_xboole_0(A_94) ) ),
    inference(resolution,[status(thm)],[c_350,c_479])).

tff(c_496,plain,(
    ! [A_94] :
      ( k1_xboole_0 = A_94
      | ~ v1_xboole_0(A_94) ) ),
    inference(resolution,[status(thm)],[c_30,c_493])).

tff(c_1337,plain,(
    ! [A_167] : k4_xboole_0(A_167,A_167) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1319,c_496])).

tff(c_36,plain,(
    ! [B_17] : r1_tarski(B_17,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_185,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(A_60,B_61) = A_60
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_193,plain,(
    ! [B_17] : k3_xboole_0(B_17,B_17) = B_17 ),
    inference(resolution,[status(thm)],[c_36,c_185])).

tff(c_328,plain,(
    ! [A_73,B_74] : k5_xboole_0(A_73,k3_xboole_0(A_73,B_74)) = k4_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_337,plain,(
    ! [B_17] : k5_xboole_0(B_17,B_17) = k4_xboole_0(B_17,B_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_328])).

tff(c_60,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(k1_tarski(A_39),B_40)
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1072,plain,(
    ! [A_144,B_145] :
      ( k3_xboole_0(k1_tarski(A_144),B_145) = k1_tarski(A_144)
      | ~ r2_hidden(A_144,B_145) ) ),
    inference(resolution,[status(thm)],[c_60,c_185])).

tff(c_38,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k3_xboole_0(A_18,B_19)) = k4_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1078,plain,(
    ! [A_144,B_145] :
      ( k5_xboole_0(k1_tarski(A_144),k1_tarski(A_144)) = k4_xboole_0(k1_tarski(A_144),B_145)
      | ~ r2_hidden(A_144,B_145) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1072,c_38])).

tff(c_1091,plain,(
    ! [A_144,B_145] :
      ( k4_xboole_0(k1_tarski(A_144),k1_tarski(A_144)) = k4_xboole_0(k1_tarski(A_144),B_145)
      | ~ r2_hidden(A_144,B_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_1078])).

tff(c_7982,plain,(
    ! [A_507,B_508] :
      ( k4_xboole_0(k1_tarski(A_507),B_508) = k1_xboole_0
      | ~ r2_hidden(A_507,B_508) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1337,c_1091])).

tff(c_44,plain,(
    ! [A_23,B_24] : k2_xboole_0(A_23,k4_xboole_0(B_24,A_23)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8199,plain,(
    ! [B_508,A_507] :
      ( k2_xboole_0(B_508,k1_tarski(A_507)) = k2_xboole_0(B_508,k1_xboole_0)
      | ~ r2_hidden(A_507,B_508) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7982,c_44])).

tff(c_8258,plain,(
    ! [B_509,A_510] :
      ( k2_xboole_0(B_509,k1_tarski(A_510)) = B_509
      | ~ r2_hidden(A_510,B_509) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8199])).

tff(c_48,plain,(
    ! [B_28,A_27] : k2_tarski(B_28,A_27) = k2_tarski(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_130,plain,(
    ! [A_51,B_52] : k3_tarski(k2_tarski(A_51,B_52)) = k2_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_215,plain,(
    ! [A_68,B_69] : k3_tarski(k2_tarski(A_68,B_69)) = k2_xboole_0(B_69,A_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_130])).

tff(c_62,plain,(
    ! [A_41,B_42] : k3_tarski(k2_tarski(A_41,B_42)) = k2_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_221,plain,(
    ! [B_69,A_68] : k2_xboole_0(B_69,A_68) = k2_xboole_0(A_68,B_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_62])).

tff(c_64,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_241,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_64])).

tff(c_8276,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_8258,c_241])).

tff(c_8321,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_8276])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:58:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.24/2.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.24/2.52  
% 7.24/2.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.24/2.52  %$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2
% 7.24/2.52  
% 7.24/2.52  %Foreground sorts:
% 7.24/2.52  
% 7.24/2.52  
% 7.24/2.52  %Background operators:
% 7.24/2.52  
% 7.24/2.52  
% 7.24/2.52  %Foreground operators:
% 7.24/2.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.24/2.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.24/2.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.24/2.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.24/2.52  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.24/2.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.24/2.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.24/2.52  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.24/2.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.24/2.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.24/2.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.24/2.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.24/2.52  tff('#skF_5', type, '#skF_5': $i).
% 7.24/2.52  tff('#skF_6', type, '#skF_6': $i).
% 7.24/2.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.24/2.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.24/2.52  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.24/2.52  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.24/2.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.24/2.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.24/2.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.24/2.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.24/2.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.24/2.52  
% 7.24/2.54  tff(f_88, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 7.24/2.54  tff(f_59, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 7.24/2.54  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.24/2.54  tff(f_48, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 7.24/2.54  tff(f_49, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.24/2.54  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.24/2.54  tff(f_55, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.24/2.54  tff(f_63, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.24/2.54  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.24/2.54  tff(f_81, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 7.24/2.54  tff(f_65, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 7.24/2.54  tff(f_69, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.24/2.54  tff(f_83, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 7.24/2.54  tff(c_66, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.24/2.54  tff(c_40, plain, (![A_20]: (k2_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.24/2.54  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.24/2.54  tff(c_457, plain, (![D_88, A_89, B_90]: (r2_hidden(D_88, A_89) | ~r2_hidden(D_88, k4_xboole_0(A_89, B_90)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.24/2.54  tff(c_1281, plain, (![A_165, B_166]: (r2_hidden('#skF_1'(k4_xboole_0(A_165, B_166)), A_165) | v1_xboole_0(k4_xboole_0(A_165, B_166)))), inference(resolution, [status(thm)], [c_4, c_457])).
% 7.24/2.54  tff(c_209, plain, (![D_65, B_66, A_67]: (~r2_hidden(D_65, B_66) | ~r2_hidden(D_65, k4_xboole_0(A_67, B_66)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.24/2.54  tff(c_214, plain, (![A_67, B_66]: (~r2_hidden('#skF_1'(k4_xboole_0(A_67, B_66)), B_66) | v1_xboole_0(k4_xboole_0(A_67, B_66)))), inference(resolution, [status(thm)], [c_4, c_209])).
% 7.24/2.54  tff(c_1319, plain, (![A_167]: (v1_xboole_0(k4_xboole_0(A_167, A_167)))), inference(resolution, [status(thm)], [c_1281, c_214])).
% 7.24/2.54  tff(c_30, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.24/2.54  tff(c_341, plain, (![A_75, B_76]: (r2_hidden('#skF_2'(A_75, B_76), A_75) | r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.24/2.54  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.24/2.54  tff(c_350, plain, (![A_75, B_76]: (~v1_xboole_0(A_75) | r1_tarski(A_75, B_76))), inference(resolution, [status(thm)], [c_341, c_2])).
% 7.24/2.54  tff(c_413, plain, (![B_84, A_85]: (B_84=A_85 | ~r1_tarski(B_84, A_85) | ~r1_tarski(A_85, B_84))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.24/2.54  tff(c_479, plain, (![B_91, A_92]: (B_91=A_92 | ~r1_tarski(B_91, A_92) | ~v1_xboole_0(A_92))), inference(resolution, [status(thm)], [c_350, c_413])).
% 7.24/2.54  tff(c_493, plain, (![B_93, A_94]: (B_93=A_94 | ~v1_xboole_0(B_93) | ~v1_xboole_0(A_94))), inference(resolution, [status(thm)], [c_350, c_479])).
% 7.24/2.54  tff(c_496, plain, (![A_94]: (k1_xboole_0=A_94 | ~v1_xboole_0(A_94))), inference(resolution, [status(thm)], [c_30, c_493])).
% 7.24/2.54  tff(c_1337, plain, (![A_167]: (k4_xboole_0(A_167, A_167)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1319, c_496])).
% 7.24/2.54  tff(c_36, plain, (![B_17]: (r1_tarski(B_17, B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.24/2.54  tff(c_185, plain, (![A_60, B_61]: (k3_xboole_0(A_60, B_61)=A_60 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.24/2.54  tff(c_193, plain, (![B_17]: (k3_xboole_0(B_17, B_17)=B_17)), inference(resolution, [status(thm)], [c_36, c_185])).
% 7.24/2.54  tff(c_328, plain, (![A_73, B_74]: (k5_xboole_0(A_73, k3_xboole_0(A_73, B_74))=k4_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.24/2.54  tff(c_337, plain, (![B_17]: (k5_xboole_0(B_17, B_17)=k4_xboole_0(B_17, B_17))), inference(superposition, [status(thm), theory('equality')], [c_193, c_328])).
% 7.24/2.54  tff(c_60, plain, (![A_39, B_40]: (r1_tarski(k1_tarski(A_39), B_40) | ~r2_hidden(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.24/2.54  tff(c_1072, plain, (![A_144, B_145]: (k3_xboole_0(k1_tarski(A_144), B_145)=k1_tarski(A_144) | ~r2_hidden(A_144, B_145))), inference(resolution, [status(thm)], [c_60, c_185])).
% 7.24/2.54  tff(c_38, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k3_xboole_0(A_18, B_19))=k4_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.24/2.54  tff(c_1078, plain, (![A_144, B_145]: (k5_xboole_0(k1_tarski(A_144), k1_tarski(A_144))=k4_xboole_0(k1_tarski(A_144), B_145) | ~r2_hidden(A_144, B_145))), inference(superposition, [status(thm), theory('equality')], [c_1072, c_38])).
% 7.24/2.54  tff(c_1091, plain, (![A_144, B_145]: (k4_xboole_0(k1_tarski(A_144), k1_tarski(A_144))=k4_xboole_0(k1_tarski(A_144), B_145) | ~r2_hidden(A_144, B_145))), inference(demodulation, [status(thm), theory('equality')], [c_337, c_1078])).
% 7.24/2.54  tff(c_7982, plain, (![A_507, B_508]: (k4_xboole_0(k1_tarski(A_507), B_508)=k1_xboole_0 | ~r2_hidden(A_507, B_508))), inference(demodulation, [status(thm), theory('equality')], [c_1337, c_1091])).
% 7.24/2.54  tff(c_44, plain, (![A_23, B_24]: (k2_xboole_0(A_23, k4_xboole_0(B_24, A_23))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.24/2.54  tff(c_8199, plain, (![B_508, A_507]: (k2_xboole_0(B_508, k1_tarski(A_507))=k2_xboole_0(B_508, k1_xboole_0) | ~r2_hidden(A_507, B_508))), inference(superposition, [status(thm), theory('equality')], [c_7982, c_44])).
% 7.24/2.54  tff(c_8258, plain, (![B_509, A_510]: (k2_xboole_0(B_509, k1_tarski(A_510))=B_509 | ~r2_hidden(A_510, B_509))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_8199])).
% 7.24/2.54  tff(c_48, plain, (![B_28, A_27]: (k2_tarski(B_28, A_27)=k2_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.24/2.54  tff(c_130, plain, (![A_51, B_52]: (k3_tarski(k2_tarski(A_51, B_52))=k2_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.24/2.54  tff(c_215, plain, (![A_68, B_69]: (k3_tarski(k2_tarski(A_68, B_69))=k2_xboole_0(B_69, A_68))), inference(superposition, [status(thm), theory('equality')], [c_48, c_130])).
% 7.24/2.54  tff(c_62, plain, (![A_41, B_42]: (k3_tarski(k2_tarski(A_41, B_42))=k2_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.24/2.54  tff(c_221, plain, (![B_69, A_68]: (k2_xboole_0(B_69, A_68)=k2_xboole_0(A_68, B_69))), inference(superposition, [status(thm), theory('equality')], [c_215, c_62])).
% 7.24/2.54  tff(c_64, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.24/2.54  tff(c_241, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_221, c_64])).
% 7.24/2.54  tff(c_8276, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_8258, c_241])).
% 7.24/2.54  tff(c_8321, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_8276])).
% 7.24/2.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.24/2.54  
% 7.24/2.54  Inference rules
% 7.24/2.54  ----------------------
% 7.24/2.54  #Ref     : 0
% 7.24/2.54  #Sup     : 2004
% 7.24/2.54  #Fact    : 0
% 7.24/2.54  #Define  : 0
% 7.24/2.54  #Split   : 8
% 7.24/2.54  #Chain   : 0
% 7.24/2.54  #Close   : 0
% 7.24/2.54  
% 7.24/2.54  Ordering : KBO
% 7.24/2.54  
% 7.24/2.54  Simplification rules
% 7.24/2.54  ----------------------
% 7.24/2.54  #Subsume      : 919
% 7.24/2.54  #Demod        : 761
% 7.24/2.54  #Tautology    : 498
% 7.24/2.54  #SimpNegUnit  : 51
% 7.24/2.54  #BackRed      : 33
% 7.24/2.54  
% 7.24/2.54  #Partial instantiations: 0
% 7.24/2.54  #Strategies tried      : 1
% 7.24/2.54  
% 7.24/2.54  Timing (in seconds)
% 7.24/2.54  ----------------------
% 7.24/2.54  Preprocessing        : 0.32
% 7.24/2.54  Parsing              : 0.17
% 7.24/2.54  CNF conversion       : 0.02
% 7.24/2.54  Main loop            : 1.41
% 7.24/2.54  Inferencing          : 0.46
% 7.24/2.54  Reduction            : 0.47
% 7.24/2.54  Demodulation         : 0.33
% 7.24/2.54  BG Simplification    : 0.05
% 7.24/2.54  Subsumption          : 0.34
% 7.24/2.54  Abstraction          : 0.07
% 7.24/2.54  MUC search           : 0.00
% 7.24/2.54  Cooper               : 0.00
% 7.24/2.54  Total                : 1.76
% 7.24/2.54  Index Insertion      : 0.00
% 7.24/2.54  Index Deletion       : 0.00
% 7.24/2.54  Index Matching       : 0.00
% 7.24/2.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
