%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:41 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   71 (  88 expanded)
%              Number of leaves         :   32 (  43 expanded)
%              Depth                    :    7
%              Number of atoms          :   75 ( 110 expanded)
%              Number of equality atoms :   28 (  45 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

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

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_66,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_68,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_68,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_94,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_28,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_166,plain,(
    ! [A_67,B_68] :
      ( r1_xboole_0(k1_tarski(A_67),B_68)
      | r2_hidden(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_24,plain,(
    ! [B_10,A_9] :
      ( r1_xboole_0(B_10,A_9)
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_182,plain,(
    ! [B_71,A_72] :
      ( r1_xboole_0(B_71,k1_tarski(A_72))
      | r2_hidden(A_72,B_71) ) ),
    inference(resolution,[status(thm)],[c_166,c_24])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_328,plain,(
    ! [B_89,A_90] :
      ( k3_xboole_0(B_89,k1_tarski(A_90)) = k1_xboole_0
      | r2_hidden(A_90,B_89) ) ),
    inference(resolution,[status(thm)],[c_182,c_20])).

tff(c_26,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_340,plain,(
    ! [B_89,A_90] :
      ( k4_xboole_0(B_89,k1_tarski(A_90)) = k5_xboole_0(B_89,k1_xboole_0)
      | r2_hidden(A_90,B_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_328,c_26])).

tff(c_373,plain,(
    ! [B_94,A_95] :
      ( k4_xboole_0(B_94,k1_tarski(A_95)) = B_94
      | r2_hidden(A_95,B_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_340])).

tff(c_66,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_104,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_401,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_104])).

tff(c_421,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_401])).

tff(c_422,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_56,plain,(
    ! [A_23] : k2_tarski(A_23,A_23) = k1_tarski(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_550,plain,(
    ! [A_109,B_110] : k1_enumset1(A_109,A_109,B_110) = k2_tarski(A_109,B_110) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_34,plain,(
    ! [E_22,A_16,B_17] : r2_hidden(E_22,k1_enumset1(A_16,B_17,E_22)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_575,plain,(
    ! [B_114,A_115] : r2_hidden(B_114,k2_tarski(A_115,B_114)) ),
    inference(superposition,[status(thm),theory(equality)],[c_550,c_34])).

tff(c_578,plain,(
    ! [A_23] : r2_hidden(A_23,k1_tarski(A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_575])).

tff(c_423,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_70,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_488,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_70])).

tff(c_568,plain,(
    ! [D_111,B_112,A_113] :
      ( ~ r2_hidden(D_111,B_112)
      | ~ r2_hidden(D_111,k4_xboole_0(A_113,B_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_615,plain,(
    ! [D_127] :
      ( ~ r2_hidden(D_127,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_127,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_488,c_568])).

tff(c_619,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_578,c_615])).

tff(c_623,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_619])).

tff(c_624,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_632,plain,(
    ! [A_133,B_134] : k1_enumset1(A_133,A_133,B_134) = k2_tarski(A_133,B_134) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_655,plain,(
    ! [B_137,A_138] : r2_hidden(B_137,k2_tarski(A_138,B_137)) ),
    inference(superposition,[status(thm),theory(equality)],[c_632,c_34])).

tff(c_658,plain,(
    ! [A_23] : r2_hidden(A_23,k1_tarski(A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_655])).

tff(c_625,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_72,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_661,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_625,c_72])).

tff(c_766,plain,(
    ! [D_156,B_157,A_158] :
      ( ~ r2_hidden(D_156,B_157)
      | ~ r2_hidden(D_156,k4_xboole_0(A_158,B_157)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_770,plain,(
    ! [D_159] :
      ( ~ r2_hidden(D_159,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_159,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_661,c_766])).

tff(c_774,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_658,c_770])).

tff(c_778,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_774])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:00:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.43  
% 2.52/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.43  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 2.52/1.43  
% 2.52/1.43  %Foreground sorts:
% 2.52/1.43  
% 2.52/1.43  
% 2.52/1.43  %Background operators:
% 2.52/1.43  
% 2.52/1.43  
% 2.52/1.43  %Foreground operators:
% 2.52/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.52/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.52/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.52/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.52/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.52/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.52/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.52/1.43  tff('#skF_7', type, '#skF_7': $i).
% 2.52/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.52/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.52/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.52/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.52/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.52/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.52/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.52/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.52/1.43  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.52/1.43  tff('#skF_8', type, '#skF_8': $i).
% 2.52/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.52/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.52/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.52/1.43  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.52/1.43  
% 2.52/1.45  tff(f_83, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.52/1.45  tff(f_47, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.52/1.45  tff(f_77, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.52/1.45  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.52/1.45  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.52/1.45  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.52/1.45  tff(f_66, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.52/1.45  tff(f_68, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.52/1.45  tff(f_64, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.52/1.45  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.52/1.45  tff(c_68, plain, (~r2_hidden('#skF_6', '#skF_5') | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.52/1.45  tff(c_94, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_68])).
% 2.52/1.45  tff(c_28, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.52/1.45  tff(c_166, plain, (![A_67, B_68]: (r1_xboole_0(k1_tarski(A_67), B_68) | r2_hidden(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.52/1.45  tff(c_24, plain, (![B_10, A_9]: (r1_xboole_0(B_10, A_9) | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.52/1.45  tff(c_182, plain, (![B_71, A_72]: (r1_xboole_0(B_71, k1_tarski(A_72)) | r2_hidden(A_72, B_71))), inference(resolution, [status(thm)], [c_166, c_24])).
% 2.52/1.45  tff(c_20, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.52/1.45  tff(c_328, plain, (![B_89, A_90]: (k3_xboole_0(B_89, k1_tarski(A_90))=k1_xboole_0 | r2_hidden(A_90, B_89))), inference(resolution, [status(thm)], [c_182, c_20])).
% 2.52/1.45  tff(c_26, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.52/1.45  tff(c_340, plain, (![B_89, A_90]: (k4_xboole_0(B_89, k1_tarski(A_90))=k5_xboole_0(B_89, k1_xboole_0) | r2_hidden(A_90, B_89))), inference(superposition, [status(thm), theory('equality')], [c_328, c_26])).
% 2.52/1.45  tff(c_373, plain, (![B_94, A_95]: (k4_xboole_0(B_94, k1_tarski(A_95))=B_94 | r2_hidden(A_95, B_94))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_340])).
% 2.52/1.45  tff(c_66, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.52/1.45  tff(c_104, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_66])).
% 2.52/1.45  tff(c_401, plain, (r2_hidden('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_373, c_104])).
% 2.52/1.45  tff(c_421, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_401])).
% 2.52/1.45  tff(c_422, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_66])).
% 2.52/1.45  tff(c_56, plain, (![A_23]: (k2_tarski(A_23, A_23)=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.52/1.45  tff(c_550, plain, (![A_109, B_110]: (k1_enumset1(A_109, A_109, B_110)=k2_tarski(A_109, B_110))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.52/1.45  tff(c_34, plain, (![E_22, A_16, B_17]: (r2_hidden(E_22, k1_enumset1(A_16, B_17, E_22)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.52/1.45  tff(c_575, plain, (![B_114, A_115]: (r2_hidden(B_114, k2_tarski(A_115, B_114)))), inference(superposition, [status(thm), theory('equality')], [c_550, c_34])).
% 2.52/1.45  tff(c_578, plain, (![A_23]: (r2_hidden(A_23, k1_tarski(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_575])).
% 2.52/1.45  tff(c_423, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_66])).
% 2.52/1.45  tff(c_70, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.52/1.45  tff(c_488, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_423, c_70])).
% 2.52/1.45  tff(c_568, plain, (![D_111, B_112, A_113]: (~r2_hidden(D_111, B_112) | ~r2_hidden(D_111, k4_xboole_0(A_113, B_112)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.52/1.45  tff(c_615, plain, (![D_127]: (~r2_hidden(D_127, k1_tarski('#skF_8')) | ~r2_hidden(D_127, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_488, c_568])).
% 2.52/1.45  tff(c_619, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_578, c_615])).
% 2.52/1.45  tff(c_623, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_422, c_619])).
% 2.52/1.45  tff(c_624, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_68])).
% 2.52/1.45  tff(c_632, plain, (![A_133, B_134]: (k1_enumset1(A_133, A_133, B_134)=k2_tarski(A_133, B_134))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.52/1.45  tff(c_655, plain, (![B_137, A_138]: (r2_hidden(B_137, k2_tarski(A_138, B_137)))), inference(superposition, [status(thm), theory('equality')], [c_632, c_34])).
% 2.52/1.45  tff(c_658, plain, (![A_23]: (r2_hidden(A_23, k1_tarski(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_655])).
% 2.52/1.45  tff(c_625, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_68])).
% 2.52/1.45  tff(c_72, plain, (~r2_hidden('#skF_6', '#skF_5') | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.52/1.45  tff(c_661, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_625, c_72])).
% 2.52/1.45  tff(c_766, plain, (![D_156, B_157, A_158]: (~r2_hidden(D_156, B_157) | ~r2_hidden(D_156, k4_xboole_0(A_158, B_157)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.52/1.45  tff(c_770, plain, (![D_159]: (~r2_hidden(D_159, k1_tarski('#skF_8')) | ~r2_hidden(D_159, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_661, c_766])).
% 2.52/1.45  tff(c_774, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_658, c_770])).
% 2.52/1.45  tff(c_778, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_624, c_774])).
% 2.52/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.45  
% 2.52/1.45  Inference rules
% 2.52/1.45  ----------------------
% 2.52/1.45  #Ref     : 0
% 2.52/1.45  #Sup     : 178
% 2.52/1.45  #Fact    : 0
% 2.52/1.45  #Define  : 0
% 2.52/1.45  #Split   : 3
% 2.52/1.45  #Chain   : 0
% 2.52/1.45  #Close   : 0
% 2.52/1.45  
% 2.52/1.45  Ordering : KBO
% 2.52/1.45  
% 2.52/1.45  Simplification rules
% 2.52/1.45  ----------------------
% 2.52/1.45  #Subsume      : 16
% 2.52/1.45  #Demod        : 46
% 2.52/1.45  #Tautology    : 103
% 2.52/1.45  #SimpNegUnit  : 1
% 2.52/1.45  #BackRed      : 0
% 2.52/1.45  
% 2.52/1.45  #Partial instantiations: 0
% 2.52/1.45  #Strategies tried      : 1
% 2.52/1.45  
% 2.52/1.45  Timing (in seconds)
% 2.52/1.45  ----------------------
% 2.52/1.45  Preprocessing        : 0.34
% 2.52/1.45  Parsing              : 0.17
% 2.52/1.45  CNF conversion       : 0.03
% 2.52/1.45  Main loop            : 0.29
% 2.52/1.45  Inferencing          : 0.11
% 2.52/1.45  Reduction            : 0.09
% 2.52/1.45  Demodulation         : 0.06
% 2.52/1.45  BG Simplification    : 0.02
% 2.52/1.45  Subsumption          : 0.05
% 2.52/1.45  Abstraction          : 0.02
% 2.52/1.45  MUC search           : 0.00
% 2.52/1.45  Cooper               : 0.00
% 2.52/1.45  Total                : 0.66
% 2.52/1.45  Index Insertion      : 0.00
% 2.52/1.45  Index Deletion       : 0.00
% 2.52/1.45  Index Matching       : 0.00
% 2.52/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
