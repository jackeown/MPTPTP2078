%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:38 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 117 expanded)
%              Number of leaves         :   33 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :   67 ( 169 expanded)
%              Number of equality atoms :   32 (  87 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(c_50,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_20,plain,(
    ! [C_18] : r2_hidden(C_18,k1_tarski(C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_65,plain,(
    ! [B_53,A_54] :
      ( ~ r2_hidden(B_53,A_54)
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_69,plain,(
    ! [C_18] : ~ v1_xboole_0(k1_tarski(C_18)) ),
    inference(resolution,[status(thm)],[c_20,c_65])).

tff(c_86,plain,(
    ! [A_59] :
      ( v1_xboole_0(A_59)
      | r2_hidden('#skF_1'(A_59),A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [C_18,A_14] :
      ( C_18 = A_14
      | ~ r2_hidden(C_18,k1_tarski(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_90,plain,(
    ! [A_14] :
      ( '#skF_1'(k1_tarski(A_14)) = A_14
      | v1_xboole_0(k1_tarski(A_14)) ) ),
    inference(resolution,[status(thm)],[c_86,c_18])).

tff(c_96,plain,(
    ! [A_14] : '#skF_1'(k1_tarski(A_14)) = A_14 ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_90])).

tff(c_52,plain,(
    r1_tarski(k1_tarski('#skF_4'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_191,plain,(
    ! [B_76,A_77] :
      ( k1_tarski(B_76) = A_77
      | k1_xboole_0 = A_77
      | ~ r1_tarski(A_77,k1_tarski(B_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_203,plain,
    ( k1_tarski('#skF_5') = k1_tarski('#skF_4')
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_191])).

tff(c_206,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_203])).

tff(c_232,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_69])).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_46,plain,(
    ! [B_48] : r1_tarski(k1_tarski(B_48),k1_tarski(B_48)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_127,plain,(
    ! [A_67,B_68] :
      ( k3_xboole_0(A_67,B_68) = A_67
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_137,plain,(
    ! [B_48] : k3_xboole_0(k1_tarski(B_48),k1_tarski(B_48)) = k1_tarski(B_48) ),
    inference(resolution,[status(thm)],[c_46,c_127])).

tff(c_222,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_137])).

tff(c_248,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_206,c_222])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_283,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_6])).

tff(c_286,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_283])).

tff(c_48,plain,(
    ! [B_48] : r1_tarski(k1_xboole_0,k1_tarski(B_48)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_240,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_48])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( r1_xboole_0(A_12,B_13)
      | k4_xboole_0(A_12,B_13) != A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_186,plain,(
    ! [B_74,A_75] :
      ( ~ r1_xboole_0(B_74,A_75)
      | ~ r1_tarski(B_74,A_75)
      | v1_xboole_0(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_323,plain,(
    ! [A_87,B_88] :
      ( ~ r1_tarski(A_87,B_88)
      | v1_xboole_0(A_87)
      | k4_xboole_0(A_87,B_88) != A_87 ) ),
    inference(resolution,[status(thm)],[c_16,c_186])).

tff(c_326,plain,
    ( v1_xboole_0(k1_xboole_0)
    | k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_240,c_323])).

tff(c_335,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_326])).

tff(c_337,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_232,c_335])).

tff(c_338,plain,(
    k1_tarski('#skF_5') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_360,plain,(
    '#skF_1'(k1_tarski('#skF_4')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_96])).

tff(c_384,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_360])).

tff(c_386,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_384])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:02:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.28  
% 2.23/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.28  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 2.23/1.28  
% 2.23/1.28  %Foreground sorts:
% 2.23/1.28  
% 2.23/1.28  
% 2.23/1.28  %Background operators:
% 2.23/1.28  
% 2.23/1.28  
% 2.23/1.28  %Foreground operators:
% 2.23/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.23/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.23/1.28  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.23/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.23/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.23/1.28  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.23/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.23/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.23/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.23/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.23/1.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.23/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.23/1.28  
% 2.23/1.29  tff(f_83, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.23/1.29  tff(f_58, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.23/1.29  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.23/1.29  tff(f_78, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.23/1.29  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.23/1.29  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.23/1.29  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.23/1.29  tff(f_51, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.23/1.29  tff(f_47, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.23/1.29  tff(c_50, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.23/1.29  tff(c_20, plain, (![C_18]: (r2_hidden(C_18, k1_tarski(C_18)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.23/1.29  tff(c_65, plain, (![B_53, A_54]: (~r2_hidden(B_53, A_54) | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.23/1.29  tff(c_69, plain, (![C_18]: (~v1_xboole_0(k1_tarski(C_18)))), inference(resolution, [status(thm)], [c_20, c_65])).
% 2.23/1.29  tff(c_86, plain, (![A_59]: (v1_xboole_0(A_59) | r2_hidden('#skF_1'(A_59), A_59))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.23/1.29  tff(c_18, plain, (![C_18, A_14]: (C_18=A_14 | ~r2_hidden(C_18, k1_tarski(A_14)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.23/1.29  tff(c_90, plain, (![A_14]: ('#skF_1'(k1_tarski(A_14))=A_14 | v1_xboole_0(k1_tarski(A_14)))), inference(resolution, [status(thm)], [c_86, c_18])).
% 2.23/1.29  tff(c_96, plain, (![A_14]: ('#skF_1'(k1_tarski(A_14))=A_14)), inference(negUnitSimplification, [status(thm)], [c_69, c_90])).
% 2.23/1.29  tff(c_52, plain, (r1_tarski(k1_tarski('#skF_4'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.23/1.29  tff(c_191, plain, (![B_76, A_77]: (k1_tarski(B_76)=A_77 | k1_xboole_0=A_77 | ~r1_tarski(A_77, k1_tarski(B_76)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.23/1.29  tff(c_203, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_4') | k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_191])).
% 2.23/1.29  tff(c_206, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_203])).
% 2.23/1.29  tff(c_232, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_206, c_69])).
% 2.23/1.29  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.23/1.29  tff(c_46, plain, (![B_48]: (r1_tarski(k1_tarski(B_48), k1_tarski(B_48)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.23/1.29  tff(c_127, plain, (![A_67, B_68]: (k3_xboole_0(A_67, B_68)=A_67 | ~r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.23/1.29  tff(c_137, plain, (![B_48]: (k3_xboole_0(k1_tarski(B_48), k1_tarski(B_48))=k1_tarski(B_48))), inference(resolution, [status(thm)], [c_46, c_127])).
% 2.23/1.29  tff(c_222, plain, (k3_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_206, c_137])).
% 2.23/1.29  tff(c_248, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_206, c_206, c_222])).
% 2.23/1.29  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.23/1.29  tff(c_283, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_248, c_6])).
% 2.23/1.29  tff(c_286, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10, c_283])).
% 2.23/1.29  tff(c_48, plain, (![B_48]: (r1_tarski(k1_xboole_0, k1_tarski(B_48)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.23/1.29  tff(c_240, plain, (r1_tarski(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_206, c_48])).
% 2.23/1.29  tff(c_16, plain, (![A_12, B_13]: (r1_xboole_0(A_12, B_13) | k4_xboole_0(A_12, B_13)!=A_12)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.23/1.29  tff(c_186, plain, (![B_74, A_75]: (~r1_xboole_0(B_74, A_75) | ~r1_tarski(B_74, A_75) | v1_xboole_0(B_74))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.23/1.29  tff(c_323, plain, (![A_87, B_88]: (~r1_tarski(A_87, B_88) | v1_xboole_0(A_87) | k4_xboole_0(A_87, B_88)!=A_87)), inference(resolution, [status(thm)], [c_16, c_186])).
% 2.23/1.29  tff(c_326, plain, (v1_xboole_0(k1_xboole_0) | k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_240, c_323])).
% 2.23/1.29  tff(c_335, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_286, c_326])).
% 2.23/1.29  tff(c_337, plain, $false, inference(negUnitSimplification, [status(thm)], [c_232, c_335])).
% 2.23/1.29  tff(c_338, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_203])).
% 2.23/1.29  tff(c_360, plain, ('#skF_1'(k1_tarski('#skF_4'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_338, c_96])).
% 2.23/1.29  tff(c_384, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_360])).
% 2.23/1.29  tff(c_386, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_384])).
% 2.23/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.29  
% 2.23/1.29  Inference rules
% 2.23/1.29  ----------------------
% 2.23/1.29  #Ref     : 0
% 2.23/1.29  #Sup     : 82
% 2.23/1.29  #Fact    : 0
% 2.23/1.29  #Define  : 0
% 2.23/1.29  #Split   : 1
% 2.23/1.29  #Chain   : 0
% 2.23/1.29  #Close   : 0
% 2.23/1.29  
% 2.23/1.29  Ordering : KBO
% 2.23/1.29  
% 2.23/1.29  Simplification rules
% 2.23/1.29  ----------------------
% 2.23/1.29  #Subsume      : 2
% 2.23/1.29  #Demod        : 41
% 2.23/1.29  #Tautology    : 56
% 2.23/1.29  #SimpNegUnit  : 6
% 2.23/1.29  #BackRed      : 4
% 2.23/1.29  
% 2.23/1.29  #Partial instantiations: 0
% 2.23/1.29  #Strategies tried      : 1
% 2.23/1.29  
% 2.23/1.29  Timing (in seconds)
% 2.23/1.29  ----------------------
% 2.23/1.29  Preprocessing        : 0.33
% 2.23/1.29  Parsing              : 0.17
% 2.23/1.29  CNF conversion       : 0.02
% 2.23/1.29  Main loop            : 0.19
% 2.23/1.29  Inferencing          : 0.07
% 2.23/1.29  Reduction            : 0.07
% 2.23/1.29  Demodulation         : 0.04
% 2.23/1.29  BG Simplification    : 0.02
% 2.23/1.29  Subsumption          : 0.02
% 2.23/1.30  Abstraction          : 0.01
% 2.23/1.30  MUC search           : 0.00
% 2.23/1.30  Cooper               : 0.00
% 2.23/1.30  Total                : 0.55
% 2.23/1.30  Index Insertion      : 0.00
% 2.23/1.30  Index Deletion       : 0.00
% 2.23/1.30  Index Matching       : 0.00
% 2.23/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
