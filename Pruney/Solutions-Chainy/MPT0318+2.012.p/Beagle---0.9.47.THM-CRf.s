%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:03 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   55 (  64 expanded)
%              Number of leaves         :   29 (  35 expanded)
%              Depth                    :    6
%              Number of atoms          :   54 (  77 expanded)
%              Number of equality atoms :   36 (  59 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_78,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_60,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_62,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_52,plain,(
    ! [B_44] : k2_zfmisc_1(k1_xboole_0,B_44) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_8,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_128,plain,(
    ! [A_64,B_65,C_66] :
      ( ~ r1_xboole_0(A_64,B_65)
      | ~ r2_hidden(C_66,k3_xboole_0(A_64,B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_131,plain,(
    ! [A_6,C_66] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_66,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_128])).

tff(c_133,plain,(
    ! [C_66] : ~ r2_hidden(C_66,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_131])).

tff(c_54,plain,
    ( k2_zfmisc_1('#skF_4',k1_tarski('#skF_5')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_99,plain,(
    k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_140,plain,(
    ! [B_70,A_71] :
      ( k1_xboole_0 = B_70
      | k1_xboole_0 = A_71
      | k2_zfmisc_1(A_71,B_70) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_143,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_140])).

tff(c_152,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_143])).

tff(c_34,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_104,plain,(
    ! [A_59,B_60] : k1_enumset1(A_59,A_59,B_60) = k2_tarski(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16,plain,(
    ! [E_14,B_9,C_10] : r2_hidden(E_14,k1_enumset1(E_14,B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_122,plain,(
    ! [A_61,B_62] : r2_hidden(A_61,k2_tarski(A_61,B_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_16])).

tff(c_125,plain,(
    ! [A_15] : r2_hidden(A_15,k1_tarski(A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_122])).

tff(c_162,plain,(
    r2_hidden('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_125])).

tff(c_166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_162])).

tff(c_167,plain,(
    k2_zfmisc_1('#skF_4',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_209,plain,(
    ! [B_83,A_84] :
      ( k1_xboole_0 = B_83
      | k1_xboole_0 = A_84
      | k2_zfmisc_1(A_84,B_83) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_212,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_209])).

tff(c_221,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_212])).

tff(c_168,plain,(
    k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_226,plain,(
    k2_zfmisc_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_168])).

tff(c_230,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_226])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:58:55 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.21  
% 2.00/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.21  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.00/1.21  
% 2.00/1.21  %Foreground sorts:
% 2.00/1.21  
% 2.00/1.21  
% 2.00/1.21  %Background operators:
% 2.00/1.21  
% 2.00/1.21  
% 2.00/1.21  %Foreground operators:
% 2.00/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.00/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.00/1.21  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.00/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.00/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.00/1.21  tff('#skF_5', type, '#skF_5': $i).
% 2.00/1.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.00/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.00/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.00/1.21  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.00/1.21  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.00/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.00/1.21  tff('#skF_4', type, '#skF_4': $i).
% 2.00/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.00/1.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.00/1.21  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.00/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.00/1.21  
% 2.09/1.22  tff(f_78, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.09/1.22  tff(f_88, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 2.09/1.22  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.09/1.22  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.09/1.22  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.09/1.22  tff(f_60, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.09/1.22  tff(f_62, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.09/1.22  tff(f_58, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.09/1.22  tff(c_52, plain, (![B_44]: (k2_zfmisc_1(k1_xboole_0, B_44)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.09/1.22  tff(c_56, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.09/1.22  tff(c_8, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.09/1.22  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.09/1.22  tff(c_128, plain, (![A_64, B_65, C_66]: (~r1_xboole_0(A_64, B_65) | ~r2_hidden(C_66, k3_xboole_0(A_64, B_65)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.09/1.22  tff(c_131, plain, (![A_6, C_66]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_66, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_128])).
% 2.09/1.22  tff(c_133, plain, (![C_66]: (~r2_hidden(C_66, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_131])).
% 2.09/1.22  tff(c_54, plain, (k2_zfmisc_1('#skF_4', k1_tarski('#skF_5'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.09/1.22  tff(c_99, plain, (k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_54])).
% 2.09/1.22  tff(c_140, plain, (![B_70, A_71]: (k1_xboole_0=B_70 | k1_xboole_0=A_71 | k2_zfmisc_1(A_71, B_70)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.09/1.22  tff(c_143, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_99, c_140])).
% 2.09/1.22  tff(c_152, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_56, c_143])).
% 2.09/1.22  tff(c_34, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.09/1.22  tff(c_104, plain, (![A_59, B_60]: (k1_enumset1(A_59, A_59, B_60)=k2_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.09/1.22  tff(c_16, plain, (![E_14, B_9, C_10]: (r2_hidden(E_14, k1_enumset1(E_14, B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.09/1.22  tff(c_122, plain, (![A_61, B_62]: (r2_hidden(A_61, k2_tarski(A_61, B_62)))), inference(superposition, [status(thm), theory('equality')], [c_104, c_16])).
% 2.09/1.22  tff(c_125, plain, (![A_15]: (r2_hidden(A_15, k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_122])).
% 2.09/1.22  tff(c_162, plain, (r2_hidden('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_152, c_125])).
% 2.09/1.22  tff(c_166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133, c_162])).
% 2.09/1.22  tff(c_167, plain, (k2_zfmisc_1('#skF_4', k1_tarski('#skF_5'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 2.09/1.22  tff(c_209, plain, (![B_83, A_84]: (k1_xboole_0=B_83 | k1_xboole_0=A_84 | k2_zfmisc_1(A_84, B_83)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.09/1.22  tff(c_212, plain, (k1_tarski('#skF_5')=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_167, c_209])).
% 2.09/1.22  tff(c_221, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_56, c_212])).
% 2.09/1.22  tff(c_168, plain, (k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 2.09/1.22  tff(c_226, plain, (k2_zfmisc_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_221, c_168])).
% 2.09/1.22  tff(c_230, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_226])).
% 2.09/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.22  
% 2.09/1.22  Inference rules
% 2.09/1.22  ----------------------
% 2.09/1.22  #Ref     : 0
% 2.09/1.22  #Sup     : 39
% 2.09/1.22  #Fact    : 0
% 2.09/1.22  #Define  : 0
% 2.09/1.22  #Split   : 1
% 2.09/1.22  #Chain   : 0
% 2.09/1.22  #Close   : 0
% 2.09/1.22  
% 2.09/1.22  Ordering : KBO
% 2.09/1.22  
% 2.09/1.22  Simplification rules
% 2.09/1.22  ----------------------
% 2.09/1.22  #Subsume      : 0
% 2.09/1.22  #Demod        : 11
% 2.09/1.22  #Tautology    : 28
% 2.09/1.22  #SimpNegUnit  : 3
% 2.09/1.22  #BackRed      : 3
% 2.09/1.22  
% 2.09/1.22  #Partial instantiations: 0
% 2.09/1.22  #Strategies tried      : 1
% 2.09/1.22  
% 2.09/1.22  Timing (in seconds)
% 2.09/1.22  ----------------------
% 2.09/1.23  Preprocessing        : 0.32
% 2.09/1.23  Parsing              : 0.17
% 2.09/1.23  CNF conversion       : 0.02
% 2.09/1.23  Main loop            : 0.15
% 2.09/1.23  Inferencing          : 0.05
% 2.09/1.23  Reduction            : 0.05
% 2.09/1.23  Demodulation         : 0.04
% 2.09/1.23  BG Simplification    : 0.01
% 2.09/1.23  Subsumption          : 0.03
% 2.09/1.23  Abstraction          : 0.01
% 2.09/1.23  MUC search           : 0.00
% 2.09/1.23  Cooper               : 0.00
% 2.09/1.23  Total                : 0.50
% 2.09/1.23  Index Insertion      : 0.00
% 2.09/1.23  Index Deletion       : 0.00
% 2.09/1.23  Index Matching       : 0.00
% 2.09/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
