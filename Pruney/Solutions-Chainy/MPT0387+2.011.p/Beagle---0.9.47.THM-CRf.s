%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:12 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   52 (  71 expanded)
%              Number of leaves         :   23 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   62 (  93 expanded)
%              Number of equality atoms :   23 (  35 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_71,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_65,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( r2_hidden(k1_xboole_0,A)
       => k1_setfam_1(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_setfam_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_43,axiom,(
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

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_22,plain,(
    ! [A_18] : k5_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_16,plain,(
    ! [A_15] : r1_tarski(k1_xboole_0,A_15) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_37,plain,(
    ! [A_23,B_24] :
      ( k3_xboole_0(A_23,B_24) = A_23
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_41,plain,(
    ! [A_15] : k3_xboole_0(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_37])).

tff(c_62,plain,(
    ! [A_36,B_37] : k5_xboole_0(A_36,k3_xboole_0(A_36,B_37)) = k4_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_71,plain,(
    ! [A_15] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_62])).

tff(c_74,plain,(
    ! [A_15] : k4_xboole_0(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_71])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( r1_xboole_0(A_16,B_17)
      | k4_xboole_0(A_16,B_17) != A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_26,plain,(
    k1_setfam_1('#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    r2_hidden(k1_xboole_0,'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_50,plain,(
    ! [B_28,A_29] :
      ( r1_tarski(k1_setfam_1(B_28),A_29)
      | ~ r2_hidden(A_29,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,B_14) = A_13
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_184,plain,(
    ! [B_57,A_58] :
      ( k3_xboole_0(k1_setfam_1(B_57),A_58) = k1_setfam_1(B_57)
      | ~ r2_hidden(A_58,B_57) ) ),
    inference(resolution,[status(thm)],[c_50,c_14])).

tff(c_12,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_202,plain,(
    ! [B_57,A_58] :
      ( k5_xboole_0(k1_setfam_1(B_57),k1_setfam_1(B_57)) = k4_xboole_0(k1_setfam_1(B_57),A_58)
      | ~ r2_hidden(A_58,B_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_12])).

tff(c_209,plain,(
    ! [B_59,A_60] :
      ( k4_xboole_0(k1_setfam_1(B_59),A_60) = k1_xboole_0
      | ~ r2_hidden(A_60,B_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_202])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_82,plain,(
    ! [A_39,B_40,C_41] :
      ( ~ r1_xboole_0(A_39,B_40)
      | ~ r2_hidden(C_41,k3_xboole_0(A_39,B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_93,plain,(
    ! [A_15,C_41] :
      ( ~ r1_xboole_0(k1_xboole_0,A_15)
      | ~ r2_hidden(C_41,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_82])).

tff(c_101,plain,(
    ! [C_45] : ~ r2_hidden(C_45,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_112,plain,(
    ! [A_46] : r1_xboole_0(A_46,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_101])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = A_16
      | ~ r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_119,plain,(
    ! [A_46] : k4_xboole_0(A_46,k1_xboole_0) = A_46 ),
    inference(resolution,[status(thm)],[c_112,c_18])).

tff(c_239,plain,(
    ! [B_64] :
      ( k1_setfam_1(B_64) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,B_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_119])).

tff(c_242,plain,(
    k1_setfam_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_239])).

tff(c_246,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_242])).

tff(c_248,plain,(
    ! [A_65] : ~ r1_xboole_0(k1_xboole_0,A_65) ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_252,plain,(
    ! [B_17] : k4_xboole_0(k1_xboole_0,B_17) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_248])).

tff(c_256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_252])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:13:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.22  
% 1.81/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.22  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 1.81/1.22  
% 1.81/1.22  %Foreground sorts:
% 1.81/1.22  
% 1.81/1.22  
% 1.81/1.22  %Background operators:
% 1.81/1.22  
% 1.81/1.22  
% 1.81/1.22  %Foreground operators:
% 1.81/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.81/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.81/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.81/1.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.81/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.81/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.81/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.81/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.81/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.81/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.81/1.22  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.81/1.22  
% 2.05/1.23  tff(f_71, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.05/1.23  tff(f_65, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.05/1.23  tff(f_63, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.05/1.23  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.05/1.23  tff(f_69, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.05/1.23  tff(f_80, negated_conjecture, ~(![A]: (r2_hidden(k1_xboole_0, A) => (k1_setfam_1(A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_setfam_1)).
% 2.05/1.23  tff(f_75, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.05/1.23  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.05/1.23  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.05/1.23  tff(c_22, plain, (![A_18]: (k5_xboole_0(A_18, A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.05/1.23  tff(c_16, plain, (![A_15]: (r1_tarski(k1_xboole_0, A_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.05/1.23  tff(c_37, plain, (![A_23, B_24]: (k3_xboole_0(A_23, B_24)=A_23 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.05/1.23  tff(c_41, plain, (![A_15]: (k3_xboole_0(k1_xboole_0, A_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_37])).
% 2.05/1.23  tff(c_62, plain, (![A_36, B_37]: (k5_xboole_0(A_36, k3_xboole_0(A_36, B_37))=k4_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.05/1.23  tff(c_71, plain, (![A_15]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_15))), inference(superposition, [status(thm), theory('equality')], [c_41, c_62])).
% 2.05/1.23  tff(c_74, plain, (![A_15]: (k4_xboole_0(k1_xboole_0, A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_71])).
% 2.05/1.23  tff(c_20, plain, (![A_16, B_17]: (r1_xboole_0(A_16, B_17) | k4_xboole_0(A_16, B_17)!=A_16)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.05/1.23  tff(c_26, plain, (k1_setfam_1('#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.05/1.23  tff(c_28, plain, (r2_hidden(k1_xboole_0, '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.05/1.23  tff(c_50, plain, (![B_28, A_29]: (r1_tarski(k1_setfam_1(B_28), A_29) | ~r2_hidden(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.05/1.23  tff(c_14, plain, (![A_13, B_14]: (k3_xboole_0(A_13, B_14)=A_13 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.05/1.23  tff(c_184, plain, (![B_57, A_58]: (k3_xboole_0(k1_setfam_1(B_57), A_58)=k1_setfam_1(B_57) | ~r2_hidden(A_58, B_57))), inference(resolution, [status(thm)], [c_50, c_14])).
% 2.05/1.23  tff(c_12, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.05/1.23  tff(c_202, plain, (![B_57, A_58]: (k5_xboole_0(k1_setfam_1(B_57), k1_setfam_1(B_57))=k4_xboole_0(k1_setfam_1(B_57), A_58) | ~r2_hidden(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_184, c_12])).
% 2.05/1.23  tff(c_209, plain, (![B_59, A_60]: (k4_xboole_0(k1_setfam_1(B_59), A_60)=k1_xboole_0 | ~r2_hidden(A_60, B_59))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_202])).
% 2.05/1.23  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.05/1.23  tff(c_82, plain, (![A_39, B_40, C_41]: (~r1_xboole_0(A_39, B_40) | ~r2_hidden(C_41, k3_xboole_0(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.05/1.23  tff(c_93, plain, (![A_15, C_41]: (~r1_xboole_0(k1_xboole_0, A_15) | ~r2_hidden(C_41, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_41, c_82])).
% 2.05/1.23  tff(c_101, plain, (![C_45]: (~r2_hidden(C_45, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_93])).
% 2.05/1.23  tff(c_112, plain, (![A_46]: (r1_xboole_0(A_46, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_101])).
% 2.05/1.23  tff(c_18, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=A_16 | ~r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.05/1.23  tff(c_119, plain, (![A_46]: (k4_xboole_0(A_46, k1_xboole_0)=A_46)), inference(resolution, [status(thm)], [c_112, c_18])).
% 2.05/1.23  tff(c_239, plain, (![B_64]: (k1_setfam_1(B_64)=k1_xboole_0 | ~r2_hidden(k1_xboole_0, B_64))), inference(superposition, [status(thm), theory('equality')], [c_209, c_119])).
% 2.05/1.23  tff(c_242, plain, (k1_setfam_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_239])).
% 2.05/1.23  tff(c_246, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_242])).
% 2.05/1.23  tff(c_248, plain, (![A_65]: (~r1_xboole_0(k1_xboole_0, A_65))), inference(splitRight, [status(thm)], [c_93])).
% 2.05/1.23  tff(c_252, plain, (![B_17]: (k4_xboole_0(k1_xboole_0, B_17)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_248])).
% 2.05/1.23  tff(c_256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_252])).
% 2.05/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.23  
% 2.05/1.23  Inference rules
% 2.05/1.23  ----------------------
% 2.05/1.23  #Ref     : 0
% 2.05/1.23  #Sup     : 51
% 2.05/1.23  #Fact    : 0
% 2.05/1.23  #Define  : 0
% 2.05/1.23  #Split   : 1
% 2.05/1.23  #Chain   : 0
% 2.05/1.23  #Close   : 0
% 2.05/1.23  
% 2.05/1.23  Ordering : KBO
% 2.05/1.23  
% 2.05/1.23  Simplification rules
% 2.05/1.23  ----------------------
% 2.05/1.23  #Subsume      : 4
% 2.05/1.23  #Demod        : 9
% 2.05/1.23  #Tautology    : 22
% 2.05/1.23  #SimpNegUnit  : 2
% 2.05/1.23  #BackRed      : 0
% 2.05/1.23  
% 2.05/1.23  #Partial instantiations: 0
% 2.05/1.23  #Strategies tried      : 1
% 2.05/1.23  
% 2.05/1.23  Timing (in seconds)
% 2.05/1.23  ----------------------
% 2.05/1.24  Preprocessing        : 0.28
% 2.05/1.24  Parsing              : 0.16
% 2.05/1.24  CNF conversion       : 0.02
% 2.05/1.24  Main loop            : 0.20
% 2.05/1.24  Inferencing          : 0.09
% 2.05/1.24  Reduction            : 0.05
% 2.05/1.24  Demodulation         : 0.04
% 2.05/1.24  BG Simplification    : 0.01
% 2.05/1.24  Subsumption          : 0.03
% 2.05/1.24  Abstraction          : 0.01
% 2.05/1.24  MUC search           : 0.00
% 2.05/1.24  Cooper               : 0.00
% 2.05/1.24  Total                : 0.51
% 2.05/1.24  Index Insertion      : 0.00
% 2.05/1.24  Index Deletion       : 0.00
% 2.05/1.24  Index Matching       : 0.00
% 2.05/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
