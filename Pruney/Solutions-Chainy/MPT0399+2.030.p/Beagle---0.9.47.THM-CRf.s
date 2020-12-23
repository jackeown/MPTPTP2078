%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:35 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   54 (  55 expanded)
%              Number of leaves         :   33 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   47 (  49 expanded)
%              Number of equality atoms :   24 (  25 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_46,plain,(
    r1_setfam_1('#skF_4',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_277,plain,(
    ! [A_97,B_98,C_99] :
      ( r2_hidden('#skF_3'(A_97,B_98,C_99),B_98)
      | ~ r2_hidden(C_99,A_97)
      | ~ r1_setfam_1(A_97,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_10,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_140,plain,(
    ! [A_74,B_75] : k3_xboole_0(k1_tarski(A_74),k2_tarski(A_74,B_75)) = k1_tarski(A_74) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_146,plain,(
    ! [A_74,B_75] : k5_xboole_0(k1_tarski(A_74),k1_tarski(A_74)) = k4_xboole_0(k1_tarski(A_74),k2_tarski(A_74,B_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_4])).

tff(c_156,plain,(
    ! [A_76,B_77] : k4_xboole_0(k1_tarski(A_76),k2_tarski(A_76,B_77)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_146])).

tff(c_163,plain,(
    ! [A_7] : k4_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_156])).

tff(c_30,plain,(
    ! [B_40] : k4_xboole_0(k1_tarski(B_40),k1_tarski(B_40)) != k1_tarski(B_40) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_166,plain,(
    ! [B_40] : k1_tarski(B_40) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_30])).

tff(c_105,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(k1_tarski(A_67),B_68)
      | ~ r2_hidden(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_114,plain,(
    ! [A_67] :
      ( k1_tarski(A_67) = k1_xboole_0
      | ~ r2_hidden(A_67,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_105,c_6])).

tff(c_174,plain,(
    ! [A_67] : ~ r2_hidden(A_67,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_114])).

tff(c_283,plain,(
    ! [C_100,A_101] :
      ( ~ r2_hidden(C_100,A_101)
      | ~ r1_setfam_1(A_101,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_277,c_174])).

tff(c_296,plain,(
    ! [A_102] :
      ( ~ r1_setfam_1(A_102,k1_xboole_0)
      | k1_xboole_0 = A_102 ) ),
    inference(resolution,[status(thm)],[c_2,c_283])).

tff(c_303,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_296])).

tff(c_309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_303])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:40:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.26  
% 2.23/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.26  %$ r2_hidden > r1_tarski > r1_setfam_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2
% 2.23/1.26  
% 2.23/1.26  %Foreground sorts:
% 2.23/1.26  
% 2.23/1.26  
% 2.23/1.26  %Background operators:
% 2.23/1.26  
% 2.23/1.26  
% 2.23/1.26  %Foreground operators:
% 2.23/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.26  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.23/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.23/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.23/1.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.23/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.23/1.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.23/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.23/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.23/1.26  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.26  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.26  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.23/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.23/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.26  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.23/1.26  
% 2.23/1.27  tff(f_85, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_setfam_1)).
% 2.23/1.27  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.23/1.27  tff(f_78, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 2.23/1.27  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.23/1.27  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.23/1.27  tff(f_61, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 2.23/1.27  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.23/1.27  tff(f_66, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.23/1.27  tff(f_59, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.23/1.27  tff(f_39, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.23/1.27  tff(c_44, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.23/1.27  tff(c_46, plain, (r1_setfam_1('#skF_4', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.23/1.27  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.23/1.27  tff(c_277, plain, (![A_97, B_98, C_99]: (r2_hidden('#skF_3'(A_97, B_98, C_99), B_98) | ~r2_hidden(C_99, A_97) | ~r1_setfam_1(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.23/1.27  tff(c_10, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.23/1.27  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.23/1.27  tff(c_140, plain, (![A_74, B_75]: (k3_xboole_0(k1_tarski(A_74), k2_tarski(A_74, B_75))=k1_tarski(A_74))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.23/1.27  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.23/1.27  tff(c_146, plain, (![A_74, B_75]: (k5_xboole_0(k1_tarski(A_74), k1_tarski(A_74))=k4_xboole_0(k1_tarski(A_74), k2_tarski(A_74, B_75)))), inference(superposition, [status(thm), theory('equality')], [c_140, c_4])).
% 2.23/1.27  tff(c_156, plain, (![A_76, B_77]: (k4_xboole_0(k1_tarski(A_76), k2_tarski(A_76, B_77))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_146])).
% 2.23/1.27  tff(c_163, plain, (![A_7]: (k4_xboole_0(k1_tarski(A_7), k1_tarski(A_7))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_156])).
% 2.23/1.27  tff(c_30, plain, (![B_40]: (k4_xboole_0(k1_tarski(B_40), k1_tarski(B_40))!=k1_tarski(B_40))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.23/1.27  tff(c_166, plain, (![B_40]: (k1_tarski(B_40)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_163, c_30])).
% 2.23/1.27  tff(c_105, plain, (![A_67, B_68]: (r1_tarski(k1_tarski(A_67), B_68) | ~r2_hidden(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.23/1.27  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.23/1.27  tff(c_114, plain, (![A_67]: (k1_tarski(A_67)=k1_xboole_0 | ~r2_hidden(A_67, k1_xboole_0))), inference(resolution, [status(thm)], [c_105, c_6])).
% 2.23/1.27  tff(c_174, plain, (![A_67]: (~r2_hidden(A_67, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_166, c_114])).
% 2.23/1.27  tff(c_283, plain, (![C_100, A_101]: (~r2_hidden(C_100, A_101) | ~r1_setfam_1(A_101, k1_xboole_0))), inference(resolution, [status(thm)], [c_277, c_174])).
% 2.23/1.27  tff(c_296, plain, (![A_102]: (~r1_setfam_1(A_102, k1_xboole_0) | k1_xboole_0=A_102)), inference(resolution, [status(thm)], [c_2, c_283])).
% 2.23/1.27  tff(c_303, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_46, c_296])).
% 2.23/1.27  tff(c_309, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_303])).
% 2.23/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.27  
% 2.23/1.27  Inference rules
% 2.23/1.27  ----------------------
% 2.23/1.27  #Ref     : 0
% 2.23/1.27  #Sup     : 56
% 2.23/1.27  #Fact    : 0
% 2.23/1.27  #Define  : 0
% 2.23/1.27  #Split   : 0
% 2.23/1.27  #Chain   : 0
% 2.23/1.27  #Close   : 0
% 2.23/1.27  
% 2.23/1.27  Ordering : KBO
% 2.23/1.27  
% 2.23/1.27  Simplification rules
% 2.23/1.27  ----------------------
% 2.23/1.27  #Subsume      : 0
% 2.23/1.27  #Demod        : 9
% 2.23/1.27  #Tautology    : 43
% 2.23/1.27  #SimpNegUnit  : 5
% 2.23/1.27  #BackRed      : 2
% 2.23/1.27  
% 2.23/1.27  #Partial instantiations: 0
% 2.23/1.27  #Strategies tried      : 1
% 2.23/1.27  
% 2.23/1.27  Timing (in seconds)
% 2.23/1.27  ----------------------
% 2.23/1.27  Preprocessing        : 0.34
% 2.23/1.27  Parsing              : 0.18
% 2.23/1.27  CNF conversion       : 0.02
% 2.23/1.28  Main loop            : 0.17
% 2.23/1.28  Inferencing          : 0.07
% 2.23/1.28  Reduction            : 0.05
% 2.23/1.28  Demodulation         : 0.04
% 2.23/1.28  BG Simplification    : 0.02
% 2.23/1.28  Subsumption          : 0.02
% 2.23/1.28  Abstraction          : 0.01
% 2.23/1.28  MUC search           : 0.00
% 2.23/1.28  Cooper               : 0.00
% 2.23/1.28  Total                : 0.54
% 2.23/1.28  Index Insertion      : 0.00
% 2.23/1.28  Index Deletion       : 0.00
% 2.23/1.28  Index Matching       : 0.00
% 2.23/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
