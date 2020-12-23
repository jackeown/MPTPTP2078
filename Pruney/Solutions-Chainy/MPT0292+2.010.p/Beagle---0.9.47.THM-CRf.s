%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:36 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   52 (  53 expanded)
%              Number of leaves         :   31 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 (  54 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_64,axiom,(
    ! [A] : r1_tarski(k1_tarski(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_62,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_78,negated_conjecture,(
    ~ ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(c_40,plain,(
    ! [A_42] : r1_tarski(k1_tarski(A_42),k1_zfmisc_1(A_42)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_86,plain,(
    ! [A_62,B_63] : k3_tarski(k2_tarski(A_62,B_63)) = k2_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_95,plain,(
    ! [A_7] : k3_tarski(k1_tarski(A_7)) = k2_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_86])).

tff(c_98,plain,(
    ! [A_7] : k3_tarski(k1_tarski(A_7)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_95])).

tff(c_123,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(k3_tarski(A_67),k3_tarski(B_68))
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_144,plain,(
    ! [A_73,B_74] :
      ( r1_tarski(A_73,k3_tarski(B_74))
      | ~ r1_tarski(k1_tarski(A_73),B_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_123])).

tff(c_148,plain,(
    ! [A_42] : r1_tarski(A_42,k3_tarski(k1_zfmisc_1(A_42))) ),
    inference(resolution,[status(thm)],[c_40,c_144])).

tff(c_167,plain,(
    ! [A_77,B_78] :
      ( r2_hidden('#skF_3'(A_77,B_78),A_77)
      | r1_tarski(k3_tarski(A_77),B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    ! [C_39,A_35] :
      ( r1_tarski(C_39,A_35)
      | ~ r2_hidden(C_39,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_252,plain,(
    ! [A_99,B_100] :
      ( r1_tarski('#skF_3'(k1_zfmisc_1(A_99),B_100),A_99)
      | r1_tarski(k3_tarski(k1_zfmisc_1(A_99)),B_100) ) ),
    inference(resolution,[status(thm)],[c_167,c_26])).

tff(c_42,plain,(
    ! [A_43,B_44] :
      ( ~ r1_tarski('#skF_3'(A_43,B_44),B_44)
      | r1_tarski(k3_tarski(A_43),B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_270,plain,(
    ! [A_101] : r1_tarski(k3_tarski(k1_zfmisc_1(A_101)),A_101) ),
    inference(resolution,[status(thm)],[c_252,c_42])).

tff(c_108,plain,(
    ! [A_65,B_66] :
      ( r2_xboole_0(A_65,B_66)
      | B_66 = A_65
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [B_6,A_5] :
      ( ~ r2_xboole_0(B_6,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_120,plain,(
    ! [B_66,A_65] :
      ( ~ r1_tarski(B_66,A_65)
      | B_66 = A_65
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_108,c_10])).

tff(c_272,plain,(
    ! [A_101] :
      ( k3_tarski(k1_zfmisc_1(A_101)) = A_101
      | ~ r1_tarski(A_101,k3_tarski(k1_zfmisc_1(A_101))) ) ),
    inference(resolution,[status(thm)],[c_270,c_120])).

tff(c_275,plain,(
    ! [A_101] : k3_tarski(k1_zfmisc_1(A_101)) = A_101 ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_272])).

tff(c_48,plain,(
    k3_tarski(k1_zfmisc_1('#skF_4')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:38:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.29  
% 2.15/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.30  %$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.15/1.30  
% 2.15/1.30  %Foreground sorts:
% 2.15/1.30  
% 2.15/1.30  
% 2.15/1.30  %Background operators:
% 2.15/1.30  
% 2.15/1.30  
% 2.15/1.30  %Foreground operators:
% 2.15/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.15/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.15/1.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.15/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.15/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.15/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.15/1.30  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.15/1.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.15/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.15/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.15/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.15/1.30  
% 2.15/1.31  tff(f_64, axiom, (![A]: r1_tarski(k1_tarski(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 2.15/1.31  tff(f_34, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.15/1.31  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.15/1.31  tff(f_62, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.15/1.31  tff(f_75, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 2.15/1.31  tff(f_71, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 2.15/1.31  tff(f_60, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.15/1.31  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.15/1.31  tff(f_39, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_xboole_1)).
% 2.15/1.31  tff(f_78, negated_conjecture, ~(![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.15/1.31  tff(c_40, plain, (![A_42]: (r1_tarski(k1_tarski(A_42), k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.15/1.31  tff(c_8, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.15/1.31  tff(c_12, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.15/1.31  tff(c_86, plain, (![A_62, B_63]: (k3_tarski(k2_tarski(A_62, B_63))=k2_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.15/1.31  tff(c_95, plain, (![A_7]: (k3_tarski(k1_tarski(A_7))=k2_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_12, c_86])).
% 2.15/1.31  tff(c_98, plain, (![A_7]: (k3_tarski(k1_tarski(A_7))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_95])).
% 2.15/1.31  tff(c_123, plain, (![A_67, B_68]: (r1_tarski(k3_tarski(A_67), k3_tarski(B_68)) | ~r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.15/1.31  tff(c_144, plain, (![A_73, B_74]: (r1_tarski(A_73, k3_tarski(B_74)) | ~r1_tarski(k1_tarski(A_73), B_74))), inference(superposition, [status(thm), theory('equality')], [c_98, c_123])).
% 2.15/1.31  tff(c_148, plain, (![A_42]: (r1_tarski(A_42, k3_tarski(k1_zfmisc_1(A_42))))), inference(resolution, [status(thm)], [c_40, c_144])).
% 2.15/1.31  tff(c_167, plain, (![A_77, B_78]: (r2_hidden('#skF_3'(A_77, B_78), A_77) | r1_tarski(k3_tarski(A_77), B_78))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.15/1.31  tff(c_26, plain, (![C_39, A_35]: (r1_tarski(C_39, A_35) | ~r2_hidden(C_39, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.15/1.31  tff(c_252, plain, (![A_99, B_100]: (r1_tarski('#skF_3'(k1_zfmisc_1(A_99), B_100), A_99) | r1_tarski(k3_tarski(k1_zfmisc_1(A_99)), B_100))), inference(resolution, [status(thm)], [c_167, c_26])).
% 2.15/1.31  tff(c_42, plain, (![A_43, B_44]: (~r1_tarski('#skF_3'(A_43, B_44), B_44) | r1_tarski(k3_tarski(A_43), B_44))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.15/1.31  tff(c_270, plain, (![A_101]: (r1_tarski(k3_tarski(k1_zfmisc_1(A_101)), A_101))), inference(resolution, [status(thm)], [c_252, c_42])).
% 2.15/1.31  tff(c_108, plain, (![A_65, B_66]: (r2_xboole_0(A_65, B_66) | B_66=A_65 | ~r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.15/1.31  tff(c_10, plain, (![B_6, A_5]: (~r2_xboole_0(B_6, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.15/1.31  tff(c_120, plain, (![B_66, A_65]: (~r1_tarski(B_66, A_65) | B_66=A_65 | ~r1_tarski(A_65, B_66))), inference(resolution, [status(thm)], [c_108, c_10])).
% 2.15/1.31  tff(c_272, plain, (![A_101]: (k3_tarski(k1_zfmisc_1(A_101))=A_101 | ~r1_tarski(A_101, k3_tarski(k1_zfmisc_1(A_101))))), inference(resolution, [status(thm)], [c_270, c_120])).
% 2.15/1.31  tff(c_275, plain, (![A_101]: (k3_tarski(k1_zfmisc_1(A_101))=A_101)), inference(demodulation, [status(thm), theory('equality')], [c_148, c_272])).
% 2.15/1.31  tff(c_48, plain, (k3_tarski(k1_zfmisc_1('#skF_4'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.15/1.31  tff(c_286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_275, c_48])).
% 2.15/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.31  
% 2.15/1.31  Inference rules
% 2.15/1.31  ----------------------
% 2.15/1.31  #Ref     : 0
% 2.15/1.31  #Sup     : 50
% 2.15/1.31  #Fact    : 0
% 2.15/1.31  #Define  : 0
% 2.15/1.31  #Split   : 0
% 2.15/1.31  #Chain   : 0
% 2.15/1.31  #Close   : 0
% 2.15/1.31  
% 2.15/1.31  Ordering : KBO
% 2.15/1.31  
% 2.15/1.31  Simplification rules
% 2.15/1.31  ----------------------
% 2.15/1.31  #Subsume      : 1
% 2.15/1.31  #Demod        : 14
% 2.15/1.31  #Tautology    : 18
% 2.15/1.31  #SimpNegUnit  : 0
% 2.15/1.31  #BackRed      : 7
% 2.15/1.31  
% 2.15/1.31  #Partial instantiations: 0
% 2.15/1.31  #Strategies tried      : 1
% 2.15/1.31  
% 2.15/1.31  Timing (in seconds)
% 2.15/1.31  ----------------------
% 2.15/1.31  Preprocessing        : 0.34
% 2.15/1.31  Parsing              : 0.18
% 2.15/1.31  CNF conversion       : 0.02
% 2.15/1.31  Main loop            : 0.21
% 2.15/1.31  Inferencing          : 0.08
% 2.15/1.31  Reduction            : 0.06
% 2.15/1.31  Demodulation         : 0.05
% 2.15/1.31  BG Simplification    : 0.02
% 2.15/1.31  Subsumption          : 0.04
% 2.15/1.31  Abstraction          : 0.01
% 2.15/1.31  MUC search           : 0.00
% 2.15/1.31  Cooper               : 0.00
% 2.15/1.31  Total                : 0.57
% 2.15/1.31  Index Insertion      : 0.00
% 2.15/1.31  Index Deletion       : 0.00
% 2.15/1.31  Index Matching       : 0.00
% 2.15/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
