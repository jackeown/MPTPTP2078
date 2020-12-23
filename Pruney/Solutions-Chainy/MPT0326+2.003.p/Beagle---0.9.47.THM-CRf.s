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
% DateTime   : Thu Dec  3 09:54:28 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 113 expanded)
%              Number of leaves         :   21 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :   84 ( 212 expanded)
%              Number of equality atoms :   26 (  64 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B,C,D] :
            ( ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
              | r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(D,C)) )
           => r1_tarski(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
     => ( k2_zfmisc_1(A,B) = k1_xboole_0
        | ( r1_tarski(A,C)
          & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(c_32,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_28,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_30,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_zfmisc_1('#skF_4','#skF_3'))
    | r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_77,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_271,plain,(
    ! [B_49,D_50,A_51,C_52] :
      ( r1_tarski(B_49,D_50)
      | k2_zfmisc_1(A_51,B_49) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_51,B_49),k2_zfmisc_1(C_52,D_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_274,plain,
    ( r1_tarski('#skF_2','#skF_4')
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_77,c_271])).

tff(c_293,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_274])).

tff(c_18,plain,(
    ! [B_11,A_10] :
      ( k1_xboole_0 = B_11
      | k1_xboole_0 = A_10
      | k2_zfmisc_1(A_10,B_11) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_317,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_18])).

tff(c_319,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_317])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_123,plain,(
    ! [B_34,A_35] :
      ( ~ r1_xboole_0(B_34,A_35)
      | ~ r1_tarski(B_34,A_35)
      | v1_xboole_0(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_126,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_123])).

tff(c_129,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_126])).

tff(c_325,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_129])).

tff(c_334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_325])).

tff(c_335,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_317])).

tff(c_10,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_92,plain,(
    ! [A_28,B_29,C_30] :
      ( r1_tarski(A_28,B_29)
      | ~ r1_tarski(A_28,k3_xboole_0(B_29,C_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_101,plain,(
    ! [B_31,C_32] : r1_tarski(k3_xboole_0(B_31,C_32),B_31) ),
    inference(resolution,[status(thm)],[c_6,c_92])).

tff(c_110,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_101])).

tff(c_344,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_110])).

tff(c_363,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_28])).

tff(c_364,plain,(
    r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_507,plain,(
    ! [A_70,C_71,B_72,D_73] :
      ( r1_tarski(A_70,C_71)
      | k2_zfmisc_1(A_70,B_72) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_70,B_72),k2_zfmisc_1(C_71,D_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_510,plain,
    ( r1_tarski('#skF_2','#skF_4')
    | k2_zfmisc_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_364,c_507])).

tff(c_529,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_510])).

tff(c_553,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_529,c_18])).

tff(c_555,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_553])).

tff(c_369,plain,(
    ! [A_53,B_54,C_55] :
      ( r1_tarski(A_53,B_54)
      | ~ r1_tarski(A_53,k3_xboole_0(B_54,C_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_378,plain,(
    ! [B_56,C_57] : r1_tarski(k3_xboole_0(B_56,C_57),B_56) ),
    inference(resolution,[status(thm)],[c_6,c_369])).

tff(c_387,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_378])).

tff(c_563,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_555,c_387])).

tff(c_589,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_563,c_28])).

tff(c_590,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_553])).

tff(c_457,plain,(
    ! [B_63,A_64] :
      ( ~ r1_xboole_0(B_63,A_64)
      | ~ r1_tarski(B_63,A_64)
      | v1_xboole_0(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_460,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_457])).

tff(c_463,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_460])).

tff(c_595,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_463])).

tff(c_606,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_595])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n020.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 16:58:52 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.38  
% 2.73/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.38  %$ r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.73/1.38  
% 2.73/1.38  %Foreground sorts:
% 2.73/1.38  
% 2.73/1.38  
% 2.73/1.38  %Background operators:
% 2.73/1.38  
% 2.73/1.38  
% 2.73/1.38  %Foreground operators:
% 2.73/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.73/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.73/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.73/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.73/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.73/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.73/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.73/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.73/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.73/1.38  
% 2.73/1.40  tff(f_82, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B, C, D]: ((r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) | r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(D, C))) => r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_zfmisc_1)).
% 2.73/1.40  tff(f_71, axiom, (![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 2.73/1.40  tff(f_63, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.73/1.40  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.73/1.40  tff(f_49, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.73/1.40  tff(f_57, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.73/1.40  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.73/1.40  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 2.73/1.40  tff(c_32, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.73/1.40  tff(c_28, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.73/1.40  tff(c_30, plain, (r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_zfmisc_1('#skF_4', '#skF_3')) | r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.73/1.40  tff(c_77, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_30])).
% 2.73/1.40  tff(c_271, plain, (![B_49, D_50, A_51, C_52]: (r1_tarski(B_49, D_50) | k2_zfmisc_1(A_51, B_49)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_51, B_49), k2_zfmisc_1(C_52, D_50)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.73/1.40  tff(c_274, plain, (r1_tarski('#skF_2', '#skF_4') | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_77, c_271])).
% 2.73/1.40  tff(c_293, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_28, c_274])).
% 2.73/1.40  tff(c_18, plain, (![B_11, A_10]: (k1_xboole_0=B_11 | k1_xboole_0=A_10 | k2_zfmisc_1(A_10, B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.73/1.40  tff(c_317, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_293, c_18])).
% 2.73/1.40  tff(c_319, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_317])).
% 2.73/1.40  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.73/1.40  tff(c_12, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.73/1.40  tff(c_123, plain, (![B_34, A_35]: (~r1_xboole_0(B_34, A_35) | ~r1_tarski(B_34, A_35) | v1_xboole_0(B_34))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.73/1.40  tff(c_126, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0) | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_123])).
% 2.73/1.40  tff(c_129, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_126])).
% 2.73/1.40  tff(c_325, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_319, c_129])).
% 2.73/1.40  tff(c_334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_325])).
% 2.73/1.40  tff(c_335, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_317])).
% 2.73/1.40  tff(c_10, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.73/1.40  tff(c_92, plain, (![A_28, B_29, C_30]: (r1_tarski(A_28, B_29) | ~r1_tarski(A_28, k3_xboole_0(B_29, C_30)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.73/1.40  tff(c_101, plain, (![B_31, C_32]: (r1_tarski(k3_xboole_0(B_31, C_32), B_31))), inference(resolution, [status(thm)], [c_6, c_92])).
% 2.73/1.40  tff(c_110, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(superposition, [status(thm), theory('equality')], [c_10, c_101])).
% 2.73/1.40  tff(c_344, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_335, c_110])).
% 2.73/1.40  tff(c_363, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_344, c_28])).
% 2.73/1.40  tff(c_364, plain, (r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_zfmisc_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_30])).
% 2.73/1.40  tff(c_507, plain, (![A_70, C_71, B_72, D_73]: (r1_tarski(A_70, C_71) | k2_zfmisc_1(A_70, B_72)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_70, B_72), k2_zfmisc_1(C_71, D_73)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.73/1.40  tff(c_510, plain, (r1_tarski('#skF_2', '#skF_4') | k2_zfmisc_1('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_364, c_507])).
% 2.73/1.40  tff(c_529, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_28, c_510])).
% 2.73/1.40  tff(c_553, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_529, c_18])).
% 2.73/1.40  tff(c_555, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_553])).
% 2.73/1.40  tff(c_369, plain, (![A_53, B_54, C_55]: (r1_tarski(A_53, B_54) | ~r1_tarski(A_53, k3_xboole_0(B_54, C_55)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.73/1.40  tff(c_378, plain, (![B_56, C_57]: (r1_tarski(k3_xboole_0(B_56, C_57), B_56))), inference(resolution, [status(thm)], [c_6, c_369])).
% 2.73/1.40  tff(c_387, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(superposition, [status(thm), theory('equality')], [c_10, c_378])).
% 2.73/1.40  tff(c_563, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_555, c_387])).
% 2.73/1.40  tff(c_589, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_563, c_28])).
% 2.73/1.40  tff(c_590, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_553])).
% 2.73/1.40  tff(c_457, plain, (![B_63, A_64]: (~r1_xboole_0(B_63, A_64) | ~r1_tarski(B_63, A_64) | v1_xboole_0(B_63))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.73/1.40  tff(c_460, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0) | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_457])).
% 2.73/1.40  tff(c_463, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_460])).
% 2.73/1.40  tff(c_595, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_590, c_463])).
% 2.73/1.40  tff(c_606, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_595])).
% 2.73/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.40  
% 2.73/1.40  Inference rules
% 2.73/1.40  ----------------------
% 2.73/1.40  #Ref     : 0
% 2.73/1.40  #Sup     : 110
% 2.73/1.40  #Fact    : 0
% 2.73/1.40  #Define  : 0
% 2.73/1.40  #Split   : 5
% 2.73/1.40  #Chain   : 0
% 2.73/1.40  #Close   : 0
% 2.73/1.40  
% 2.73/1.40  Ordering : KBO
% 2.73/1.40  
% 2.73/1.40  Simplification rules
% 2.73/1.40  ----------------------
% 2.73/1.40  #Subsume      : 7
% 2.73/1.40  #Demod        : 168
% 2.73/1.40  #Tautology    : 78
% 2.73/1.40  #SimpNegUnit  : 4
% 2.73/1.40  #BackRed      : 59
% 2.73/1.40  
% 2.73/1.40  #Partial instantiations: 0
% 2.73/1.40  #Strategies tried      : 1
% 2.73/1.40  
% 2.73/1.40  Timing (in seconds)
% 2.73/1.40  ----------------------
% 2.73/1.40  Preprocessing        : 0.29
% 2.73/1.40  Parsing              : 0.17
% 2.73/1.40  CNF conversion       : 0.02
% 2.73/1.40  Main loop            : 0.26
% 2.73/1.40  Inferencing          : 0.09
% 2.73/1.40  Reduction            : 0.09
% 2.73/1.40  Demodulation         : 0.06
% 2.73/1.40  BG Simplification    : 0.01
% 2.73/1.40  Subsumption          : 0.05
% 2.73/1.40  Abstraction          : 0.01
% 2.73/1.40  MUC search           : 0.00
% 2.73/1.40  Cooper               : 0.00
% 2.73/1.40  Total                : 0.59
% 2.73/1.40  Index Insertion      : 0.00
% 2.73/1.40  Index Deletion       : 0.00
% 2.73/1.40  Index Matching       : 0.00
% 2.73/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
