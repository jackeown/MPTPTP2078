%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:30 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 125 expanded)
%              Number of leaves         :   20 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :   81 ( 239 expanded)
%              Number of equality atoms :   18 (  41 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B,C,D] :
            ( ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
              | r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(D,C)) )
           => r1_tarski(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
     => ( k2_zfmisc_1(A,B) = k1_xboole_0
        | ( r1_tarski(A,C)
          & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(c_22,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_zfmisc_1('#skF_4','#skF_3'))
    | r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_49,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_58,plain,(
    ! [B_41,D_42,A_43,C_44] :
      ( r1_tarski(B_41,D_42)
      | k2_zfmisc_1(A_43,B_41) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_43,B_41),k2_zfmisc_1(C_44,D_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_61,plain,
    ( r1_tarski('#skF_2','#skF_4')
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_49,c_58])).

tff(c_64,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_61])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] :
      ( ~ r1_tarski(k2_zfmisc_1(A_8,B_9),k2_zfmisc_1(A_8,C_10))
      | r1_tarski(B_9,C_10)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_82,plain,(
    ! [C_10] :
      ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1('#skF_1',C_10))
      | r1_tarski('#skF_2',C_10)
      | k1_xboole_0 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_10])).

tff(c_99,plain,(
    ! [C_10] :
      ( r1_tarski('#skF_2',C_10)
      | k1_xboole_0 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_82])).

tff(c_103,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_xboole_0(k4_xboole_0(A_6,B_7),B_7) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_25,plain,(
    ! [B_21,A_22] :
      ( r1_xboole_0(B_21,A_22)
      | ~ r1_xboole_0(A_22,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_34,plain,(
    ! [B_25,A_26] : r1_xboole_0(B_25,k4_xboole_0(A_26,B_25)) ),
    inference(resolution,[status(thm)],[c_8,c_25])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( ~ r1_xboole_0(B_5,A_4)
      | ~ r1_tarski(B_5,A_4)
      | v1_xboole_0(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_43,plain,(
    ! [B_27,A_28] :
      ( ~ r1_tarski(B_27,k4_xboole_0(A_28,B_27))
      | v1_xboole_0(B_27) ) ),
    inference(resolution,[status(thm)],[c_34,c_6])).

tff(c_48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_43])).

tff(c_109,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_48])).

tff(c_112,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_109])).

tff(c_113,plain,(
    ! [C_10] : r1_tarski('#skF_2',C_10) ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_118,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_18])).

tff(c_119,plain,(
    r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_124,plain,(
    ! [B_53,D_54,A_55,C_56] :
      ( r1_tarski(B_53,D_54)
      | k2_zfmisc_1(A_55,B_53) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_55,B_53),k2_zfmisc_1(C_56,D_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_128,plain,
    ( r1_tarski('#skF_1','#skF_3')
    | k2_zfmisc_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_119,c_124])).

tff(c_129,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_141,plain,(
    ! [C_10] :
      ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1('#skF_2',C_10))
      | r1_tarski('#skF_1',C_10)
      | k1_xboole_0 = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_10])).

tff(c_156,plain,(
    ! [C_10] :
      ( r1_tarski('#skF_1',C_10)
      | k1_xboole_0 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_141])).

tff(c_160,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_166,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_4])).

tff(c_173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_18])).

tff(c_185,plain,(
    ! [C_61] : r1_tarski('#skF_1',C_61) ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_40,plain,(
    ! [B_25,A_26] :
      ( ~ r1_tarski(B_25,k4_xboole_0(A_26,B_25))
      | v1_xboole_0(B_25) ) ),
    inference(resolution,[status(thm)],[c_34,c_6])).

tff(c_189,plain,(
    v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_185,c_40])).

tff(c_193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_189])).

tff(c_195,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_196,plain,(
    ! [A_62,C_63,B_64,D_65] :
      ( r1_tarski(A_62,C_63)
      | k2_zfmisc_1(A_62,B_64) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_62,B_64),k2_zfmisc_1(C_63,D_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_199,plain,
    ( r1_tarski('#skF_2','#skF_4')
    | k2_zfmisc_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_119,c_196])).

tff(c_203,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_18,c_199])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:16:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.17  
% 1.88/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.17  %$ r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.88/1.17  
% 1.88/1.17  %Foreground sorts:
% 1.88/1.17  
% 1.88/1.17  
% 1.88/1.17  %Background operators:
% 1.88/1.17  
% 1.88/1.17  
% 1.88/1.17  %Foreground operators:
% 1.88/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.88/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.88/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.88/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.88/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.88/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.88/1.17  
% 1.88/1.19  tff(f_71, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B, C, D]: ((r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) | r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(D, C))) => r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_zfmisc_1)).
% 1.88/1.19  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.88/1.19  tff(f_60, axiom, (![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 1.88/1.19  tff(f_52, axiom, (![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 1.88/1.19  tff(f_41, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.88/1.19  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.88/1.19  tff(f_39, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 1.88/1.19  tff(c_22, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.88/1.19  tff(c_4, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.88/1.19  tff(c_18, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.88/1.19  tff(c_20, plain, (r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_zfmisc_1('#skF_4', '#skF_3')) | r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.88/1.19  tff(c_49, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_20])).
% 1.88/1.19  tff(c_58, plain, (![B_41, D_42, A_43, C_44]: (r1_tarski(B_41, D_42) | k2_zfmisc_1(A_43, B_41)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_43, B_41), k2_zfmisc_1(C_44, D_42)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.88/1.19  tff(c_61, plain, (r1_tarski('#skF_2', '#skF_4') | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_49, c_58])).
% 1.88/1.19  tff(c_64, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_18, c_61])).
% 1.88/1.19  tff(c_10, plain, (![A_8, B_9, C_10]: (~r1_tarski(k2_zfmisc_1(A_8, B_9), k2_zfmisc_1(A_8, C_10)) | r1_tarski(B_9, C_10) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.88/1.19  tff(c_82, plain, (![C_10]: (~r1_tarski(k1_xboole_0, k2_zfmisc_1('#skF_1', C_10)) | r1_tarski('#skF_2', C_10) | k1_xboole_0='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_64, c_10])).
% 1.88/1.19  tff(c_99, plain, (![C_10]: (r1_tarski('#skF_2', C_10) | k1_xboole_0='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_82])).
% 1.88/1.19  tff(c_103, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_99])).
% 1.88/1.19  tff(c_8, plain, (![A_6, B_7]: (r1_xboole_0(k4_xboole_0(A_6, B_7), B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.88/1.19  tff(c_25, plain, (![B_21, A_22]: (r1_xboole_0(B_21, A_22) | ~r1_xboole_0(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.88/1.19  tff(c_34, plain, (![B_25, A_26]: (r1_xboole_0(B_25, k4_xboole_0(A_26, B_25)))), inference(resolution, [status(thm)], [c_8, c_25])).
% 1.88/1.19  tff(c_6, plain, (![B_5, A_4]: (~r1_xboole_0(B_5, A_4) | ~r1_tarski(B_5, A_4) | v1_xboole_0(B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.88/1.19  tff(c_43, plain, (![B_27, A_28]: (~r1_tarski(B_27, k4_xboole_0(A_28, B_27)) | v1_xboole_0(B_27))), inference(resolution, [status(thm)], [c_34, c_6])).
% 1.88/1.19  tff(c_48, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_43])).
% 1.88/1.19  tff(c_109, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_48])).
% 1.88/1.19  tff(c_112, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_109])).
% 1.88/1.19  tff(c_113, plain, (![C_10]: (r1_tarski('#skF_2', C_10))), inference(splitRight, [status(thm)], [c_99])).
% 1.88/1.19  tff(c_118, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_113, c_18])).
% 1.88/1.19  tff(c_119, plain, (r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_zfmisc_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_20])).
% 1.88/1.19  tff(c_124, plain, (![B_53, D_54, A_55, C_56]: (r1_tarski(B_53, D_54) | k2_zfmisc_1(A_55, B_53)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_55, B_53), k2_zfmisc_1(C_56, D_54)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.88/1.19  tff(c_128, plain, (r1_tarski('#skF_1', '#skF_3') | k2_zfmisc_1('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_119, c_124])).
% 1.88/1.19  tff(c_129, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_128])).
% 1.88/1.19  tff(c_141, plain, (![C_10]: (~r1_tarski(k1_xboole_0, k2_zfmisc_1('#skF_2', C_10)) | r1_tarski('#skF_1', C_10) | k1_xboole_0='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_129, c_10])).
% 1.88/1.19  tff(c_156, plain, (![C_10]: (r1_tarski('#skF_1', C_10) | k1_xboole_0='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_141])).
% 1.88/1.19  tff(c_160, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_156])).
% 1.88/1.19  tff(c_166, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_4])).
% 1.88/1.19  tff(c_173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_166, c_18])).
% 1.88/1.19  tff(c_185, plain, (![C_61]: (r1_tarski('#skF_1', C_61))), inference(splitRight, [status(thm)], [c_156])).
% 1.88/1.19  tff(c_40, plain, (![B_25, A_26]: (~r1_tarski(B_25, k4_xboole_0(A_26, B_25)) | v1_xboole_0(B_25))), inference(resolution, [status(thm)], [c_34, c_6])).
% 1.88/1.19  tff(c_189, plain, (v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_185, c_40])).
% 1.88/1.19  tff(c_193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_189])).
% 1.88/1.19  tff(c_195, plain, (k2_zfmisc_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_128])).
% 1.88/1.19  tff(c_196, plain, (![A_62, C_63, B_64, D_65]: (r1_tarski(A_62, C_63) | k2_zfmisc_1(A_62, B_64)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_62, B_64), k2_zfmisc_1(C_63, D_65)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.88/1.19  tff(c_199, plain, (r1_tarski('#skF_2', '#skF_4') | k2_zfmisc_1('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_119, c_196])).
% 1.88/1.19  tff(c_203, plain, $false, inference(negUnitSimplification, [status(thm)], [c_195, c_18, c_199])).
% 1.88/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.19  
% 1.88/1.19  Inference rules
% 1.88/1.19  ----------------------
% 1.88/1.19  #Ref     : 0
% 1.88/1.19  #Sup     : 32
% 1.88/1.19  #Fact    : 0
% 1.88/1.19  #Define  : 0
% 1.88/1.19  #Split   : 4
% 1.88/1.19  #Chain   : 0
% 1.88/1.19  #Close   : 0
% 1.88/1.19  
% 1.88/1.19  Ordering : KBO
% 1.88/1.19  
% 1.88/1.19  Simplification rules
% 1.88/1.19  ----------------------
% 1.88/1.19  #Subsume      : 0
% 1.88/1.19  #Demod        : 33
% 1.88/1.19  #Tautology    : 14
% 1.88/1.19  #SimpNegUnit  : 4
% 1.88/1.19  #BackRed      : 17
% 1.88/1.19  
% 1.88/1.19  #Partial instantiations: 0
% 1.88/1.19  #Strategies tried      : 1
% 1.88/1.19  
% 1.88/1.19  Timing (in seconds)
% 1.88/1.19  ----------------------
% 1.88/1.19  Preprocessing        : 0.26
% 1.88/1.19  Parsing              : 0.15
% 1.88/1.19  CNF conversion       : 0.02
% 1.88/1.19  Main loop            : 0.17
% 1.88/1.19  Inferencing          : 0.06
% 1.88/1.19  Reduction            : 0.05
% 1.88/1.19  Demodulation         : 0.04
% 1.88/1.19  BG Simplification    : 0.01
% 1.88/1.19  Subsumption          : 0.03
% 1.88/1.19  Abstraction          : 0.01
% 1.88/1.19  MUC search           : 0.00
% 1.88/1.19  Cooper               : 0.00
% 1.88/1.19  Total                : 0.46
% 1.88/1.19  Index Insertion      : 0.00
% 1.88/1.19  Index Deletion       : 0.00
% 1.88/1.19  Index Matching       : 0.00
% 1.88/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
