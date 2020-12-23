%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:56 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   48 (  66 expanded)
%              Number of leaves         :   21 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   61 (  98 expanded)
%              Number of equality atoms :   31 (  53 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(B,C))
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_mcart_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & r2_hidden(C,B) )
     => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) != k1_xboole_0
     => ! [C] :
          ( m1_subset_1(C,k2_zfmisc_1(A,B))
         => ( C != k1_mcart_1(C)
            & C != k2_mcart_1(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_mcart_1)).

tff(c_18,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_141,plain,(
    ! [A_40,C_41,B_42] :
      ( k2_xboole_0(k2_tarski(A_40,C_41),B_42) = B_42
      | ~ r2_hidden(C_41,B_42)
      | ~ r2_hidden(A_40,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_157,plain,(
    ! [A_46,B_47] :
      ( k2_xboole_0(k1_tarski(A_46),B_47) = B_47
      | ~ r2_hidden(A_46,B_47)
      | ~ r2_hidden(A_46,B_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_141])).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(k1_tarski(A_7),B_8) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_181,plain,(
    ! [B_51,A_52] :
      ( k1_xboole_0 != B_51
      | ~ r2_hidden(A_52,B_51)
      | ~ r2_hidden(A_52,B_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_8])).

tff(c_183,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') != k1_xboole_0
    | ~ r2_hidden('#skF_1',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_181])).

tff(c_186,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_183])).

tff(c_60,plain,(
    ! [A_28,C_29,B_30] :
      ( k2_xboole_0(k2_tarski(A_28,C_29),B_30) = B_30
      | ~ r2_hidden(C_29,B_30)
      | ~ r2_hidden(A_28,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_72,plain,(
    ! [A_31,B_32] :
      ( k2_xboole_0(k1_tarski(A_31),B_32) = B_32
      | ~ r2_hidden(A_31,B_32)
      | ~ r2_hidden(A_31,B_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_60])).

tff(c_116,plain,(
    ! [A_31] : ~ r2_hidden(A_31,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_8])).

tff(c_16,plain,
    ( k2_mcart_1('#skF_1') = '#skF_1'
    | k1_mcart_1('#skF_1') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_29,plain,(
    k1_mcart_1('#skF_1') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_34,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,B_19)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_38,plain,(
    m1_subset_1('#skF_1',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_34])).

tff(c_90,plain,(
    ! [C_33,A_34,B_35] :
      ( k1_mcart_1(C_33) != C_33
      | ~ m1_subset_1(C_33,k2_zfmisc_1(A_34,B_35))
      | k2_zfmisc_1(A_34,B_35) = k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_93,plain,
    ( k1_mcart_1('#skF_1') != '#skF_1'
    | k2_zfmisc_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_90])).

tff(c_96,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_93])).

tff(c_98,plain,(
    r2_hidden('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_18])).

tff(c_118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_98])).

tff(c_119,plain,(
    k2_mcart_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_125,plain,(
    ! [A_36,B_37] :
      ( m1_subset_1(A_36,B_37)
      | ~ r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_129,plain,(
    m1_subset_1('#skF_1',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_125])).

tff(c_187,plain,(
    ! [C_53,A_54,B_55] :
      ( k2_mcart_1(C_53) != C_53
      | ~ m1_subset_1(C_53,k2_zfmisc_1(A_54,B_55))
      | k2_zfmisc_1(A_54,B_55) = k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_190,plain,
    ( k2_mcart_1('#skF_1') != '#skF_1'
    | k2_zfmisc_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_129,c_187])).

tff(c_193,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_190])).

tff(c_195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_193])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:05:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.40  
% 2.05/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.40  %$ r2_hidden > m1_subset_1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.05/1.40  
% 2.05/1.40  %Foreground sorts:
% 2.05/1.40  
% 2.05/1.40  
% 2.05/1.40  %Background operators:
% 2.05/1.40  
% 2.05/1.40  
% 2.05/1.40  %Foreground operators:
% 2.05/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.05/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.05/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.05/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.05/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.05/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.05/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.40  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.05/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.05/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.40  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.05/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.05/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.05/1.40  
% 2.05/1.41  tff(f_63, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_mcart_1)).
% 2.05/1.41  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.05/1.41  tff(f_35, axiom, (![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 2.05/1.41  tff(f_38, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.05/1.41  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.05/1.41  tff(f_54, axiom, (![A, B]: (~(k2_zfmisc_1(A, B) = k1_xboole_0) => (![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (~(C = k1_mcart_1(C)) & ~(C = k2_mcart_1(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_mcart_1)).
% 2.05/1.41  tff(c_18, plain, (r2_hidden('#skF_1', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.05/1.41  tff(c_4, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.05/1.41  tff(c_141, plain, (![A_40, C_41, B_42]: (k2_xboole_0(k2_tarski(A_40, C_41), B_42)=B_42 | ~r2_hidden(C_41, B_42) | ~r2_hidden(A_40, B_42))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.05/1.41  tff(c_157, plain, (![A_46, B_47]: (k2_xboole_0(k1_tarski(A_46), B_47)=B_47 | ~r2_hidden(A_46, B_47) | ~r2_hidden(A_46, B_47))), inference(superposition, [status(thm), theory('equality')], [c_4, c_141])).
% 2.05/1.41  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(k1_tarski(A_7), B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.05/1.41  tff(c_181, plain, (![B_51, A_52]: (k1_xboole_0!=B_51 | ~r2_hidden(A_52, B_51) | ~r2_hidden(A_52, B_51))), inference(superposition, [status(thm), theory('equality')], [c_157, c_8])).
% 2.05/1.41  tff(c_183, plain, (k2_zfmisc_1('#skF_2', '#skF_3')!=k1_xboole_0 | ~r2_hidden('#skF_1', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_181])).
% 2.05/1.41  tff(c_186, plain, (k2_zfmisc_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_18, c_183])).
% 2.05/1.41  tff(c_60, plain, (![A_28, C_29, B_30]: (k2_xboole_0(k2_tarski(A_28, C_29), B_30)=B_30 | ~r2_hidden(C_29, B_30) | ~r2_hidden(A_28, B_30))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.05/1.41  tff(c_72, plain, (![A_31, B_32]: (k2_xboole_0(k1_tarski(A_31), B_32)=B_32 | ~r2_hidden(A_31, B_32) | ~r2_hidden(A_31, B_32))), inference(superposition, [status(thm), theory('equality')], [c_4, c_60])).
% 2.05/1.41  tff(c_116, plain, (![A_31]: (~r2_hidden(A_31, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_72, c_8])).
% 2.05/1.41  tff(c_16, plain, (k2_mcart_1('#skF_1')='#skF_1' | k1_mcart_1('#skF_1')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.05/1.41  tff(c_29, plain, (k1_mcart_1('#skF_1')='#skF_1'), inference(splitLeft, [status(thm)], [c_16])).
% 2.05/1.41  tff(c_34, plain, (![A_18, B_19]: (m1_subset_1(A_18, B_19) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.05/1.41  tff(c_38, plain, (m1_subset_1('#skF_1', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_34])).
% 2.05/1.41  tff(c_90, plain, (![C_33, A_34, B_35]: (k1_mcart_1(C_33)!=C_33 | ~m1_subset_1(C_33, k2_zfmisc_1(A_34, B_35)) | k2_zfmisc_1(A_34, B_35)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.05/1.41  tff(c_93, plain, (k1_mcart_1('#skF_1')!='#skF_1' | k2_zfmisc_1('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_90])).
% 2.05/1.41  tff(c_96, plain, (k2_zfmisc_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_29, c_93])).
% 2.05/1.41  tff(c_98, plain, (r2_hidden('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_96, c_18])).
% 2.05/1.41  tff(c_118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116, c_98])).
% 2.05/1.41  tff(c_119, plain, (k2_mcart_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_16])).
% 2.05/1.41  tff(c_125, plain, (![A_36, B_37]: (m1_subset_1(A_36, B_37) | ~r2_hidden(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.05/1.41  tff(c_129, plain, (m1_subset_1('#skF_1', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_125])).
% 2.05/1.41  tff(c_187, plain, (![C_53, A_54, B_55]: (k2_mcart_1(C_53)!=C_53 | ~m1_subset_1(C_53, k2_zfmisc_1(A_54, B_55)) | k2_zfmisc_1(A_54, B_55)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.05/1.41  tff(c_190, plain, (k2_mcart_1('#skF_1')!='#skF_1' | k2_zfmisc_1('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_129, c_187])).
% 2.05/1.41  tff(c_193, plain, (k2_zfmisc_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_119, c_190])).
% 2.05/1.41  tff(c_195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_186, c_193])).
% 2.05/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.41  
% 2.05/1.41  Inference rules
% 2.05/1.41  ----------------------
% 2.05/1.41  #Ref     : 0
% 2.05/1.41  #Sup     : 42
% 2.05/1.41  #Fact    : 0
% 2.05/1.41  #Define  : 0
% 2.05/1.41  #Split   : 2
% 2.05/1.41  #Chain   : 0
% 2.05/1.41  #Close   : 0
% 2.05/1.41  
% 2.05/1.41  Ordering : KBO
% 2.05/1.41  
% 2.05/1.41  Simplification rules
% 2.05/1.41  ----------------------
% 2.05/1.41  #Subsume      : 1
% 2.05/1.41  #Demod        : 8
% 2.05/1.41  #Tautology    : 23
% 2.05/1.41  #SimpNegUnit  : 2
% 2.05/1.41  #BackRed      : 3
% 2.05/1.41  
% 2.05/1.41  #Partial instantiations: 0
% 2.05/1.41  #Strategies tried      : 1
% 2.05/1.41  
% 2.05/1.41  Timing (in seconds)
% 2.05/1.41  ----------------------
% 2.05/1.42  Preprocessing        : 0.42
% 2.05/1.42  Parsing              : 0.24
% 2.05/1.42  CNF conversion       : 0.02
% 2.05/1.42  Main loop            : 0.17
% 2.05/1.42  Inferencing          : 0.07
% 2.05/1.42  Reduction            : 0.05
% 2.05/1.42  Demodulation         : 0.04
% 2.05/1.42  BG Simplification    : 0.01
% 2.05/1.42  Subsumption          : 0.02
% 2.05/1.42  Abstraction          : 0.01
% 2.05/1.42  MUC search           : 0.00
% 2.05/1.42  Cooper               : 0.00
% 2.05/1.42  Total                : 0.62
% 2.05/1.42  Index Insertion      : 0.00
% 2.05/1.42  Index Deletion       : 0.00
% 2.05/1.42  Index Matching       : 0.00
% 2.05/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
