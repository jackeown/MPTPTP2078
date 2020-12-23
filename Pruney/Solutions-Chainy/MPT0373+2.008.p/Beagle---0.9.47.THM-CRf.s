%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:57 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 111 expanded)
%              Number of leaves         :   24 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :   78 ( 210 expanded)
%              Number of equality atoms :   10 (  29 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,A)
       => ( A != k1_xboole_0
         => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_39,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(k1_tarski(A_15),B_16)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_40,plain,(
    m1_subset_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_78,plain,(
    ! [B_31,A_32] :
      ( v1_xboole_0(B_31)
      | ~ m1_subset_1(B_31,A_32)
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_86,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_78])).

tff(c_87,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_30,plain,(
    ! [B_18,A_17] :
      ( r2_hidden(B_18,A_17)
      | ~ m1_subset_1(B_18,A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_63,plain,(
    ! [B_27,A_28] :
      ( m1_subset_1(B_27,A_28)
      | ~ v1_xboole_0(B_27)
      | ~ v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_36,plain,(
    ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_67,plain,
    ( ~ v1_xboole_0(k1_tarski('#skF_6'))
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_63,c_36])).

tff(c_68,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_14,plain,(
    ! [C_14,A_10] :
      ( r2_hidden(C_14,k1_zfmisc_1(A_10))
      | ~ r1_tarski(C_14,A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_114,plain,(
    ! [B_41,A_42] :
      ( m1_subset_1(B_41,A_42)
      | ~ r2_hidden(B_41,A_42)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_167,plain,(
    ! [C_51,A_52] :
      ( m1_subset_1(C_51,k1_zfmisc_1(A_52))
      | v1_xboole_0(k1_zfmisc_1(A_52))
      | ~ r1_tarski(C_51,A_52) ) ),
    inference(resolution,[status(thm)],[c_14,c_114])).

tff(c_173,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_5'))
    | ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_167,c_36])).

tff(c_177,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_173])).

tff(c_181,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_177])).

tff(c_184,plain,
    ( ~ m1_subset_1('#skF_6','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_181])).

tff(c_187,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_184])).

tff(c_189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_187])).

tff(c_191,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_51,plain,(
    ! [A_22] :
      ( r2_hidden('#skF_2'(A_22),A_22)
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_55,plain,(
    ! [A_22] :
      ( ~ v1_xboole_0(A_22)
      | k1_xboole_0 = A_22 ) ),
    inference(resolution,[status(thm)],[c_51,c_2])).

tff(c_198,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_191,c_55])).

tff(c_202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_198])).

tff(c_204,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_208,plain,(
    k1_zfmisc_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_204,c_55])).

tff(c_209,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_204])).

tff(c_215,plain,(
    ! [C_53,A_54] :
      ( r2_hidden(C_53,k1_zfmisc_1(A_54))
      | ~ r1_tarski(C_53,A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_234,plain,(
    ! [A_55,C_56] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_55))
      | ~ r1_tarski(C_56,A_55) ) ),
    inference(resolution,[status(thm)],[c_215,c_2])).

tff(c_236,plain,(
    ! [C_56] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r1_tarski(C_56,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_234])).

tff(c_246,plain,(
    ! [C_58] : ~ r1_tarski(C_58,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_236])).

tff(c_252,plain,(
    ! [A_59] : ~ r2_hidden(A_59,'#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_246])).

tff(c_260,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_6,c_252])).

tff(c_265,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_260])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:01:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.24  
% 2.13/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.25  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4
% 2.13/1.25  
% 2.13/1.25  %Foreground sorts:
% 2.13/1.25  
% 2.13/1.25  
% 2.13/1.25  %Background operators:
% 2.13/1.25  
% 2.13/1.25  
% 2.13/1.25  %Foreground operators:
% 2.13/1.25  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.13/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.13/1.25  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.13/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.25  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.13/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.13/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.13/1.25  tff('#skF_6', type, '#skF_6': $i).
% 2.13/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.13/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.13/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.13/1.25  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.13/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.13/1.25  
% 2.13/1.26  tff(f_75, negated_conjecture, ~(![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 2.13/1.26  tff(f_39, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.13/1.26  tff(f_54, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.13/1.26  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.13/1.26  tff(f_50, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.13/1.26  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.13/1.26  tff(c_38, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.13/1.26  tff(c_6, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.13/1.26  tff(c_26, plain, (![A_15, B_16]: (r1_tarski(k1_tarski(A_15), B_16) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.13/1.26  tff(c_40, plain, (m1_subset_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.13/1.26  tff(c_78, plain, (![B_31, A_32]: (v1_xboole_0(B_31) | ~m1_subset_1(B_31, A_32) | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.13/1.26  tff(c_86, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_40, c_78])).
% 2.13/1.26  tff(c_87, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_86])).
% 2.13/1.26  tff(c_30, plain, (![B_18, A_17]: (r2_hidden(B_18, A_17) | ~m1_subset_1(B_18, A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.13/1.26  tff(c_63, plain, (![B_27, A_28]: (m1_subset_1(B_27, A_28) | ~v1_xboole_0(B_27) | ~v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.13/1.26  tff(c_36, plain, (~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.13/1.26  tff(c_67, plain, (~v1_xboole_0(k1_tarski('#skF_6')) | ~v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_63, c_36])).
% 2.13/1.26  tff(c_68, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_67])).
% 2.13/1.26  tff(c_14, plain, (![C_14, A_10]: (r2_hidden(C_14, k1_zfmisc_1(A_10)) | ~r1_tarski(C_14, A_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.13/1.26  tff(c_114, plain, (![B_41, A_42]: (m1_subset_1(B_41, A_42) | ~r2_hidden(B_41, A_42) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.13/1.26  tff(c_167, plain, (![C_51, A_52]: (m1_subset_1(C_51, k1_zfmisc_1(A_52)) | v1_xboole_0(k1_zfmisc_1(A_52)) | ~r1_tarski(C_51, A_52))), inference(resolution, [status(thm)], [c_14, c_114])).
% 2.13/1.26  tff(c_173, plain, (v1_xboole_0(k1_zfmisc_1('#skF_5')) | ~r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_167, c_36])).
% 2.13/1.26  tff(c_177, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_68, c_173])).
% 2.13/1.26  tff(c_181, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_26, c_177])).
% 2.13/1.26  tff(c_184, plain, (~m1_subset_1('#skF_6', '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_30, c_181])).
% 2.13/1.26  tff(c_187, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_184])).
% 2.13/1.26  tff(c_189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_187])).
% 2.13/1.26  tff(c_191, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_86])).
% 2.13/1.26  tff(c_51, plain, (![A_22]: (r2_hidden('#skF_2'(A_22), A_22) | k1_xboole_0=A_22)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.13/1.26  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.26  tff(c_55, plain, (![A_22]: (~v1_xboole_0(A_22) | k1_xboole_0=A_22)), inference(resolution, [status(thm)], [c_51, c_2])).
% 2.13/1.26  tff(c_198, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_191, c_55])).
% 2.13/1.26  tff(c_202, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_198])).
% 2.13/1.26  tff(c_204, plain, (v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(splitRight, [status(thm)], [c_67])).
% 2.13/1.26  tff(c_208, plain, (k1_zfmisc_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_204, c_55])).
% 2.13/1.26  tff(c_209, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_208, c_204])).
% 2.13/1.26  tff(c_215, plain, (![C_53, A_54]: (r2_hidden(C_53, k1_zfmisc_1(A_54)) | ~r1_tarski(C_53, A_54))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.13/1.26  tff(c_234, plain, (![A_55, C_56]: (~v1_xboole_0(k1_zfmisc_1(A_55)) | ~r1_tarski(C_56, A_55))), inference(resolution, [status(thm)], [c_215, c_2])).
% 2.13/1.26  tff(c_236, plain, (![C_56]: (~v1_xboole_0(k1_xboole_0) | ~r1_tarski(C_56, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_208, c_234])).
% 2.13/1.26  tff(c_246, plain, (![C_58]: (~r1_tarski(C_58, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_209, c_236])).
% 2.13/1.26  tff(c_252, plain, (![A_59]: (~r2_hidden(A_59, '#skF_5'))), inference(resolution, [status(thm)], [c_26, c_246])).
% 2.13/1.26  tff(c_260, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_6, c_252])).
% 2.13/1.26  tff(c_265, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_260])).
% 2.13/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.26  
% 2.13/1.26  Inference rules
% 2.13/1.26  ----------------------
% 2.13/1.26  #Ref     : 0
% 2.13/1.26  #Sup     : 43
% 2.13/1.26  #Fact    : 0
% 2.13/1.26  #Define  : 0
% 2.13/1.26  #Split   : 2
% 2.13/1.26  #Chain   : 0
% 2.13/1.26  #Close   : 0
% 2.13/1.26  
% 2.13/1.26  Ordering : KBO
% 2.13/1.26  
% 2.13/1.26  Simplification rules
% 2.13/1.26  ----------------------
% 2.13/1.26  #Subsume      : 5
% 2.13/1.26  #Demod        : 6
% 2.13/1.26  #Tautology    : 14
% 2.13/1.26  #SimpNegUnit  : 4
% 2.13/1.26  #BackRed      : 2
% 2.13/1.26  
% 2.13/1.26  #Partial instantiations: 0
% 2.13/1.26  #Strategies tried      : 1
% 2.13/1.26  
% 2.13/1.26  Timing (in seconds)
% 2.13/1.26  ----------------------
% 2.13/1.26  Preprocessing        : 0.29
% 2.13/1.26  Parsing              : 0.15
% 2.13/1.26  CNF conversion       : 0.02
% 2.13/1.26  Main loop            : 0.18
% 2.13/1.26  Inferencing          : 0.07
% 2.13/1.26  Reduction            : 0.05
% 2.13/1.26  Demodulation         : 0.03
% 2.13/1.26  BG Simplification    : 0.01
% 2.13/1.26  Subsumption          : 0.03
% 2.13/1.26  Abstraction          : 0.01
% 2.13/1.26  MUC search           : 0.00
% 2.13/1.26  Cooper               : 0.00
% 2.13/1.26  Total                : 0.49
% 2.13/1.26  Index Insertion      : 0.00
% 2.13/1.26  Index Deletion       : 0.00
% 2.13/1.26  Index Matching       : 0.00
% 2.13/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
