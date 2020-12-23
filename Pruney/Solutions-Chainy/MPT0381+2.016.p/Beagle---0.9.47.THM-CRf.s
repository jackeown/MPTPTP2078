%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:03 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   56 (  97 expanded)
%              Number of leaves         :   29 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :   62 ( 139 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_52,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_63,plain,(
    ! [B_32,A_33] :
      ( ~ r2_hidden(B_32,A_33)
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_67,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_63])).

tff(c_154,plain,(
    ! [B_56,A_57] :
      ( m1_subset_1(B_56,A_57)
      | ~ r2_hidden(B_56,A_57)
      | v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_163,plain,
    ( m1_subset_1('#skF_4','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_154])).

tff(c_168,plain,(
    m1_subset_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_163])).

tff(c_252,plain,(
    ! [B_71,A_72] :
      ( m1_subset_1(k1_tarski(B_71),k1_zfmisc_1(A_72))
      | k1_xboole_0 = A_72
      | ~ m1_subset_1(B_71,A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_50,plain,(
    ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_258,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_252,c_50])).

tff(c_262,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_258])).

tff(c_221,plain,(
    ! [B_66,A_67] :
      ( m1_subset_1(k1_tarski(B_66),k1_zfmisc_1(A_67))
      | k1_xboole_0 = A_67
      | ~ m1_subset_1(B_66,A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_227,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_221,c_50])).

tff(c_231,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_227])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_94,plain,(
    ! [A_43,B_44] :
      ( k4_xboole_0(A_43,B_44) = A_43
      | ~ r1_xboole_0(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_102,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(resolution,[status(thm)],[c_26,c_94])).

tff(c_140,plain,(
    ! [D_53,B_54,A_55] :
      ( ~ r2_hidden(D_53,B_54)
      | ~ r2_hidden(D_53,k4_xboole_0(A_55,B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_178,plain,(
    ! [D_59,A_60] :
      ( ~ r2_hidden(D_59,k1_xboole_0)
      | ~ r2_hidden(D_59,A_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_140])).

tff(c_186,plain,(
    ! [A_60] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0),A_60)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_178])).

tff(c_188,plain,(
    ! [A_61] : ~ r2_hidden('#skF_1'(k1_xboole_0),A_61) ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_198,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_188])).

tff(c_234,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_198])).

tff(c_240,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_234])).

tff(c_241,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_284,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_241])).

tff(c_289,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_284])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:39:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.30  
% 2.04/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.30  %$ r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.04/1.30  
% 2.04/1.30  %Foreground sorts:
% 2.04/1.30  
% 2.04/1.30  
% 2.04/1.30  %Background operators:
% 2.04/1.30  
% 2.04/1.30  
% 2.04/1.30  %Foreground operators:
% 2.04/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.04/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.04/1.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.04/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.04/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.04/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.04/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.04/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.04/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.04/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.04/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.04/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.04/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.04/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.04/1.30  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.04/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.04/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.04/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.04/1.30  
% 2.04/1.31  tff(f_82, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 2.04/1.31  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.04/1.31  tff(f_70, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.04/1.31  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 2.04/1.31  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.04/1.31  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.04/1.31  tff(f_41, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.04/1.31  tff(c_52, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.04/1.31  tff(c_63, plain, (![B_32, A_33]: (~r2_hidden(B_32, A_33) | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.04/1.31  tff(c_67, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_52, c_63])).
% 2.04/1.31  tff(c_154, plain, (![B_56, A_57]: (m1_subset_1(B_56, A_57) | ~r2_hidden(B_56, A_57) | v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.04/1.31  tff(c_163, plain, (m1_subset_1('#skF_4', '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_52, c_154])).
% 2.04/1.31  tff(c_168, plain, (m1_subset_1('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_67, c_163])).
% 2.04/1.31  tff(c_252, plain, (![B_71, A_72]: (m1_subset_1(k1_tarski(B_71), k1_zfmisc_1(A_72)) | k1_xboole_0=A_72 | ~m1_subset_1(B_71, A_72))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.04/1.31  tff(c_50, plain, (~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.04/1.31  tff(c_258, plain, (k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_252, c_50])).
% 2.04/1.31  tff(c_262, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_168, c_258])).
% 2.04/1.31  tff(c_221, plain, (![B_66, A_67]: (m1_subset_1(k1_tarski(B_66), k1_zfmisc_1(A_67)) | k1_xboole_0=A_67 | ~m1_subset_1(B_66, A_67))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.04/1.31  tff(c_227, plain, (k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_221, c_50])).
% 2.04/1.31  tff(c_231, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_168, c_227])).
% 2.04/1.31  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.04/1.31  tff(c_26, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.04/1.31  tff(c_94, plain, (![A_43, B_44]: (k4_xboole_0(A_43, B_44)=A_43 | ~r1_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.04/1.31  tff(c_102, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(resolution, [status(thm)], [c_26, c_94])).
% 2.04/1.31  tff(c_140, plain, (![D_53, B_54, A_55]: (~r2_hidden(D_53, B_54) | ~r2_hidden(D_53, k4_xboole_0(A_55, B_54)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.04/1.31  tff(c_178, plain, (![D_59, A_60]: (~r2_hidden(D_59, k1_xboole_0) | ~r2_hidden(D_59, A_60))), inference(superposition, [status(thm), theory('equality')], [c_102, c_140])).
% 2.04/1.31  tff(c_186, plain, (![A_60]: (~r2_hidden('#skF_1'(k1_xboole_0), A_60) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_178])).
% 2.04/1.31  tff(c_188, plain, (![A_61]: (~r2_hidden('#skF_1'(k1_xboole_0), A_61))), inference(splitLeft, [status(thm)], [c_186])).
% 2.04/1.31  tff(c_198, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_188])).
% 2.04/1.31  tff(c_234, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_231, c_198])).
% 2.04/1.31  tff(c_240, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_234])).
% 2.04/1.31  tff(c_241, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_186])).
% 2.04/1.31  tff(c_284, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_262, c_241])).
% 2.04/1.31  tff(c_289, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_284])).
% 2.04/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.31  
% 2.04/1.31  Inference rules
% 2.04/1.31  ----------------------
% 2.04/1.31  #Ref     : 0
% 2.04/1.31  #Sup     : 45
% 2.04/1.31  #Fact    : 0
% 2.04/1.31  #Define  : 0
% 2.04/1.31  #Split   : 2
% 2.04/1.31  #Chain   : 0
% 2.04/1.31  #Close   : 0
% 2.04/1.31  
% 2.04/1.31  Ordering : KBO
% 2.04/1.32  
% 2.04/1.32  Simplification rules
% 2.04/1.32  ----------------------
% 2.04/1.32  #Subsume      : 1
% 2.27/1.32  #Demod        : 17
% 2.27/1.32  #Tautology    : 26
% 2.27/1.32  #SimpNegUnit  : 3
% 2.27/1.32  #BackRed      : 12
% 2.27/1.32  
% 2.27/1.32  #Partial instantiations: 0
% 2.27/1.32  #Strategies tried      : 1
% 2.27/1.32  
% 2.27/1.32  Timing (in seconds)
% 2.27/1.32  ----------------------
% 2.27/1.32  Preprocessing        : 0.35
% 2.27/1.32  Parsing              : 0.18
% 2.27/1.32  CNF conversion       : 0.02
% 2.27/1.32  Main loop            : 0.20
% 2.27/1.32  Inferencing          : 0.07
% 2.27/1.32  Reduction            : 0.05
% 2.27/1.32  Demodulation         : 0.03
% 2.27/1.32  BG Simplification    : 0.02
% 2.27/1.32  Subsumption          : 0.04
% 2.27/1.32  Abstraction          : 0.01
% 2.27/1.32  MUC search           : 0.00
% 2.27/1.32  Cooper               : 0.00
% 2.27/1.32  Total                : 0.57
% 2.27/1.32  Index Insertion      : 0.00
% 2.27/1.32  Index Deletion       : 0.00
% 2.27/1.32  Index Matching       : 0.00
% 2.27/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
