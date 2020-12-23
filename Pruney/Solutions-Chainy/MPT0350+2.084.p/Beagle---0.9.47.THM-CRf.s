%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:36 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   53 (  69 expanded)
%              Number of leaves         :   29 (  37 expanded)
%              Depth                    :    6
%              Number of atoms          :   58 (  86 expanded)
%              Number of equality atoms :   18 (  29 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_46,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_18,plain,(
    ! [A_17] : k2_subset_1(A_17) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_28,plain,(
    k4_subset_1('#skF_2','#skF_3',k3_subset_1('#skF_2','#skF_3')) != k2_subset_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_31,plain,(
    k4_subset_1('#skF_2','#skF_3',k3_subset_1('#skF_2','#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_28])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_103,plain,(
    ! [A_54,B_55] :
      ( k4_xboole_0(A_54,B_55) = k3_subset_1(A_54,B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_111,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k3_subset_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_103])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k2_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = B_9
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_122,plain,
    ( k2_xboole_0('#skF_3',k3_subset_1('#skF_2','#skF_3')) = '#skF_2'
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_10])).

tff(c_126,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_99,plain,(
    ! [C_51,A_52,B_53] :
      ( r2_hidden(C_51,A_52)
      | ~ r2_hidden(C_51,B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_153,plain,(
    ! [A_63,B_64,A_65] :
      ( r2_hidden('#skF_1'(A_63,B_64),A_65)
      | ~ m1_subset_1(A_63,k1_zfmisc_1(A_65))
      | r1_tarski(A_63,B_64) ) ),
    inference(resolution,[status(thm)],[c_6,c_99])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_165,plain,(
    ! [A_66,A_67] :
      ( ~ m1_subset_1(A_66,k1_zfmisc_1(A_67))
      | r1_tarski(A_66,A_67) ) ),
    inference(resolution,[status(thm)],[c_153,c_4])).

tff(c_171,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_165])).

tff(c_176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_171])).

tff(c_177,plain,(
    k2_xboole_0('#skF_3',k3_subset_1('#skF_2','#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_22,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k3_subset_1(A_20,B_21),k1_zfmisc_1(A_20))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_112,plain,(
    ! [A_56,B_57,C_58] :
      ( k4_subset_1(A_56,B_57,C_58) = k2_xboole_0(B_57,C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(A_56))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_253,plain,(
    ! [A_82,B_83,B_84] :
      ( k4_subset_1(A_82,B_83,k3_subset_1(A_82,B_84)) = k2_xboole_0(B_83,k3_subset_1(A_82,B_84))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_82))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_82)) ) ),
    inference(resolution,[status(thm)],[c_22,c_112])).

tff(c_289,plain,(
    ! [B_91] :
      ( k4_subset_1('#skF_2','#skF_3',k3_subset_1('#skF_2',B_91)) = k2_xboole_0('#skF_3',k3_subset_1('#skF_2',B_91))
      | ~ m1_subset_1(B_91,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_30,c_253])).

tff(c_296,plain,(
    k4_subset_1('#skF_2','#skF_3',k3_subset_1('#skF_2','#skF_3')) = k2_xboole_0('#skF_3',k3_subset_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_289])).

tff(c_299,plain,(
    k4_subset_1('#skF_2','#skF_3',k3_subset_1('#skF_2','#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_296])).

tff(c_301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31,c_299])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:58:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.29  
% 2.06/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.29  %$ r2_hidden > r1_tarski > m1_subset_1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.06/1.29  
% 2.06/1.29  %Foreground sorts:
% 2.06/1.29  
% 2.06/1.29  
% 2.06/1.29  %Background operators:
% 2.06/1.29  
% 2.06/1.29  
% 2.06/1.29  %Foreground operators:
% 2.06/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.06/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.06/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.06/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.29  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.06/1.29  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.06/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.06/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.06/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.06/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.06/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.06/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.06/1.29  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.06/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.06/1.29  
% 2.06/1.31  tff(f_46, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.06/1.31  tff(f_72, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 2.06/1.31  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.06/1.31  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 2.06/1.31  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.06/1.31  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.06/1.31  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.06/1.31  tff(f_67, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.06/1.31  tff(c_18, plain, (![A_17]: (k2_subset_1(A_17)=A_17)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.06/1.31  tff(c_28, plain, (k4_subset_1('#skF_2', '#skF_3', k3_subset_1('#skF_2', '#skF_3'))!=k2_subset_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.06/1.31  tff(c_31, plain, (k4_subset_1('#skF_2', '#skF_3', k3_subset_1('#skF_2', '#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_28])).
% 2.06/1.31  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.06/1.31  tff(c_103, plain, (![A_54, B_55]: (k4_xboole_0(A_54, B_55)=k3_subset_1(A_54, B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.06/1.31  tff(c_111, plain, (k4_xboole_0('#skF_2', '#skF_3')=k3_subset_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_103])).
% 2.06/1.31  tff(c_10, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k4_xboole_0(B_9, A_8))=B_9 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.06/1.31  tff(c_122, plain, (k2_xboole_0('#skF_3', k3_subset_1('#skF_2', '#skF_3'))='#skF_2' | ~r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_111, c_10])).
% 2.06/1.31  tff(c_126, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_122])).
% 2.06/1.31  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.06/1.31  tff(c_99, plain, (![C_51, A_52, B_53]: (r2_hidden(C_51, A_52) | ~r2_hidden(C_51, B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.06/1.31  tff(c_153, plain, (![A_63, B_64, A_65]: (r2_hidden('#skF_1'(A_63, B_64), A_65) | ~m1_subset_1(A_63, k1_zfmisc_1(A_65)) | r1_tarski(A_63, B_64))), inference(resolution, [status(thm)], [c_6, c_99])).
% 2.06/1.31  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.06/1.31  tff(c_165, plain, (![A_66, A_67]: (~m1_subset_1(A_66, k1_zfmisc_1(A_67)) | r1_tarski(A_66, A_67))), inference(resolution, [status(thm)], [c_153, c_4])).
% 2.06/1.31  tff(c_171, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_165])).
% 2.06/1.31  tff(c_176, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126, c_171])).
% 2.06/1.31  tff(c_177, plain, (k2_xboole_0('#skF_3', k3_subset_1('#skF_2', '#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_122])).
% 2.06/1.31  tff(c_22, plain, (![A_20, B_21]: (m1_subset_1(k3_subset_1(A_20, B_21), k1_zfmisc_1(A_20)) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.06/1.31  tff(c_112, plain, (![A_56, B_57, C_58]: (k4_subset_1(A_56, B_57, C_58)=k2_xboole_0(B_57, C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(A_56)) | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.06/1.31  tff(c_253, plain, (![A_82, B_83, B_84]: (k4_subset_1(A_82, B_83, k3_subset_1(A_82, B_84))=k2_xboole_0(B_83, k3_subset_1(A_82, B_84)) | ~m1_subset_1(B_83, k1_zfmisc_1(A_82)) | ~m1_subset_1(B_84, k1_zfmisc_1(A_82)))), inference(resolution, [status(thm)], [c_22, c_112])).
% 2.06/1.31  tff(c_289, plain, (![B_91]: (k4_subset_1('#skF_2', '#skF_3', k3_subset_1('#skF_2', B_91))=k2_xboole_0('#skF_3', k3_subset_1('#skF_2', B_91)) | ~m1_subset_1(B_91, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_30, c_253])).
% 2.06/1.31  tff(c_296, plain, (k4_subset_1('#skF_2', '#skF_3', k3_subset_1('#skF_2', '#skF_3'))=k2_xboole_0('#skF_3', k3_subset_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_289])).
% 2.06/1.31  tff(c_299, plain, (k4_subset_1('#skF_2', '#skF_3', k3_subset_1('#skF_2', '#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_177, c_296])).
% 2.06/1.31  tff(c_301, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31, c_299])).
% 2.06/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.31  
% 2.06/1.31  Inference rules
% 2.06/1.31  ----------------------
% 2.06/1.31  #Ref     : 0
% 2.06/1.31  #Sup     : 67
% 2.06/1.31  #Fact    : 0
% 2.06/1.31  #Define  : 0
% 2.06/1.31  #Split   : 1
% 2.06/1.31  #Chain   : 0
% 2.06/1.31  #Close   : 0
% 2.06/1.31  
% 2.06/1.31  Ordering : KBO
% 2.06/1.31  
% 2.06/1.31  Simplification rules
% 2.06/1.31  ----------------------
% 2.06/1.31  #Subsume      : 1
% 2.06/1.31  #Demod        : 3
% 2.06/1.31  #Tautology    : 27
% 2.06/1.31  #SimpNegUnit  : 2
% 2.06/1.31  #BackRed      : 0
% 2.06/1.31  
% 2.06/1.31  #Partial instantiations: 0
% 2.06/1.31  #Strategies tried      : 1
% 2.06/1.31  
% 2.06/1.31  Timing (in seconds)
% 2.06/1.31  ----------------------
% 2.06/1.31  Preprocessing        : 0.31
% 2.06/1.31  Parsing              : 0.17
% 2.06/1.31  CNF conversion       : 0.02
% 2.06/1.31  Main loop            : 0.23
% 2.06/1.31  Inferencing          : 0.09
% 2.06/1.31  Reduction            : 0.06
% 2.06/1.31  Demodulation         : 0.04
% 2.06/1.31  BG Simplification    : 0.01
% 2.06/1.31  Subsumption          : 0.05
% 2.06/1.31  Abstraction          : 0.01
% 2.06/1.31  MUC search           : 0.00
% 2.06/1.31  Cooper               : 0.00
% 2.06/1.31  Total                : 0.56
% 2.06/1.31  Index Insertion      : 0.00
% 2.06/1.31  Index Deletion       : 0.00
% 2.06/1.31  Index Matching       : 0.00
% 2.06/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
