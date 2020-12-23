%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:01 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 153 expanded)
%              Number of leaves         :   31 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :   67 ( 204 expanded)
%              Number of equality atoms :   18 (  67 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_58,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_64,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_697,plain,(
    ! [D_97,A_98,B_99] :
      ( r2_hidden(D_97,k4_xboole_0(A_98,B_99))
      | r2_hidden(D_97,B_99)
      | ~ r2_hidden(D_97,A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_75,plain,(
    ! [B_37,A_38] :
      ( ~ r2_hidden(B_37,A_38)
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_79,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_75])).

tff(c_316,plain,(
    ! [B_66,A_67] :
      ( m1_subset_1(B_66,A_67)
      | ~ r2_hidden(B_66,A_67)
      | v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_325,plain,
    ( m1_subset_1('#skF_4','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_316])).

tff(c_330,plain,(
    m1_subset_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_325])).

tff(c_441,plain,(
    ! [B_78,A_79] :
      ( m1_subset_1(k1_tarski(B_78),k1_zfmisc_1(A_79))
      | k1_xboole_0 = A_79
      | ~ m1_subset_1(B_78,A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_62,plain,(
    ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_447,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_441,c_62])).

tff(c_451,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_447])).

tff(c_42,plain,(
    ! [A_20] : r1_tarski(k1_xboole_0,A_20) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_124,plain,(
    ! [A_44,B_45] :
      ( k3_xboole_0(A_44,B_45) = A_44
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_128,plain,(
    ! [A_20] : k3_xboole_0(k1_xboole_0,A_20) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_124])).

tff(c_216,plain,(
    ! [A_57,B_58] : k5_xboole_0(A_57,k3_xboole_0(A_57,B_58)) = k4_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_237,plain,(
    ! [A_59] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_216])).

tff(c_228,plain,(
    ! [A_20] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_216])).

tff(c_240,plain,(
    ! [A_59,A_20] : k4_xboole_0(k1_xboole_0,A_59) = k4_xboole_0(k1_xboole_0,A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_228])).

tff(c_129,plain,(
    ! [A_46] : k3_xboole_0(k1_xboole_0,A_46) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_124])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_134,plain,(
    ! [A_46] : k3_xboole_0(A_46,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_2])).

tff(c_225,plain,(
    ! [A_46] : k5_xboole_0(A_46,k1_xboole_0) = k4_xboole_0(A_46,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_216])).

tff(c_10,plain,(
    ! [D_12,B_8,A_7] :
      ( ~ r2_hidden(D_12,B_8)
      | ~ r2_hidden(D_12,k4_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_243,plain,(
    ! [D_12,A_59] :
      ( ~ r2_hidden(D_12,A_59)
      | ~ r2_hidden(D_12,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_10])).

tff(c_376,plain,(
    ! [D_71,A_72] :
      ( ~ r2_hidden(D_71,A_72)
      | ~ r2_hidden(D_71,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_243])).

tff(c_385,plain,(
    ~ r2_hidden('#skF_4',k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_64,c_376])).

tff(c_396,plain,(
    ! [A_59] : ~ r2_hidden('#skF_4',k4_xboole_0(k1_xboole_0,A_59)) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_385])).

tff(c_455,plain,(
    ! [A_59] : ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',A_59)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_451,c_396])).

tff(c_701,plain,(
    ! [B_99] :
      ( r2_hidden('#skF_4',B_99)
      | ~ r2_hidden('#skF_4','#skF_5') ) ),
    inference(resolution,[status(thm)],[c_697,c_455])).

tff(c_725,plain,(
    ! [B_99] : r2_hidden('#skF_4',B_99) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_701])).

tff(c_734,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_725,c_455])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:24:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.36  
% 2.65/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.36  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.65/1.36  
% 2.65/1.36  %Foreground sorts:
% 2.65/1.36  
% 2.65/1.36  
% 2.65/1.36  %Background operators:
% 2.65/1.36  
% 2.65/1.36  
% 2.65/1.36  %Foreground operators:
% 2.65/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.65/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.65/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.65/1.36  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.65/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.65/1.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.65/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.65/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.65/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.65/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.65/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.65/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.65/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.65/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.65/1.36  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.65/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.65/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.65/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.65/1.36  
% 2.72/1.37  tff(f_91, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 2.72/1.37  tff(f_43, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.72/1.37  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.72/1.37  tff(f_79, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.72/1.37  tff(f_86, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 2.72/1.37  tff(f_58, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.72/1.37  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.72/1.37  tff(f_52, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.72/1.37  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.72/1.37  tff(c_64, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.72/1.37  tff(c_697, plain, (![D_97, A_98, B_99]: (r2_hidden(D_97, k4_xboole_0(A_98, B_99)) | r2_hidden(D_97, B_99) | ~r2_hidden(D_97, A_98))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.72/1.37  tff(c_75, plain, (![B_37, A_38]: (~r2_hidden(B_37, A_38) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.72/1.37  tff(c_79, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_64, c_75])).
% 2.72/1.37  tff(c_316, plain, (![B_66, A_67]: (m1_subset_1(B_66, A_67) | ~r2_hidden(B_66, A_67) | v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.72/1.37  tff(c_325, plain, (m1_subset_1('#skF_4', '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_64, c_316])).
% 2.72/1.37  tff(c_330, plain, (m1_subset_1('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_79, c_325])).
% 2.72/1.37  tff(c_441, plain, (![B_78, A_79]: (m1_subset_1(k1_tarski(B_78), k1_zfmisc_1(A_79)) | k1_xboole_0=A_79 | ~m1_subset_1(B_78, A_79))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.72/1.37  tff(c_62, plain, (~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.72/1.37  tff(c_447, plain, (k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_441, c_62])).
% 2.72/1.37  tff(c_451, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_330, c_447])).
% 2.72/1.37  tff(c_42, plain, (![A_20]: (r1_tarski(k1_xboole_0, A_20))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.72/1.37  tff(c_124, plain, (![A_44, B_45]: (k3_xboole_0(A_44, B_45)=A_44 | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.72/1.37  tff(c_128, plain, (![A_20]: (k3_xboole_0(k1_xboole_0, A_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_124])).
% 2.72/1.37  tff(c_216, plain, (![A_57, B_58]: (k5_xboole_0(A_57, k3_xboole_0(A_57, B_58))=k4_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.72/1.37  tff(c_237, plain, (![A_59]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_59))), inference(superposition, [status(thm), theory('equality')], [c_128, c_216])).
% 2.72/1.37  tff(c_228, plain, (![A_20]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_20))), inference(superposition, [status(thm), theory('equality')], [c_128, c_216])).
% 2.72/1.37  tff(c_240, plain, (![A_59, A_20]: (k4_xboole_0(k1_xboole_0, A_59)=k4_xboole_0(k1_xboole_0, A_20))), inference(superposition, [status(thm), theory('equality')], [c_237, c_228])).
% 2.72/1.37  tff(c_129, plain, (![A_46]: (k3_xboole_0(k1_xboole_0, A_46)=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_124])).
% 2.72/1.37  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.72/1.37  tff(c_134, plain, (![A_46]: (k3_xboole_0(A_46, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_129, c_2])).
% 2.72/1.37  tff(c_225, plain, (![A_46]: (k5_xboole_0(A_46, k1_xboole_0)=k4_xboole_0(A_46, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_134, c_216])).
% 2.72/1.37  tff(c_10, plain, (![D_12, B_8, A_7]: (~r2_hidden(D_12, B_8) | ~r2_hidden(D_12, k4_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.72/1.37  tff(c_243, plain, (![D_12, A_59]: (~r2_hidden(D_12, A_59) | ~r2_hidden(D_12, k5_xboole_0(k1_xboole_0, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_237, c_10])).
% 2.72/1.37  tff(c_376, plain, (![D_71, A_72]: (~r2_hidden(D_71, A_72) | ~r2_hidden(D_71, k4_xboole_0(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_243])).
% 2.72/1.37  tff(c_385, plain, (~r2_hidden('#skF_4', k4_xboole_0(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_64, c_376])).
% 2.72/1.37  tff(c_396, plain, (![A_59]: (~r2_hidden('#skF_4', k4_xboole_0(k1_xboole_0, A_59)))), inference(superposition, [status(thm), theory('equality')], [c_240, c_385])).
% 2.72/1.37  tff(c_455, plain, (![A_59]: (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', A_59)))), inference(demodulation, [status(thm), theory('equality')], [c_451, c_396])).
% 2.72/1.37  tff(c_701, plain, (![B_99]: (r2_hidden('#skF_4', B_99) | ~r2_hidden('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_697, c_455])).
% 2.72/1.37  tff(c_725, plain, (![B_99]: (r2_hidden('#skF_4', B_99))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_701])).
% 2.72/1.37  tff(c_734, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_725, c_455])).
% 2.72/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.37  
% 2.72/1.37  Inference rules
% 2.72/1.37  ----------------------
% 2.72/1.37  #Ref     : 0
% 2.72/1.37  #Sup     : 184
% 2.72/1.37  #Fact    : 0
% 2.72/1.37  #Define  : 0
% 2.72/1.37  #Split   : 3
% 2.72/1.37  #Chain   : 0
% 2.72/1.37  #Close   : 0
% 2.72/1.37  
% 2.72/1.37  Ordering : KBO
% 2.72/1.37  
% 2.72/1.37  Simplification rules
% 2.72/1.37  ----------------------
% 2.72/1.37  #Subsume      : 66
% 2.72/1.37  #Demod        : 58
% 2.72/1.37  #Tautology    : 77
% 2.72/1.37  #SimpNegUnit  : 4
% 2.72/1.37  #BackRed      : 15
% 2.72/1.37  
% 2.72/1.37  #Partial instantiations: 0
% 2.72/1.37  #Strategies tried      : 1
% 2.72/1.37  
% 2.72/1.37  Timing (in seconds)
% 2.72/1.37  ----------------------
% 2.72/1.38  Preprocessing        : 0.32
% 2.72/1.38  Parsing              : 0.16
% 2.72/1.38  CNF conversion       : 0.02
% 2.72/1.38  Main loop            : 0.30
% 2.72/1.38  Inferencing          : 0.10
% 2.72/1.38  Reduction            : 0.10
% 2.72/1.38  Demodulation         : 0.08
% 2.72/1.38  BG Simplification    : 0.02
% 2.72/1.38  Subsumption          : 0.06
% 2.72/1.38  Abstraction          : 0.02
% 2.72/1.38  MUC search           : 0.00
% 2.72/1.38  Cooper               : 0.00
% 2.72/1.38  Total                : 0.65
% 2.72/1.38  Index Insertion      : 0.00
% 2.72/1.38  Index Deletion       : 0.00
% 2.72/1.38  Index Matching       : 0.00
% 2.72/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
