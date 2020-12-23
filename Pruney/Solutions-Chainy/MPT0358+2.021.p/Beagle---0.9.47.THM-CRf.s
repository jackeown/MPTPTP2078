%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:02 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 152 expanded)
%              Number of leaves         :   31 (  64 expanded)
%              Depth                    :   11
%              Number of atoms          :   77 ( 235 expanded)
%              Number of equality atoms :   31 ( 109 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_4 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_108,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_54,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_90,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(c_70,plain,(
    ! [A_30] : k1_subset_1(A_30) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_82,plain,
    ( k1_subset_1('#skF_8') != '#skF_9'
    | ~ r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_90,plain,
    ( k1_xboole_0 != '#skF_9'
    | ~ r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_82])).

tff(c_133,plain,(
    ~ r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_88,plain,
    ( r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9'))
    | k1_subset_1('#skF_8') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_89,plain,
    ( r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9'))
    | k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_88])).

tff(c_134,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_89])).

tff(c_40,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_5'(A_15),A_15)
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_135,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_5'(A_15),A_15)
      | A_15 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_40])).

tff(c_187,plain,(
    ! [D_59,A_60,B_61] :
      ( r2_hidden(D_59,A_60)
      | ~ r2_hidden(D_59,k4_xboole_0(A_60,B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_192,plain,(
    ! [A_60,B_61] :
      ( r2_hidden('#skF_5'(k4_xboole_0(A_60,B_61)),A_60)
      | k4_xboole_0(A_60,B_61) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_135,c_187])).

tff(c_1558,plain,(
    ! [A_160,B_161] :
      ( r2_hidden('#skF_5'(k4_xboole_0(A_160,B_161)),A_160)
      | k4_xboole_0(A_160,B_161) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_135,c_187])).

tff(c_251,plain,(
    ! [D_66,B_67,A_68] :
      ( ~ r2_hidden(D_66,B_67)
      | ~ r2_hidden(D_66,k4_xboole_0(A_68,B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_264,plain,(
    ! [A_68,B_67] :
      ( ~ r2_hidden('#skF_5'(k4_xboole_0(A_68,B_67)),B_67)
      | k4_xboole_0(A_68,B_67) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_135,c_251])).

tff(c_1633,plain,(
    ! [A_162] : k4_xboole_0(A_162,A_162) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1558,c_264])).

tff(c_24,plain,(
    ! [D_14,B_10,A_9] :
      ( ~ r2_hidden(D_14,B_10)
      | ~ r2_hidden(D_14,k4_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1746,plain,(
    ! [D_167,A_168] :
      ( ~ r2_hidden(D_167,A_168)
      | ~ r2_hidden(D_167,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1633,c_24])).

tff(c_1835,plain,(
    ! [A_174] :
      ( ~ r2_hidden('#skF_5'(A_174),'#skF_9')
      | A_174 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_135,c_1746])).

tff(c_1851,plain,(
    ! [B_61] : k4_xboole_0('#skF_9',B_61) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_192,c_1835])).

tff(c_42,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | k4_xboole_0(A_17,B_18) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_165,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(A_55,B_56)
      | k4_xboole_0(A_55,B_56) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_42])).

tff(c_177,plain,(
    k4_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9')) != '#skF_9' ),
    inference(resolution,[status(thm)],[c_165,c_133])).

tff(c_1860,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1851,c_177])).

tff(c_1861,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_1862,plain,(
    r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_1895,plain,(
    ! [A_185,B_186] :
      ( k3_xboole_0(A_185,B_186) = A_185
      | ~ r1_tarski(A_185,B_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1899,plain,(
    k3_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9')) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1862,c_1895])).

tff(c_1998,plain,(
    ! [D_206,B_207,A_208] :
      ( r2_hidden(D_206,B_207)
      | ~ r2_hidden(D_206,k3_xboole_0(A_208,B_207)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2001,plain,(
    ! [D_206] :
      ( r2_hidden(D_206,k3_subset_1('#skF_8','#skF_9'))
      | ~ r2_hidden(D_206,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1899,c_1998])).

tff(c_80,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2294,plain,(
    ! [A_227,B_228] :
      ( k4_xboole_0(A_227,B_228) = k3_subset_1(A_227,B_228)
      | ~ m1_subset_1(B_228,k1_zfmisc_1(A_227)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2318,plain,(
    k4_xboole_0('#skF_8','#skF_9') = k3_subset_1('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_80,c_2294])).

tff(c_2361,plain,(
    ! [D_230] :
      ( ~ r2_hidden(D_230,'#skF_9')
      | ~ r2_hidden(D_230,k3_subset_1('#skF_8','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2318,c_24])).

tff(c_2379,plain,(
    ! [D_231] : ~ r2_hidden(D_231,'#skF_9') ),
    inference(resolution,[status(thm)],[c_2001,c_2361])).

tff(c_2387,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_40,c_2379])).

tff(c_2392,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1861,c_2387])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:25:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.60/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.62  
% 3.60/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.62  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_4 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7
% 3.60/1.62  
% 3.60/1.62  %Foreground sorts:
% 3.60/1.62  
% 3.60/1.62  
% 3.60/1.62  %Background operators:
% 3.60/1.62  
% 3.60/1.62  
% 3.60/1.62  %Foreground operators:
% 3.60/1.62  tff('#skF_5', type, '#skF_5': $i > $i).
% 3.60/1.62  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.60/1.62  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.60/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.60/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.60/1.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.60/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.60/1.62  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.60/1.62  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.60/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.60/1.62  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.60/1.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.60/1.62  tff('#skF_9', type, '#skF_9': $i).
% 3.60/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.60/1.62  tff('#skF_8', type, '#skF_8': $i).
% 3.60/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.60/1.62  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.60/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.60/1.62  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.60/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.60/1.62  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.60/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.60/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.60/1.62  
% 3.60/1.63  tff(f_86, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 3.60/1.63  tff(f_108, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 3.60/1.63  tff(f_54, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.60/1.63  tff(f_46, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.60/1.63  tff(f_58, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.60/1.63  tff(f_64, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.60/1.63  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.60/1.63  tff(f_90, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.60/1.63  tff(c_70, plain, (![A_30]: (k1_subset_1(A_30)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.60/1.63  tff(c_82, plain, (k1_subset_1('#skF_8')!='#skF_9' | ~r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.60/1.63  tff(c_90, plain, (k1_xboole_0!='#skF_9' | ~r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_82])).
% 3.60/1.63  tff(c_133, plain, (~r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(splitLeft, [status(thm)], [c_90])).
% 3.60/1.63  tff(c_88, plain, (r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9')) | k1_subset_1('#skF_8')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.60/1.63  tff(c_89, plain, (r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9')) | k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_88])).
% 3.60/1.63  tff(c_134, plain, (k1_xboole_0='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_133, c_89])).
% 3.60/1.63  tff(c_40, plain, (![A_15]: (r2_hidden('#skF_5'(A_15), A_15) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.60/1.63  tff(c_135, plain, (![A_15]: (r2_hidden('#skF_5'(A_15), A_15) | A_15='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_40])).
% 3.60/1.63  tff(c_187, plain, (![D_59, A_60, B_61]: (r2_hidden(D_59, A_60) | ~r2_hidden(D_59, k4_xboole_0(A_60, B_61)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.60/1.63  tff(c_192, plain, (![A_60, B_61]: (r2_hidden('#skF_5'(k4_xboole_0(A_60, B_61)), A_60) | k4_xboole_0(A_60, B_61)='#skF_9')), inference(resolution, [status(thm)], [c_135, c_187])).
% 3.60/1.63  tff(c_1558, plain, (![A_160, B_161]: (r2_hidden('#skF_5'(k4_xboole_0(A_160, B_161)), A_160) | k4_xboole_0(A_160, B_161)='#skF_9')), inference(resolution, [status(thm)], [c_135, c_187])).
% 3.60/1.63  tff(c_251, plain, (![D_66, B_67, A_68]: (~r2_hidden(D_66, B_67) | ~r2_hidden(D_66, k4_xboole_0(A_68, B_67)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.60/1.63  tff(c_264, plain, (![A_68, B_67]: (~r2_hidden('#skF_5'(k4_xboole_0(A_68, B_67)), B_67) | k4_xboole_0(A_68, B_67)='#skF_9')), inference(resolution, [status(thm)], [c_135, c_251])).
% 3.60/1.63  tff(c_1633, plain, (![A_162]: (k4_xboole_0(A_162, A_162)='#skF_9')), inference(resolution, [status(thm)], [c_1558, c_264])).
% 3.60/1.63  tff(c_24, plain, (![D_14, B_10, A_9]: (~r2_hidden(D_14, B_10) | ~r2_hidden(D_14, k4_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.60/1.63  tff(c_1746, plain, (![D_167, A_168]: (~r2_hidden(D_167, A_168) | ~r2_hidden(D_167, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1633, c_24])).
% 3.60/1.63  tff(c_1835, plain, (![A_174]: (~r2_hidden('#skF_5'(A_174), '#skF_9') | A_174='#skF_9')), inference(resolution, [status(thm)], [c_135, c_1746])).
% 3.60/1.63  tff(c_1851, plain, (![B_61]: (k4_xboole_0('#skF_9', B_61)='#skF_9')), inference(resolution, [status(thm)], [c_192, c_1835])).
% 3.60/1.63  tff(c_42, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | k4_xboole_0(A_17, B_18)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.60/1.63  tff(c_165, plain, (![A_55, B_56]: (r1_tarski(A_55, B_56) | k4_xboole_0(A_55, B_56)!='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_42])).
% 3.60/1.63  tff(c_177, plain, (k4_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9'))!='#skF_9'), inference(resolution, [status(thm)], [c_165, c_133])).
% 3.60/1.63  tff(c_1860, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1851, c_177])).
% 3.60/1.63  tff(c_1861, plain, (k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_90])).
% 3.60/1.63  tff(c_1862, plain, (r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(splitRight, [status(thm)], [c_90])).
% 3.60/1.63  tff(c_1895, plain, (![A_185, B_186]: (k3_xboole_0(A_185, B_186)=A_185 | ~r1_tarski(A_185, B_186))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.60/1.63  tff(c_1899, plain, (k3_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9'))='#skF_9'), inference(resolution, [status(thm)], [c_1862, c_1895])).
% 3.60/1.63  tff(c_1998, plain, (![D_206, B_207, A_208]: (r2_hidden(D_206, B_207) | ~r2_hidden(D_206, k3_xboole_0(A_208, B_207)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.60/1.63  tff(c_2001, plain, (![D_206]: (r2_hidden(D_206, k3_subset_1('#skF_8', '#skF_9')) | ~r2_hidden(D_206, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1899, c_1998])).
% 3.60/1.63  tff(c_80, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.60/1.63  tff(c_2294, plain, (![A_227, B_228]: (k4_xboole_0(A_227, B_228)=k3_subset_1(A_227, B_228) | ~m1_subset_1(B_228, k1_zfmisc_1(A_227)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.60/1.63  tff(c_2318, plain, (k4_xboole_0('#skF_8', '#skF_9')=k3_subset_1('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_80, c_2294])).
% 3.60/1.63  tff(c_2361, plain, (![D_230]: (~r2_hidden(D_230, '#skF_9') | ~r2_hidden(D_230, k3_subset_1('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_2318, c_24])).
% 3.60/1.63  tff(c_2379, plain, (![D_231]: (~r2_hidden(D_231, '#skF_9'))), inference(resolution, [status(thm)], [c_2001, c_2361])).
% 3.60/1.63  tff(c_2387, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_40, c_2379])).
% 3.60/1.63  tff(c_2392, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1861, c_2387])).
% 3.60/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.63  
% 3.60/1.63  Inference rules
% 3.60/1.63  ----------------------
% 3.60/1.63  #Ref     : 0
% 3.60/1.63  #Sup     : 539
% 3.60/1.63  #Fact    : 0
% 3.60/1.63  #Define  : 0
% 3.60/1.63  #Split   : 9
% 3.60/1.63  #Chain   : 0
% 3.60/1.63  #Close   : 0
% 3.60/1.63  
% 3.60/1.63  Ordering : KBO
% 3.60/1.63  
% 3.60/1.63  Simplification rules
% 3.60/1.63  ----------------------
% 3.60/1.63  #Subsume      : 94
% 3.60/1.63  #Demod        : 106
% 3.60/1.63  #Tautology    : 216
% 3.60/1.63  #SimpNegUnit  : 39
% 3.60/1.63  #BackRed      : 8
% 3.60/1.63  
% 3.60/1.63  #Partial instantiations: 0
% 3.60/1.63  #Strategies tried      : 1
% 3.60/1.63  
% 3.60/1.63  Timing (in seconds)
% 3.60/1.63  ----------------------
% 3.60/1.63  Preprocessing        : 0.33
% 3.60/1.63  Parsing              : 0.17
% 3.60/1.63  CNF conversion       : 0.03
% 3.60/1.63  Main loop            : 0.55
% 3.60/1.63  Inferencing          : 0.19
% 3.60/1.63  Reduction            : 0.17
% 3.60/1.63  Demodulation         : 0.12
% 3.60/1.63  BG Simplification    : 0.03
% 3.60/1.64  Subsumption          : 0.11
% 3.60/1.64  Abstraction          : 0.03
% 3.60/1.64  MUC search           : 0.00
% 3.60/1.64  Cooper               : 0.00
% 3.60/1.64  Total                : 0.91
% 3.60/1.64  Index Insertion      : 0.00
% 3.60/1.64  Index Deletion       : 0.00
% 3.60/1.64  Index Matching       : 0.00
% 3.60/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
