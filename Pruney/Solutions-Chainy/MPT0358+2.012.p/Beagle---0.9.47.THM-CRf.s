%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:01 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 127 expanded)
%              Number of leaves         :   28 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :   82 ( 193 expanded)
%              Number of equality atoms :   19 (  61 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_60,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_58,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,(
    ! [A_22] : k1_subset_1(A_22) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_50,plain,
    ( r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_6'))
    | k1_subset_1('#skF_5') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_52,plain,
    ( r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_50])).

tff(c_109,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_36,plain,(
    ! [A_21] : k4_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_110,plain,(
    ! [A_21] : k4_xboole_0(A_21,'#skF_6') = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_36])).

tff(c_136,plain,(
    ! [D_36,B_37,A_38] :
      ( ~ r2_hidden(D_36,B_37)
      | ~ r2_hidden(D_36,k4_xboole_0(A_38,B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_145,plain,(
    ! [D_39,A_40] :
      ( ~ r2_hidden(D_39,'#skF_6')
      | ~ r2_hidden(D_39,A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_136])).

tff(c_149,plain,(
    ! [A_40] :
      ( ~ r2_hidden('#skF_1'('#skF_6'),A_40)
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_6,c_145])).

tff(c_152,plain,(
    ! [A_43] : ~ r2_hidden('#skF_1'('#skF_6'),A_43) ),
    inference(splitLeft,[status(thm)],[c_149])).

tff(c_157,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_152])).

tff(c_187,plain,(
    ! [A_49,B_50] :
      ( r2_hidden('#skF_2'(A_49,B_50),A_49)
      | r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_212,plain,(
    ! [A_52,B_53] :
      ( ~ v1_xboole_0(A_52)
      | r1_tarski(A_52,B_53) ) ),
    inference(resolution,[status(thm)],[c_187,c_4])).

tff(c_44,plain,
    ( k1_subset_1('#skF_5') != '#skF_6'
    | ~ r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_51,plain,
    ( k1_xboole_0 != '#skF_6'
    | ~ r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_44])).

tff(c_118,plain,(
    ~ r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_51])).

tff(c_215,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_212,c_118])).

tff(c_219,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_215])).

tff(c_220,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_226,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_2'(A_54,B_55),A_54)
      | r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_246,plain,(
    ! [A_57,B_58] :
      ( ~ v1_xboole_0(A_57)
      | r1_tarski(A_57,B_58) ) ),
    inference(resolution,[status(thm)],[c_226,c_4])).

tff(c_249,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_246,c_118])).

tff(c_253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_249])).

tff(c_255,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_254,plain,(
    r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_367,plain,(
    ! [C_81,B_82,A_83] :
      ( r2_hidden(C_81,B_82)
      | ~ r2_hidden(C_81,A_83)
      | ~ r1_tarski(A_83,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_373,plain,(
    ! [A_3,B_82] :
      ( r2_hidden('#skF_1'(A_3),B_82)
      | ~ r1_tarski(A_3,B_82)
      | v1_xboole_0(A_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_367])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_451,plain,(
    ! [A_92,B_93] :
      ( k4_xboole_0(A_92,B_93) = k3_subset_1(A_92,B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_455,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k3_subset_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_451])).

tff(c_16,plain,(
    ! [D_17,B_13,A_12] :
      ( ~ r2_hidden(D_17,B_13)
      | ~ r2_hidden(D_17,k4_xboole_0(A_12,B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_524,plain,(
    ! [D_98] :
      ( ~ r2_hidden(D_98,'#skF_6')
      | ~ r2_hidden(D_98,k3_subset_1('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_16])).

tff(c_918,plain,(
    ! [A_121] :
      ( ~ r2_hidden('#skF_1'(A_121),'#skF_6')
      | ~ r1_tarski(A_121,k3_subset_1('#skF_5','#skF_6'))
      | v1_xboole_0(A_121) ) ),
    inference(resolution,[status(thm)],[c_373,c_524])).

tff(c_934,plain,
    ( ~ r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_6'))
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_918])).

tff(c_943,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_934])).

tff(c_32,plain,(
    ! [A_18] :
      ( k1_xboole_0 = A_18
      | ~ v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_946,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_943,c_32])).

tff(c_950,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_255,c_946])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:40:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.43  
% 2.75/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.43  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2
% 2.75/1.43  
% 2.75/1.43  %Foreground sorts:
% 2.75/1.43  
% 2.75/1.43  
% 2.75/1.43  %Background operators:
% 2.75/1.43  
% 2.75/1.43  
% 2.75/1.43  %Foreground operators:
% 2.75/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.75/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.75/1.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.75/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.75/1.43  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.75/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.75/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.75/1.43  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.75/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.75/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.75/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.75/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.43  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.75/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.75/1.43  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.75/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.75/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.75/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.75/1.43  
% 2.75/1.45  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.75/1.45  tff(f_60, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.75/1.45  tff(f_71, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 2.75/1.45  tff(f_58, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.75/1.45  tff(f_50, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.75/1.45  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.75/1.45  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.75/1.45  tff(f_54, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.75/1.45  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.75/1.45  tff(c_38, plain, (![A_22]: (k1_subset_1(A_22)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.75/1.45  tff(c_50, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_6')) | k1_subset_1('#skF_5')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.75/1.45  tff(c_52, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_6')) | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_50])).
% 2.75/1.45  tff(c_109, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_52])).
% 2.75/1.45  tff(c_36, plain, (![A_21]: (k4_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.75/1.45  tff(c_110, plain, (![A_21]: (k4_xboole_0(A_21, '#skF_6')=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_109, c_36])).
% 2.75/1.45  tff(c_136, plain, (![D_36, B_37, A_38]: (~r2_hidden(D_36, B_37) | ~r2_hidden(D_36, k4_xboole_0(A_38, B_37)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.75/1.45  tff(c_145, plain, (![D_39, A_40]: (~r2_hidden(D_39, '#skF_6') | ~r2_hidden(D_39, A_40))), inference(superposition, [status(thm), theory('equality')], [c_110, c_136])).
% 2.75/1.45  tff(c_149, plain, (![A_40]: (~r2_hidden('#skF_1'('#skF_6'), A_40) | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_6, c_145])).
% 2.75/1.45  tff(c_152, plain, (![A_43]: (~r2_hidden('#skF_1'('#skF_6'), A_43))), inference(splitLeft, [status(thm)], [c_149])).
% 2.75/1.45  tff(c_157, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_6, c_152])).
% 2.75/1.45  tff(c_187, plain, (![A_49, B_50]: (r2_hidden('#skF_2'(A_49, B_50), A_49) | r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.75/1.45  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.75/1.45  tff(c_212, plain, (![A_52, B_53]: (~v1_xboole_0(A_52) | r1_tarski(A_52, B_53))), inference(resolution, [status(thm)], [c_187, c_4])).
% 2.75/1.45  tff(c_44, plain, (k1_subset_1('#skF_5')!='#skF_6' | ~r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.75/1.45  tff(c_51, plain, (k1_xboole_0!='#skF_6' | ~r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_44])).
% 2.75/1.45  tff(c_118, plain, (~r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_51])).
% 2.75/1.45  tff(c_215, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_212, c_118])).
% 2.75/1.45  tff(c_219, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_157, c_215])).
% 2.75/1.45  tff(c_220, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_149])).
% 2.75/1.45  tff(c_226, plain, (![A_54, B_55]: (r2_hidden('#skF_2'(A_54, B_55), A_54) | r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.75/1.45  tff(c_246, plain, (![A_57, B_58]: (~v1_xboole_0(A_57) | r1_tarski(A_57, B_58))), inference(resolution, [status(thm)], [c_226, c_4])).
% 2.75/1.45  tff(c_249, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_246, c_118])).
% 2.75/1.45  tff(c_253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_220, c_249])).
% 2.75/1.45  tff(c_255, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_52])).
% 2.75/1.45  tff(c_254, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_52])).
% 2.75/1.45  tff(c_367, plain, (![C_81, B_82, A_83]: (r2_hidden(C_81, B_82) | ~r2_hidden(C_81, A_83) | ~r1_tarski(A_83, B_82))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.75/1.45  tff(c_373, plain, (![A_3, B_82]: (r2_hidden('#skF_1'(A_3), B_82) | ~r1_tarski(A_3, B_82) | v1_xboole_0(A_3))), inference(resolution, [status(thm)], [c_6, c_367])).
% 2.75/1.45  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.75/1.45  tff(c_451, plain, (![A_92, B_93]: (k4_xboole_0(A_92, B_93)=k3_subset_1(A_92, B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(A_92)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.75/1.45  tff(c_455, plain, (k4_xboole_0('#skF_5', '#skF_6')=k3_subset_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_42, c_451])).
% 2.75/1.45  tff(c_16, plain, (![D_17, B_13, A_12]: (~r2_hidden(D_17, B_13) | ~r2_hidden(D_17, k4_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.75/1.45  tff(c_524, plain, (![D_98]: (~r2_hidden(D_98, '#skF_6') | ~r2_hidden(D_98, k3_subset_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_455, c_16])).
% 2.75/1.45  tff(c_918, plain, (![A_121]: (~r2_hidden('#skF_1'(A_121), '#skF_6') | ~r1_tarski(A_121, k3_subset_1('#skF_5', '#skF_6')) | v1_xboole_0(A_121))), inference(resolution, [status(thm)], [c_373, c_524])).
% 2.75/1.45  tff(c_934, plain, (~r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_6')) | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_6, c_918])).
% 2.75/1.45  tff(c_943, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_254, c_934])).
% 2.75/1.45  tff(c_32, plain, (![A_18]: (k1_xboole_0=A_18 | ~v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.75/1.45  tff(c_946, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_943, c_32])).
% 2.75/1.45  tff(c_950, plain, $false, inference(negUnitSimplification, [status(thm)], [c_255, c_946])).
% 2.75/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.45  
% 2.75/1.45  Inference rules
% 2.75/1.45  ----------------------
% 2.75/1.45  #Ref     : 0
% 2.75/1.45  #Sup     : 190
% 2.75/1.45  #Fact    : 0
% 2.75/1.45  #Define  : 0
% 2.75/1.45  #Split   : 5
% 2.75/1.45  #Chain   : 0
% 2.75/1.45  #Close   : 0
% 2.75/1.45  
% 2.75/1.45  Ordering : KBO
% 2.75/1.45  
% 2.75/1.45  Simplification rules
% 2.75/1.45  ----------------------
% 2.75/1.45  #Subsume      : 24
% 2.75/1.45  #Demod        : 41
% 2.75/1.45  #Tautology    : 69
% 2.75/1.45  #SimpNegUnit  : 12
% 2.75/1.45  #BackRed      : 4
% 2.75/1.45  
% 2.75/1.45  #Partial instantiations: 0
% 2.75/1.45  #Strategies tried      : 1
% 2.75/1.45  
% 2.75/1.45  Timing (in seconds)
% 2.75/1.45  ----------------------
% 2.75/1.45  Preprocessing        : 0.29
% 2.75/1.45  Parsing              : 0.15
% 2.75/1.45  CNF conversion       : 0.02
% 2.75/1.45  Main loop            : 0.36
% 2.75/1.45  Inferencing          : 0.13
% 2.75/1.45  Reduction            : 0.10
% 2.75/1.45  Demodulation         : 0.07
% 2.75/1.45  BG Simplification    : 0.02
% 2.75/1.45  Subsumption          : 0.07
% 2.75/1.45  Abstraction          : 0.02
% 2.75/1.45  MUC search           : 0.00
% 2.75/1.45  Cooper               : 0.00
% 2.75/1.45  Total                : 0.68
% 2.75/1.45  Index Insertion      : 0.00
% 2.75/1.45  Index Deletion       : 0.00
% 2.75/1.45  Index Matching       : 0.00
% 2.75/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
