%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:07 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   65 (  95 expanded)
%              Number of leaves         :   30 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :   74 ( 136 expanded)
%              Number of equality atoms :   29 (  51 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_67,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_58,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_50,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_149,plain,(
    ! [A_47,B_48] :
      ( ~ r2_hidden('#skF_1'(A_47,B_48),B_48)
      | r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_160,plain,(
    ! [A_49] : r1_tarski(A_49,A_49) ),
    inference(resolution,[status(thm)],[c_6,c_149])).

tff(c_30,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_164,plain,(
    ! [A_49] : k3_xboole_0(A_49,A_49) = A_49 ),
    inference(resolution,[status(thm)],[c_160,c_30])).

tff(c_174,plain,(
    ! [A_51,B_52] : k5_xboole_0(A_51,k3_xboole_0(A_51,B_52)) = k4_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_186,plain,(
    ! [A_53] : k5_xboole_0(A_53,A_53) = k4_xboole_0(A_53,A_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_174])).

tff(c_46,plain,(
    ! [A_24] : k1_subset_1(A_24) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_52,plain,
    ( k1_subset_1('#skF_7') != '#skF_8'
    | ~ r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_59,plain,
    ( k1_xboole_0 != '#skF_8'
    | ~ r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_52])).

tff(c_78,plain,(
    ~ r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_59])).

tff(c_58,plain,
    ( r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_8'))
    | k1_subset_1('#skF_7') = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_60,plain,
    ( r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_58])).

tff(c_91,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_60])).

tff(c_32,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_93,plain,(
    ! [A_18] : k5_xboole_0(A_18,'#skF_8') = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_32])).

tff(c_193,plain,(
    k4_xboole_0('#skF_8','#skF_8') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_93])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_214,plain,(
    ! [D_54] :
      ( ~ r2_hidden(D_54,'#skF_8')
      | ~ r2_hidden(D_54,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_10])).

tff(c_240,plain,(
    ! [B_59] :
      ( ~ r2_hidden('#skF_1'('#skF_8',B_59),'#skF_8')
      | r1_tarski('#skF_8',B_59) ) ),
    inference(resolution,[status(thm)],[c_6,c_214])).

tff(c_245,plain,(
    ! [B_2] : r1_tarski('#skF_8',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_240])).

tff(c_249,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_78])).

tff(c_250,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_59])).

tff(c_251,plain,(
    r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_59])).

tff(c_26,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_4'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_328,plain,(
    ! [C_78,B_79,A_80] :
      ( r2_hidden(C_78,B_79)
      | ~ r2_hidden(C_78,A_80)
      | ~ r1_tarski(A_80,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_557,plain,(
    ! [A_104,B_105] :
      ( r2_hidden('#skF_4'(A_104),B_105)
      | ~ r1_tarski(A_104,B_105)
      | k1_xboole_0 = A_104 ) ),
    inference(resolution,[status(thm)],[c_26,c_328])).

tff(c_50,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_415,plain,(
    ! [A_87,B_88] :
      ( k4_xboole_0(A_87,B_88) = k3_subset_1(A_87,B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_419,plain,(
    k4_xboole_0('#skF_7','#skF_8') = k3_subset_1('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_50,c_415])).

tff(c_464,plain,(
    ! [D_11] :
      ( ~ r2_hidden(D_11,'#skF_8')
      | ~ r2_hidden(D_11,k3_subset_1('#skF_7','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_419,c_10])).

tff(c_1544,plain,(
    ! [A_163] :
      ( ~ r2_hidden('#skF_4'(A_163),'#skF_8')
      | ~ r1_tarski(A_163,k3_subset_1('#skF_7','#skF_8'))
      | k1_xboole_0 = A_163 ) ),
    inference(resolution,[status(thm)],[c_557,c_464])).

tff(c_1563,plain,
    ( ~ r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_26,c_1544])).

tff(c_1573,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_1563])).

tff(c_1575,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_250,c_1573])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:48:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.59  
% 3.22/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.60  %$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_5
% 3.22/1.60  
% 3.22/1.60  %Foreground sorts:
% 3.22/1.60  
% 3.22/1.60  
% 3.22/1.60  %Background operators:
% 3.22/1.60  
% 3.22/1.60  
% 3.22/1.60  %Foreground operators:
% 3.22/1.60  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.22/1.60  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.22/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.22/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.22/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.22/1.60  tff('#skF_7', type, '#skF_7': $i).
% 3.22/1.60  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.22/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.22/1.60  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.22/1.60  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.22/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.22/1.60  tff('#skF_8', type, '#skF_8': $i).
% 3.22/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.60  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.22/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.60  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.22/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.22/1.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.22/1.60  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.22/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.22/1.60  
% 3.22/1.61  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.22/1.61  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.22/1.61  tff(f_52, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.22/1.61  tff(f_67, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 3.22/1.61  tff(f_78, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 3.22/1.61  tff(f_58, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.22/1.61  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.22/1.61  tff(f_50, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.22/1.61  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.22/1.61  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.22/1.61  tff(c_149, plain, (![A_47, B_48]: (~r2_hidden('#skF_1'(A_47, B_48), B_48) | r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.22/1.61  tff(c_160, plain, (![A_49]: (r1_tarski(A_49, A_49))), inference(resolution, [status(thm)], [c_6, c_149])).
% 3.22/1.61  tff(c_30, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.22/1.61  tff(c_164, plain, (![A_49]: (k3_xboole_0(A_49, A_49)=A_49)), inference(resolution, [status(thm)], [c_160, c_30])).
% 3.22/1.61  tff(c_174, plain, (![A_51, B_52]: (k5_xboole_0(A_51, k3_xboole_0(A_51, B_52))=k4_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.22/1.61  tff(c_186, plain, (![A_53]: (k5_xboole_0(A_53, A_53)=k4_xboole_0(A_53, A_53))), inference(superposition, [status(thm), theory('equality')], [c_164, c_174])).
% 3.22/1.61  tff(c_46, plain, (![A_24]: (k1_subset_1(A_24)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.22/1.61  tff(c_52, plain, (k1_subset_1('#skF_7')!='#skF_8' | ~r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.22/1.61  tff(c_59, plain, (k1_xboole_0!='#skF_8' | ~r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_52])).
% 3.22/1.61  tff(c_78, plain, (~r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_8'))), inference(splitLeft, [status(thm)], [c_59])).
% 3.22/1.61  tff(c_58, plain, (r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_8')) | k1_subset_1('#skF_7')='#skF_8'), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.22/1.61  tff(c_60, plain, (r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_8')) | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_58])).
% 3.22/1.61  tff(c_91, plain, (k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_78, c_60])).
% 3.22/1.61  tff(c_32, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.22/1.61  tff(c_93, plain, (![A_18]: (k5_xboole_0(A_18, '#skF_8')=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_91, c_32])).
% 3.22/1.61  tff(c_193, plain, (k4_xboole_0('#skF_8', '#skF_8')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_186, c_93])).
% 3.22/1.61  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.22/1.61  tff(c_214, plain, (![D_54]: (~r2_hidden(D_54, '#skF_8') | ~r2_hidden(D_54, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_193, c_10])).
% 3.22/1.61  tff(c_240, plain, (![B_59]: (~r2_hidden('#skF_1'('#skF_8', B_59), '#skF_8') | r1_tarski('#skF_8', B_59))), inference(resolution, [status(thm)], [c_6, c_214])).
% 3.22/1.61  tff(c_245, plain, (![B_2]: (r1_tarski('#skF_8', B_2))), inference(resolution, [status(thm)], [c_6, c_240])).
% 3.22/1.61  tff(c_249, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_245, c_78])).
% 3.22/1.61  tff(c_250, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_59])).
% 3.22/1.61  tff(c_251, plain, (r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_59])).
% 3.22/1.61  tff(c_26, plain, (![A_12]: (r2_hidden('#skF_4'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.22/1.61  tff(c_328, plain, (![C_78, B_79, A_80]: (r2_hidden(C_78, B_79) | ~r2_hidden(C_78, A_80) | ~r1_tarski(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.22/1.61  tff(c_557, plain, (![A_104, B_105]: (r2_hidden('#skF_4'(A_104), B_105) | ~r1_tarski(A_104, B_105) | k1_xboole_0=A_104)), inference(resolution, [status(thm)], [c_26, c_328])).
% 3.22/1.61  tff(c_50, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.22/1.61  tff(c_415, plain, (![A_87, B_88]: (k4_xboole_0(A_87, B_88)=k3_subset_1(A_87, B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.22/1.61  tff(c_419, plain, (k4_xboole_0('#skF_7', '#skF_8')=k3_subset_1('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_50, c_415])).
% 3.22/1.61  tff(c_464, plain, (![D_11]: (~r2_hidden(D_11, '#skF_8') | ~r2_hidden(D_11, k3_subset_1('#skF_7', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_419, c_10])).
% 3.22/1.61  tff(c_1544, plain, (![A_163]: (~r2_hidden('#skF_4'(A_163), '#skF_8') | ~r1_tarski(A_163, k3_subset_1('#skF_7', '#skF_8')) | k1_xboole_0=A_163)), inference(resolution, [status(thm)], [c_557, c_464])).
% 3.22/1.61  tff(c_1563, plain, (~r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_8')) | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_26, c_1544])).
% 3.22/1.61  tff(c_1573, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_251, c_1563])).
% 3.22/1.61  tff(c_1575, plain, $false, inference(negUnitSimplification, [status(thm)], [c_250, c_1573])).
% 3.22/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.61  
% 3.22/1.61  Inference rules
% 3.22/1.61  ----------------------
% 3.22/1.61  #Ref     : 0
% 3.22/1.61  #Sup     : 335
% 3.22/1.61  #Fact    : 0
% 3.22/1.61  #Define  : 0
% 3.22/1.61  #Split   : 9
% 3.22/1.61  #Chain   : 0
% 3.22/1.61  #Close   : 0
% 3.22/1.61  
% 3.22/1.61  Ordering : KBO
% 3.22/1.61  
% 3.22/1.61  Simplification rules
% 3.22/1.61  ----------------------
% 3.22/1.61  #Subsume      : 39
% 3.22/1.61  #Demod        : 87
% 3.22/1.61  #Tautology    : 134
% 3.22/1.61  #SimpNegUnit  : 24
% 3.22/1.61  #BackRed      : 15
% 3.22/1.61  
% 3.22/1.61  #Partial instantiations: 0
% 3.22/1.61  #Strategies tried      : 1
% 3.22/1.61  
% 3.22/1.61  Timing (in seconds)
% 3.22/1.61  ----------------------
% 3.22/1.61  Preprocessing        : 0.36
% 3.22/1.61  Parsing              : 0.17
% 3.22/1.61  CNF conversion       : 0.03
% 3.22/1.61  Main loop            : 0.47
% 3.22/1.61  Inferencing          : 0.17
% 3.22/1.61  Reduction            : 0.14
% 3.22/1.61  Demodulation         : 0.09
% 3.22/1.61  BG Simplification    : 0.03
% 3.22/1.61  Subsumption          : 0.10
% 3.22/1.61  Abstraction          : 0.03
% 3.22/1.61  MUC search           : 0.00
% 3.22/1.61  Cooper               : 0.00
% 3.22/1.61  Total                : 0.86
% 3.22/1.61  Index Insertion      : 0.00
% 3.22/1.61  Index Deletion       : 0.00
% 3.22/1.61  Index Matching       : 0.00
% 3.22/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
