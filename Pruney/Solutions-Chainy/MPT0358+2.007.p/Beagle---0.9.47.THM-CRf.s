%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:01 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :   64 (  84 expanded)
%              Number of leaves         :   35 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :   66 ( 102 expanded)
%              Number of equality atoms :   24 (  44 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_4 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_112,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_74,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_54,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_72,axiom,(
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

tff(f_102,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_80,plain,(
    ! [A_37] : k1_subset_1(A_37) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_94,plain,
    ( r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9'))
    | k1_subset_1('#skF_8') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_95,plain,
    ( r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9'))
    | k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_94])).

tff(c_154,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_56,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k2_xboole_0(A_26,B_27)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_156,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k2_xboole_0(A_26,B_27)) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_56])).

tff(c_46,plain,(
    ! [B_18] : r1_tarski(B_18,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_223,plain,(
    ! [A_67,B_68,C_69] :
      ( r1_tarski(A_67,B_68)
      | ~ r1_tarski(A_67,k4_xboole_0(B_68,C_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_232,plain,(
    ! [B_70,C_71] : r1_tarski(k4_xboole_0(B_70,C_71),B_70) ),
    inference(resolution,[status(thm)],[c_46,c_223])).

tff(c_242,plain,(
    ! [A_26] : r1_tarski('#skF_9',A_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_232])).

tff(c_88,plain,
    ( k1_subset_1('#skF_8') != '#skF_9'
    | ~ r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_96,plain,
    ( k1_xboole_0 != '#skF_9'
    | ~ r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_88])).

tff(c_178,plain,(
    ~ r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_96])).

tff(c_247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_178])).

tff(c_249,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_40,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_5'(A_15),A_15)
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_248,plain,(
    r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_265,plain,(
    ! [A_76,B_77] :
      ( k3_xboole_0(A_76,B_77) = A_76
      | ~ r1_tarski(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_272,plain,(
    k3_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9')) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_248,c_265])).

tff(c_700,plain,(
    ! [D_112,B_113,A_114] :
      ( r2_hidden(D_112,B_113)
      | ~ r2_hidden(D_112,k3_xboole_0(A_114,B_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_709,plain,(
    ! [D_112] :
      ( r2_hidden(D_112,k3_subset_1('#skF_8','#skF_9'))
      | ~ r2_hidden(D_112,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_700])).

tff(c_86,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1253,plain,(
    ! [A_156,B_157] :
      ( k4_xboole_0(A_156,B_157) = k3_subset_1(A_156,B_157)
      | ~ m1_subset_1(B_157,k1_zfmisc_1(A_156)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1266,plain,(
    k4_xboole_0('#skF_8','#skF_9') = k3_subset_1('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_86,c_1253])).

tff(c_24,plain,(
    ! [D_14,B_10,A_9] :
      ( ~ r2_hidden(D_14,B_10)
      | ~ r2_hidden(D_14,k4_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1654,plain,(
    ! [D_174] :
      ( ~ r2_hidden(D_174,'#skF_9')
      | ~ r2_hidden(D_174,k3_subset_1('#skF_8','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1266,c_24])).

tff(c_1675,plain,(
    ! [D_175] : ~ r2_hidden(D_175,'#skF_9') ),
    inference(resolution,[status(thm)],[c_709,c_1654])).

tff(c_1687,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_40,c_1675])).

tff(c_1693,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_1687])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:25:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.18/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.63  
% 3.18/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.64  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_4 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7
% 3.18/1.64  
% 3.18/1.64  %Foreground sorts:
% 3.18/1.64  
% 3.18/1.64  
% 3.18/1.64  %Background operators:
% 3.18/1.64  
% 3.18/1.64  
% 3.18/1.64  %Foreground operators:
% 3.18/1.64  tff('#skF_5', type, '#skF_5': $i > $i).
% 3.18/1.64  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.18/1.64  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.18/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.18/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.18/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.18/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.18/1.64  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.18/1.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.18/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.18/1.64  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.18/1.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.18/1.64  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.18/1.64  tff('#skF_9', type, '#skF_9': $i).
% 3.18/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.56/1.64  tff('#skF_8', type, '#skF_8': $i).
% 3.56/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.56/1.64  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.56/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.56/1.64  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.56/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.56/1.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.56/1.64  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.56/1.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.56/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.56/1.64  
% 3.56/1.65  tff(f_98, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 3.56/1.65  tff(f_112, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 3.56/1.65  tff(f_74, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.56/1.65  tff(f_60, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.56/1.65  tff(f_68, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.56/1.65  tff(f_54, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.56/1.65  tff(f_72, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.56/1.65  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.56/1.65  tff(f_102, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.56/1.65  tff(f_46, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.56/1.65  tff(c_80, plain, (![A_37]: (k1_subset_1(A_37)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.56/1.65  tff(c_94, plain, (r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9')) | k1_subset_1('#skF_8')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.56/1.65  tff(c_95, plain, (r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9')) | k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_94])).
% 3.56/1.65  tff(c_154, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_95])).
% 3.56/1.65  tff(c_56, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k2_xboole_0(A_26, B_27))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.56/1.65  tff(c_156, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k2_xboole_0(A_26, B_27))='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_56])).
% 3.56/1.65  tff(c_46, plain, (![B_18]: (r1_tarski(B_18, B_18))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.56/1.65  tff(c_223, plain, (![A_67, B_68, C_69]: (r1_tarski(A_67, B_68) | ~r1_tarski(A_67, k4_xboole_0(B_68, C_69)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.56/1.65  tff(c_232, plain, (![B_70, C_71]: (r1_tarski(k4_xboole_0(B_70, C_71), B_70))), inference(resolution, [status(thm)], [c_46, c_223])).
% 3.56/1.65  tff(c_242, plain, (![A_26]: (r1_tarski('#skF_9', A_26))), inference(superposition, [status(thm), theory('equality')], [c_156, c_232])).
% 3.56/1.65  tff(c_88, plain, (k1_subset_1('#skF_8')!='#skF_9' | ~r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.56/1.65  tff(c_96, plain, (k1_xboole_0!='#skF_9' | ~r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_88])).
% 3.56/1.65  tff(c_178, plain, (~r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_96])).
% 3.56/1.65  tff(c_247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_242, c_178])).
% 3.56/1.65  tff(c_249, plain, (k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_95])).
% 3.56/1.65  tff(c_40, plain, (![A_15]: (r2_hidden('#skF_5'(A_15), A_15) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.56/1.65  tff(c_248, plain, (r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(splitRight, [status(thm)], [c_95])).
% 3.56/1.65  tff(c_265, plain, (![A_76, B_77]: (k3_xboole_0(A_76, B_77)=A_76 | ~r1_tarski(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.56/1.65  tff(c_272, plain, (k3_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9'))='#skF_9'), inference(resolution, [status(thm)], [c_248, c_265])).
% 3.56/1.65  tff(c_700, plain, (![D_112, B_113, A_114]: (r2_hidden(D_112, B_113) | ~r2_hidden(D_112, k3_xboole_0(A_114, B_113)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.56/1.65  tff(c_709, plain, (![D_112]: (r2_hidden(D_112, k3_subset_1('#skF_8', '#skF_9')) | ~r2_hidden(D_112, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_272, c_700])).
% 3.56/1.65  tff(c_86, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.56/1.65  tff(c_1253, plain, (![A_156, B_157]: (k4_xboole_0(A_156, B_157)=k3_subset_1(A_156, B_157) | ~m1_subset_1(B_157, k1_zfmisc_1(A_156)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.56/1.65  tff(c_1266, plain, (k4_xboole_0('#skF_8', '#skF_9')=k3_subset_1('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_86, c_1253])).
% 3.56/1.65  tff(c_24, plain, (![D_14, B_10, A_9]: (~r2_hidden(D_14, B_10) | ~r2_hidden(D_14, k4_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.56/1.65  tff(c_1654, plain, (![D_174]: (~r2_hidden(D_174, '#skF_9') | ~r2_hidden(D_174, k3_subset_1('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_1266, c_24])).
% 3.56/1.65  tff(c_1675, plain, (![D_175]: (~r2_hidden(D_175, '#skF_9'))), inference(resolution, [status(thm)], [c_709, c_1654])).
% 3.56/1.65  tff(c_1687, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_40, c_1675])).
% 3.56/1.65  tff(c_1693, plain, $false, inference(negUnitSimplification, [status(thm)], [c_249, c_1687])).
% 3.56/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.65  
% 3.56/1.65  Inference rules
% 3.56/1.65  ----------------------
% 3.56/1.65  #Ref     : 0
% 3.56/1.65  #Sup     : 388
% 3.56/1.65  #Fact    : 0
% 3.56/1.65  #Define  : 0
% 3.56/1.65  #Split   : 7
% 3.56/1.65  #Chain   : 0
% 3.56/1.65  #Close   : 0
% 3.56/1.65  
% 3.56/1.65  Ordering : KBO
% 3.56/1.65  
% 3.56/1.65  Simplification rules
% 3.56/1.65  ----------------------
% 3.56/1.65  #Subsume      : 31
% 3.56/1.65  #Demod        : 152
% 3.56/1.65  #Tautology    : 198
% 3.56/1.65  #SimpNegUnit  : 4
% 3.56/1.65  #BackRed      : 9
% 3.56/1.65  
% 3.56/1.65  #Partial instantiations: 0
% 3.56/1.65  #Strategies tried      : 1
% 3.56/1.65  
% 3.56/1.65  Timing (in seconds)
% 3.56/1.65  ----------------------
% 3.56/1.65  Preprocessing        : 0.35
% 3.56/1.65  Parsing              : 0.18
% 3.56/1.65  CNF conversion       : 0.03
% 3.56/1.65  Main loop            : 0.48
% 3.56/1.65  Inferencing          : 0.16
% 3.56/1.65  Reduction            : 0.16
% 3.56/1.65  Demodulation         : 0.12
% 3.56/1.65  BG Simplification    : 0.03
% 3.56/1.65  Subsumption          : 0.09
% 3.56/1.65  Abstraction          : 0.02
% 3.56/1.65  MUC search           : 0.00
% 3.56/1.65  Cooper               : 0.00
% 3.56/1.65  Total                : 0.86
% 3.56/1.65  Index Insertion      : 0.00
% 3.56/1.65  Index Deletion       : 0.00
% 3.56/1.65  Index Matching       : 0.00
% 3.56/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
