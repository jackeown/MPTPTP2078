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
% DateTime   : Thu Dec  3 09:56:00 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   62 (  90 expanded)
%              Number of leaves         :   29 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 ( 122 expanded)
%              Number of equality atoms :   28 (  54 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_90,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_64,plain,(
    ! [A_31] : k1_subset_1(A_31) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_72,plain,
    ( k1_subset_1('#skF_6') != '#skF_7'
    | ~ r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_80,plain,
    ( k1_xboole_0 != '#skF_7'
    | ~ r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_72])).

tff(c_135,plain,(
    ~ r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_394,plain,(
    ! [A_86,B_87] :
      ( r2_hidden('#skF_1'(A_86,B_87),A_86)
      | r1_tarski(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_32,plain,(
    ! [B_15] : r1_tarski(B_15,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_78,plain,
    ( r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7'))
    | k1_subset_1('#skF_6') = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_79,plain,
    ( r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7'))
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_78])).

tff(c_136,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_36,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = k1_xboole_0
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_164,plain,(
    ! [A_50,B_51] :
      ( k4_xboole_0(A_50,B_51) = '#skF_7'
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_36])).

tff(c_168,plain,(
    ! [B_15] : k4_xboole_0(B_15,B_15) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_32,c_164])).

tff(c_297,plain,(
    ! [D_70,B_71,A_72] :
      ( ~ r2_hidden(D_70,B_71)
      | ~ r2_hidden(D_70,k4_xboole_0(A_72,B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_307,plain,(
    ! [D_70,B_15] :
      ( ~ r2_hidden(D_70,B_15)
      | ~ r2_hidden(D_70,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_297])).

tff(c_508,plain,(
    ! [A_99,B_100] :
      ( ~ r2_hidden('#skF_1'(A_99,B_100),'#skF_7')
      | r1_tarski(A_99,B_100) ) ),
    inference(resolution,[status(thm)],[c_394,c_307])).

tff(c_516,plain,(
    ! [B_4] : r1_tarski('#skF_7',B_4) ),
    inference(resolution,[status(thm)],[c_8,c_508])).

tff(c_521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_516,c_135])).

tff(c_522,plain,(
    r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_524,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_522])).

tff(c_525,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_526,plain,(
    r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_541,plain,(
    ! [A_107,B_108] :
      ( k4_xboole_0(A_107,B_108) = k1_xboole_0
      | ~ r1_tarski(A_107,B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_552,plain,(
    k4_xboole_0('#skF_7',k3_subset_1('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_526,c_541])).

tff(c_70,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1091,plain,(
    ! [A_159,B_160] :
      ( k4_xboole_0(A_159,B_160) = k3_subset_1(A_159,B_160)
      | ~ m1_subset_1(B_160,k1_zfmisc_1(A_159)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1104,plain,(
    k4_xboole_0('#skF_6','#skF_7') = k3_subset_1('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_1091])).

tff(c_34,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | k4_xboole_0(A_16,B_17) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_535,plain,(
    ! [A_105,B_106] :
      ( k1_xboole_0 = A_105
      | ~ r1_tarski(A_105,k4_xboole_0(B_106,A_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_540,plain,(
    ! [A_16,B_106] :
      ( k1_xboole_0 = A_16
      | k4_xboole_0(A_16,k4_xboole_0(B_106,A_16)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_535])).

tff(c_1165,plain,
    ( k1_xboole_0 = '#skF_7'
    | k4_xboole_0('#skF_7',k3_subset_1('#skF_6','#skF_7')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1104,c_540])).

tff(c_1179,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_1165])).

tff(c_1181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_525,c_1179])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:09:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.50  
% 3.13/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.51  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 3.13/1.51  
% 3.13/1.51  %Foreground sorts:
% 3.13/1.51  
% 3.13/1.51  
% 3.13/1.51  %Background operators:
% 3.13/1.51  
% 3.13/1.51  
% 3.13/1.51  %Foreground operators:
% 3.13/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.13/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.13/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.13/1.51  tff('#skF_7', type, '#skF_7': $i).
% 3.13/1.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.13/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.13/1.51  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.13/1.51  tff('#skF_6', type, '#skF_6': $i).
% 3.13/1.51  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.13/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.13/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.51  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.13/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.51  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.13/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.13/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.13/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.13/1.51  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.13/1.51  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.13/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.13/1.51  
% 3.13/1.52  tff(f_86, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 3.13/1.52  tff(f_100, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 3.13/1.52  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.13/1.52  tff(f_50, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.13/1.52  tff(f_54, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.13/1.52  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.13/1.52  tff(f_90, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.13/1.52  tff(f_64, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 3.13/1.52  tff(c_64, plain, (![A_31]: (k1_subset_1(A_31)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.13/1.52  tff(c_72, plain, (k1_subset_1('#skF_6')!='#skF_7' | ~r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.13/1.52  tff(c_80, plain, (k1_xboole_0!='#skF_7' | ~r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_72])).
% 3.13/1.52  tff(c_135, plain, (~r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_80])).
% 3.13/1.52  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.13/1.52  tff(c_394, plain, (![A_86, B_87]: (r2_hidden('#skF_1'(A_86, B_87), A_86) | r1_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.13/1.52  tff(c_32, plain, (![B_15]: (r1_tarski(B_15, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.13/1.52  tff(c_78, plain, (r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7')) | k1_subset_1('#skF_6')='#skF_7'), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.13/1.52  tff(c_79, plain, (r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7')) | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_78])).
% 3.13/1.52  tff(c_136, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_79])).
% 3.13/1.52  tff(c_36, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=k1_xboole_0 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.13/1.52  tff(c_164, plain, (![A_50, B_51]: (k4_xboole_0(A_50, B_51)='#skF_7' | ~r1_tarski(A_50, B_51))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_36])).
% 3.13/1.52  tff(c_168, plain, (![B_15]: (k4_xboole_0(B_15, B_15)='#skF_7')), inference(resolution, [status(thm)], [c_32, c_164])).
% 3.13/1.52  tff(c_297, plain, (![D_70, B_71, A_72]: (~r2_hidden(D_70, B_71) | ~r2_hidden(D_70, k4_xboole_0(A_72, B_71)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.13/1.52  tff(c_307, plain, (![D_70, B_15]: (~r2_hidden(D_70, B_15) | ~r2_hidden(D_70, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_168, c_297])).
% 3.13/1.52  tff(c_508, plain, (![A_99, B_100]: (~r2_hidden('#skF_1'(A_99, B_100), '#skF_7') | r1_tarski(A_99, B_100))), inference(resolution, [status(thm)], [c_394, c_307])).
% 3.13/1.52  tff(c_516, plain, (![B_4]: (r1_tarski('#skF_7', B_4))), inference(resolution, [status(thm)], [c_8, c_508])).
% 3.13/1.52  tff(c_521, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_516, c_135])).
% 3.13/1.52  tff(c_522, plain, (r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_79])).
% 3.13/1.52  tff(c_524, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135, c_522])).
% 3.13/1.52  tff(c_525, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_80])).
% 3.13/1.52  tff(c_526, plain, (r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_80])).
% 3.13/1.52  tff(c_541, plain, (![A_107, B_108]: (k4_xboole_0(A_107, B_108)=k1_xboole_0 | ~r1_tarski(A_107, B_108))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.13/1.52  tff(c_552, plain, (k4_xboole_0('#skF_7', k3_subset_1('#skF_6', '#skF_7'))=k1_xboole_0), inference(resolution, [status(thm)], [c_526, c_541])).
% 3.13/1.52  tff(c_70, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.13/1.52  tff(c_1091, plain, (![A_159, B_160]: (k4_xboole_0(A_159, B_160)=k3_subset_1(A_159, B_160) | ~m1_subset_1(B_160, k1_zfmisc_1(A_159)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.13/1.52  tff(c_1104, plain, (k4_xboole_0('#skF_6', '#skF_7')=k3_subset_1('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_70, c_1091])).
% 3.13/1.52  tff(c_34, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | k4_xboole_0(A_16, B_17)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.13/1.52  tff(c_535, plain, (![A_105, B_106]: (k1_xboole_0=A_105 | ~r1_tarski(A_105, k4_xboole_0(B_106, A_105)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.13/1.52  tff(c_540, plain, (![A_16, B_106]: (k1_xboole_0=A_16 | k4_xboole_0(A_16, k4_xboole_0(B_106, A_16))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_535])).
% 3.13/1.52  tff(c_1165, plain, (k1_xboole_0='#skF_7' | k4_xboole_0('#skF_7', k3_subset_1('#skF_6', '#skF_7'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1104, c_540])).
% 3.13/1.52  tff(c_1179, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_552, c_1165])).
% 3.13/1.52  tff(c_1181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_525, c_1179])).
% 3.13/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.52  
% 3.13/1.52  Inference rules
% 3.13/1.52  ----------------------
% 3.13/1.52  #Ref     : 0
% 3.13/1.52  #Sup     : 264
% 3.13/1.52  #Fact    : 0
% 3.13/1.52  #Define  : 0
% 3.13/1.52  #Split   : 5
% 3.13/1.52  #Chain   : 0
% 3.13/1.52  #Close   : 0
% 3.13/1.52  
% 3.13/1.52  Ordering : KBO
% 3.13/1.52  
% 3.13/1.52  Simplification rules
% 3.13/1.52  ----------------------
% 3.13/1.52  #Subsume      : 29
% 3.13/1.52  #Demod        : 72
% 3.13/1.52  #Tautology    : 138
% 3.13/1.52  #SimpNegUnit  : 7
% 3.13/1.52  #BackRed      : 4
% 3.13/1.52  
% 3.13/1.52  #Partial instantiations: 0
% 3.13/1.52  #Strategies tried      : 1
% 3.13/1.52  
% 3.13/1.52  Timing (in seconds)
% 3.13/1.52  ----------------------
% 3.13/1.52  Preprocessing        : 0.34
% 3.13/1.52  Parsing              : 0.18
% 3.13/1.52  CNF conversion       : 0.02
% 3.13/1.52  Main loop            : 0.39
% 3.13/1.52  Inferencing          : 0.14
% 3.13/1.52  Reduction            : 0.12
% 3.13/1.52  Demodulation         : 0.09
% 3.13/1.52  BG Simplification    : 0.02
% 3.13/1.52  Subsumption          : 0.07
% 3.13/1.52  Abstraction          : 0.02
% 3.13/1.52  MUC search           : 0.00
% 3.13/1.52  Cooper               : 0.00
% 3.13/1.52  Total                : 0.76
% 3.13/1.52  Index Insertion      : 0.00
% 3.13/1.52  Index Deletion       : 0.00
% 3.13/1.52  Index Matching       : 0.00
% 3.13/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
