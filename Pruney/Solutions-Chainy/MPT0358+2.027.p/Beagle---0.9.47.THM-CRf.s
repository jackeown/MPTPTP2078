%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:03 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   62 (  99 expanded)
%              Number of leaves         :   28 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :   71 ( 140 expanded)
%              Number of equality atoms :   26 (  62 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_61,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_53,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_45,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_55,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(c_36,plain,(
    ! [A_20] : k1_subset_1(A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_42,plain,
    ( k1_subset_1('#skF_4') != '#skF_5'
    | ~ r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_49,plain,
    ( k1_xboole_0 != '#skF_5'
    | ~ r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_42])).

tff(c_134,plain,(
    ~ r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_49])).

tff(c_48,plain,
    ( r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5'))
    | k1_subset_1('#skF_4') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_50,plain,
    ( r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5'))
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_48])).

tff(c_135,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_28,plain,(
    ! [A_15] : r1_tarski(k1_xboole_0,A_15) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_140,plain,(
    ! [A_15] : r1_tarski('#skF_5',A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_28])).

tff(c_181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_134])).

tff(c_182,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_182])).

tff(c_185,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_22,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_3'(A_9),A_9)
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_30,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_186,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_192,plain,(
    ! [A_36,B_37] :
      ( k2_xboole_0(A_36,B_37) = B_37
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_199,plain,(
    k2_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_5')) = k3_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_186,c_192])).

tff(c_32,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k2_xboole_0(A_17,B_18)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_348,plain,(
    ! [D_59,A_60,B_61] :
      ( r2_hidden(D_59,k4_xboole_0(A_60,B_61))
      | r2_hidden(D_59,B_61)
      | ~ r2_hidden(D_59,A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_567,plain,(
    ! [D_73,A_74,B_75] :
      ( r2_hidden(D_73,k1_xboole_0)
      | r2_hidden(D_73,k2_xboole_0(A_74,B_75))
      | ~ r2_hidden(D_73,A_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_348])).

tff(c_584,plain,(
    ! [D_76] :
      ( r2_hidden(D_76,k1_xboole_0)
      | r2_hidden(D_76,k3_subset_1('#skF_4','#skF_5'))
      | ~ r2_hidden(D_76,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_567])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_327,plain,(
    ! [A_56,B_57] :
      ( k4_xboole_0(A_56,B_57) = k3_subset_1(A_56,B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_331,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k3_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_327])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_338,plain,(
    ! [D_8] :
      ( ~ r2_hidden(D_8,'#skF_5')
      | ~ r2_hidden(D_8,k3_subset_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_6])).

tff(c_603,plain,(
    ! [D_77] :
      ( r2_hidden(D_77,k1_xboole_0)
      | ~ r2_hidden(D_77,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_584,c_338])).

tff(c_240,plain,(
    ! [D_41,B_42,A_43] :
      ( ~ r2_hidden(D_41,B_42)
      | ~ r2_hidden(D_41,k4_xboole_0(A_43,B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_257,plain,(
    ! [A_43,B_42] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_43,B_42)),B_42)
      | k4_xboole_0(A_43,B_42) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_240])).

tff(c_611,plain,(
    ! [A_43] :
      ( k4_xboole_0(A_43,k1_xboole_0) = k1_xboole_0
      | ~ r2_hidden('#skF_3'(k4_xboole_0(A_43,k1_xboole_0)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_603,c_257])).

tff(c_625,plain,(
    ! [A_78] :
      ( k1_xboole_0 = A_78
      | ~ r2_hidden('#skF_3'(A_78),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_611])).

tff(c_633,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_22,c_625])).

tff(c_638,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_185,c_185,c_633])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:19:23 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.36  
% 2.47/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.36  %$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.47/1.36  
% 2.47/1.36  %Foreground sorts:
% 2.47/1.36  
% 2.47/1.36  
% 2.47/1.36  %Background operators:
% 2.47/1.36  
% 2.47/1.36  
% 2.47/1.36  %Foreground operators:
% 2.47/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.47/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.47/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.47/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.36  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.47/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.47/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.47/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.47/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.47/1.36  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.47/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.36  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.47/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.47/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.47/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.47/1.36  
% 2.47/1.38  tff(f_61, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.47/1.38  tff(f_72, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 2.47/1.38  tff(f_53, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.47/1.38  tff(f_45, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.47/1.38  tff(f_55, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.47/1.38  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.47/1.38  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.47/1.38  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.47/1.38  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.47/1.38  tff(c_36, plain, (![A_20]: (k1_subset_1(A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.47/1.38  tff(c_42, plain, (k1_subset_1('#skF_4')!='#skF_5' | ~r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.47/1.38  tff(c_49, plain, (k1_xboole_0!='#skF_5' | ~r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_42])).
% 2.47/1.38  tff(c_134, plain, (~r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_49])).
% 2.47/1.38  tff(c_48, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5')) | k1_subset_1('#skF_4')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.47/1.38  tff(c_50, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5')) | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_48])).
% 2.47/1.38  tff(c_135, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_50])).
% 2.47/1.38  tff(c_28, plain, (![A_15]: (r1_tarski(k1_xboole_0, A_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.47/1.38  tff(c_140, plain, (![A_15]: (r1_tarski('#skF_5', A_15))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_28])).
% 2.47/1.38  tff(c_181, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_134])).
% 2.47/1.38  tff(c_182, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_50])).
% 2.47/1.38  tff(c_184, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134, c_182])).
% 2.47/1.38  tff(c_185, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_49])).
% 2.47/1.38  tff(c_22, plain, (![A_9]: (r2_hidden('#skF_3'(A_9), A_9) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.47/1.38  tff(c_30, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.47/1.38  tff(c_186, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_49])).
% 2.47/1.38  tff(c_192, plain, (![A_36, B_37]: (k2_xboole_0(A_36, B_37)=B_37 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.47/1.38  tff(c_199, plain, (k2_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_5'))=k3_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_186, c_192])).
% 2.47/1.38  tff(c_32, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k2_xboole_0(A_17, B_18))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.47/1.38  tff(c_348, plain, (![D_59, A_60, B_61]: (r2_hidden(D_59, k4_xboole_0(A_60, B_61)) | r2_hidden(D_59, B_61) | ~r2_hidden(D_59, A_60))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.47/1.38  tff(c_567, plain, (![D_73, A_74, B_75]: (r2_hidden(D_73, k1_xboole_0) | r2_hidden(D_73, k2_xboole_0(A_74, B_75)) | ~r2_hidden(D_73, A_74))), inference(superposition, [status(thm), theory('equality')], [c_32, c_348])).
% 2.47/1.38  tff(c_584, plain, (![D_76]: (r2_hidden(D_76, k1_xboole_0) | r2_hidden(D_76, k3_subset_1('#skF_4', '#skF_5')) | ~r2_hidden(D_76, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_199, c_567])).
% 2.47/1.38  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.47/1.38  tff(c_327, plain, (![A_56, B_57]: (k4_xboole_0(A_56, B_57)=k3_subset_1(A_56, B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.47/1.38  tff(c_331, plain, (k4_xboole_0('#skF_4', '#skF_5')=k3_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_327])).
% 2.47/1.38  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.47/1.38  tff(c_338, plain, (![D_8]: (~r2_hidden(D_8, '#skF_5') | ~r2_hidden(D_8, k3_subset_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_331, c_6])).
% 2.47/1.38  tff(c_603, plain, (![D_77]: (r2_hidden(D_77, k1_xboole_0) | ~r2_hidden(D_77, '#skF_5'))), inference(resolution, [status(thm)], [c_584, c_338])).
% 2.47/1.38  tff(c_240, plain, (![D_41, B_42, A_43]: (~r2_hidden(D_41, B_42) | ~r2_hidden(D_41, k4_xboole_0(A_43, B_42)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.47/1.38  tff(c_257, plain, (![A_43, B_42]: (~r2_hidden('#skF_3'(k4_xboole_0(A_43, B_42)), B_42) | k4_xboole_0(A_43, B_42)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_240])).
% 2.47/1.38  tff(c_611, plain, (![A_43]: (k4_xboole_0(A_43, k1_xboole_0)=k1_xboole_0 | ~r2_hidden('#skF_3'(k4_xboole_0(A_43, k1_xboole_0)), '#skF_5'))), inference(resolution, [status(thm)], [c_603, c_257])).
% 2.47/1.38  tff(c_625, plain, (![A_78]: (k1_xboole_0=A_78 | ~r2_hidden('#skF_3'(A_78), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_611])).
% 2.47/1.38  tff(c_633, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_22, c_625])).
% 2.47/1.38  tff(c_638, plain, $false, inference(negUnitSimplification, [status(thm)], [c_185, c_185, c_633])).
% 2.47/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.38  
% 2.47/1.38  Inference rules
% 2.47/1.38  ----------------------
% 2.47/1.38  #Ref     : 0
% 2.47/1.38  #Sup     : 131
% 2.47/1.38  #Fact    : 0
% 2.47/1.38  #Define  : 0
% 2.47/1.38  #Split   : 4
% 2.47/1.38  #Chain   : 0
% 2.47/1.38  #Close   : 0
% 2.47/1.38  
% 2.47/1.38  Ordering : KBO
% 2.47/1.38  
% 2.47/1.38  Simplification rules
% 2.47/1.38  ----------------------
% 2.47/1.38  #Subsume      : 17
% 2.47/1.38  #Demod        : 47
% 2.47/1.38  #Tautology    : 82
% 2.47/1.38  #SimpNegUnit  : 8
% 2.47/1.38  #BackRed      : 13
% 2.47/1.38  
% 2.47/1.38  #Partial instantiations: 0
% 2.47/1.38  #Strategies tried      : 1
% 2.47/1.38  
% 2.47/1.38  Timing (in seconds)
% 2.47/1.38  ----------------------
% 2.47/1.38  Preprocessing        : 0.32
% 2.47/1.38  Parsing              : 0.16
% 2.47/1.38  CNF conversion       : 0.02
% 2.47/1.38  Main loop            : 0.29
% 2.47/1.38  Inferencing          : 0.10
% 2.47/1.38  Reduction            : 0.09
% 2.47/1.38  Demodulation         : 0.07
% 2.47/1.38  BG Simplification    : 0.02
% 2.47/1.38  Subsumption          : 0.06
% 2.47/1.38  Abstraction          : 0.02
% 2.47/1.38  MUC search           : 0.00
% 2.47/1.38  Cooper               : 0.00
% 2.47/1.38  Total                : 0.64
% 2.47/1.38  Index Insertion      : 0.00
% 2.47/1.38  Index Deletion       : 0.00
% 2.47/1.38  Index Matching       : 0.00
% 2.47/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
