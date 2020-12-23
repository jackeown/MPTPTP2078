%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:28 EST 2020

% Result     : Theorem 3.80s
% Output     : CNFRefutation 4.00s
% Verified   : 
% Statistics : Number of formulae       :   51 (  73 expanded)
%              Number of leaves         :   28 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :   60 ( 139 expanded)
%              Number of equality atoms :   18 (  38 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_32,plain,(
    k1_funct_1('#skF_7','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_38,plain,(
    v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_36,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_tarski('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_34,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2553,plain,(
    ! [D_4318,C_4319,B_4320,A_4321] :
      ( r2_hidden(k1_funct_1(D_4318,C_4319),B_4320)
      | k1_xboole_0 = B_4320
      | ~ r2_hidden(C_4319,A_4321)
      | ~ m1_subset_1(D_4318,k1_zfmisc_1(k2_zfmisc_1(A_4321,B_4320)))
      | ~ v1_funct_2(D_4318,A_4321,B_4320)
      | ~ v1_funct_1(D_4318) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3377,plain,(
    ! [D_6807,B_6808] :
      ( r2_hidden(k1_funct_1(D_6807,'#skF_6'),B_6808)
      | k1_xboole_0 = B_6808
      | ~ m1_subset_1(D_6807,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_6808)))
      | ~ v1_funct_2(D_6807,'#skF_4',B_6808)
      | ~ v1_funct_1(D_6807) ) ),
    inference(resolution,[status(thm)],[c_34,c_2553])).

tff(c_3394,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_6'),k1_tarski('#skF_5'))
    | k1_tarski('#skF_5') = k1_xboole_0
    | ~ v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5'))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_3377])).

tff(c_3397,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_6'),k1_tarski('#skF_5'))
    | k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_3394])).

tff(c_3398,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3397])).

tff(c_26,plain,(
    ! [A_11] : k2_tarski(A_11,A_11) = k1_tarski(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_50,plain,(
    ! [D_19,A_20] : r2_hidden(D_19,k2_tarski(A_20,D_19)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_53,plain,(
    ! [A_11] : r2_hidden(A_11,k1_tarski(A_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_50])).

tff(c_60,plain,(
    ! [B_24,A_25] :
      ( ~ r2_hidden(B_24,A_25)
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ! [A_11] : ~ v1_xboole_0(k1_tarski(A_11)) ),
    inference(resolution,[status(thm)],[c_53,c_60])).

tff(c_3412,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3398,c_74])).

tff(c_3463,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3412])).

tff(c_3464,plain,(
    r2_hidden(k1_funct_1('#skF_7','#skF_6'),k1_tarski('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_3397])).

tff(c_95,plain,(
    ! [D_32,B_33,A_34] :
      ( D_32 = B_33
      | D_32 = A_34
      | ~ r2_hidden(D_32,k2_tarski(A_34,B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_108,plain,(
    ! [D_32,A_11] :
      ( D_32 = A_11
      | D_32 = A_11
      | ~ r2_hidden(D_32,k1_tarski(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_95])).

tff(c_3480,plain,(
    k1_funct_1('#skF_7','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3464,c_108])).

tff(c_3537,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_32,c_3480])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:01:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.80/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.68  
% 3.80/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.69  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 3.80/1.69  
% 3.80/1.69  %Foreground sorts:
% 3.80/1.69  
% 3.80/1.69  
% 3.80/1.69  %Background operators:
% 3.80/1.69  
% 3.80/1.69  
% 3.80/1.69  %Foreground operators:
% 3.80/1.69  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.80/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.80/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.80/1.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.80/1.69  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.80/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.80/1.69  tff('#skF_7', type, '#skF_7': $i).
% 3.80/1.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.80/1.69  tff('#skF_5', type, '#skF_5': $i).
% 3.80/1.69  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.80/1.69  tff('#skF_6', type, '#skF_6': $i).
% 3.80/1.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.80/1.69  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.80/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.80/1.69  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.80/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.80/1.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.80/1.69  tff('#skF_4', type, '#skF_4': $i).
% 3.80/1.69  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.80/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.80/1.69  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.80/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.80/1.69  
% 4.00/1.70  tff(f_68, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 4.00/1.70  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.00/1.70  tff(f_57, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 4.00/1.70  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.00/1.70  tff(f_41, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 4.00/1.70  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.00/1.70  tff(c_32, plain, (k1_funct_1('#skF_7', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.00/1.70  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.00/1.70  tff(c_40, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.00/1.70  tff(c_38, plain, (v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.00/1.70  tff(c_36, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_tarski('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.00/1.70  tff(c_34, plain, (r2_hidden('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.00/1.70  tff(c_2553, plain, (![D_4318, C_4319, B_4320, A_4321]: (r2_hidden(k1_funct_1(D_4318, C_4319), B_4320) | k1_xboole_0=B_4320 | ~r2_hidden(C_4319, A_4321) | ~m1_subset_1(D_4318, k1_zfmisc_1(k2_zfmisc_1(A_4321, B_4320))) | ~v1_funct_2(D_4318, A_4321, B_4320) | ~v1_funct_1(D_4318))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.00/1.70  tff(c_3377, plain, (![D_6807, B_6808]: (r2_hidden(k1_funct_1(D_6807, '#skF_6'), B_6808) | k1_xboole_0=B_6808 | ~m1_subset_1(D_6807, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_6808))) | ~v1_funct_2(D_6807, '#skF_4', B_6808) | ~v1_funct_1(D_6807))), inference(resolution, [status(thm)], [c_34, c_2553])).
% 4.00/1.70  tff(c_3394, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_6'), k1_tarski('#skF_5')) | k1_tarski('#skF_5')=k1_xboole_0 | ~v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5')) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_36, c_3377])).
% 4.00/1.70  tff(c_3397, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_6'), k1_tarski('#skF_5')) | k1_tarski('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_3394])).
% 4.00/1.70  tff(c_3398, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3397])).
% 4.00/1.70  tff(c_26, plain, (![A_11]: (k2_tarski(A_11, A_11)=k1_tarski(A_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.00/1.70  tff(c_50, plain, (![D_19, A_20]: (r2_hidden(D_19, k2_tarski(A_20, D_19)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.00/1.70  tff(c_53, plain, (![A_11]: (r2_hidden(A_11, k1_tarski(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_50])).
% 4.00/1.70  tff(c_60, plain, (![B_24, A_25]: (~r2_hidden(B_24, A_25) | ~v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.00/1.70  tff(c_74, plain, (![A_11]: (~v1_xboole_0(k1_tarski(A_11)))), inference(resolution, [status(thm)], [c_53, c_60])).
% 4.00/1.70  tff(c_3412, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3398, c_74])).
% 4.00/1.70  tff(c_3463, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3412])).
% 4.00/1.70  tff(c_3464, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_6'), k1_tarski('#skF_5'))), inference(splitRight, [status(thm)], [c_3397])).
% 4.00/1.70  tff(c_95, plain, (![D_32, B_33, A_34]: (D_32=B_33 | D_32=A_34 | ~r2_hidden(D_32, k2_tarski(A_34, B_33)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.00/1.70  tff(c_108, plain, (![D_32, A_11]: (D_32=A_11 | D_32=A_11 | ~r2_hidden(D_32, k1_tarski(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_95])).
% 4.00/1.70  tff(c_3480, plain, (k1_funct_1('#skF_7', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_3464, c_108])).
% 4.00/1.70  tff(c_3537, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_32, c_3480])).
% 4.00/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.00/1.70  
% 4.00/1.70  Inference rules
% 4.00/1.70  ----------------------
% 4.00/1.70  #Ref     : 0
% 4.00/1.70  #Sup     : 447
% 4.00/1.70  #Fact    : 8
% 4.00/1.70  #Define  : 0
% 4.00/1.70  #Split   : 5
% 4.00/1.70  #Chain   : 0
% 4.00/1.70  #Close   : 0
% 4.00/1.70  
% 4.00/1.70  Ordering : KBO
% 4.00/1.70  
% 4.00/1.70  Simplification rules
% 4.00/1.70  ----------------------
% 4.00/1.70  #Subsume      : 81
% 4.00/1.70  #Demod        : 77
% 4.00/1.70  #Tautology    : 123
% 4.00/1.70  #SimpNegUnit  : 11
% 4.00/1.70  #BackRed      : 2
% 4.00/1.70  
% 4.00/1.70  #Partial instantiations: 4218
% 4.00/1.70  #Strategies tried      : 1
% 4.00/1.70  
% 4.00/1.70  Timing (in seconds)
% 4.00/1.70  ----------------------
% 4.00/1.70  Preprocessing        : 0.29
% 4.00/1.70  Parsing              : 0.14
% 4.00/1.70  CNF conversion       : 0.02
% 4.00/1.70  Main loop            : 0.64
% 4.00/1.70  Inferencing          : 0.36
% 4.00/1.70  Reduction            : 0.14
% 4.00/1.70  Demodulation         : 0.09
% 4.00/1.70  BG Simplification    : 0.03
% 4.00/1.70  Subsumption          : 0.08
% 4.00/1.70  Abstraction          : 0.04
% 4.00/1.70  MUC search           : 0.00
% 4.00/1.70  Cooper               : 0.00
% 4.00/1.70  Total                : 0.95
% 4.00/1.70  Index Insertion      : 0.00
% 4.00/1.70  Index Deletion       : 0.00
% 4.00/1.70  Index Matching       : 0.00
% 4.00/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
