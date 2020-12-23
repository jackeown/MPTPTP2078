%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:31 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :   51 (  72 expanded)
%              Number of leaves         :   27 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :   61 ( 139 expanded)
%              Number of equality atoms :   19 (  38 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_38,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_30,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_38,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_36,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_34,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_32,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1639,plain,(
    ! [D_2094,C_2095,B_2096,A_2097] :
      ( r2_hidden(k1_funct_1(D_2094,C_2095),B_2096)
      | k1_xboole_0 = B_2096
      | ~ r2_hidden(C_2095,A_2097)
      | ~ m1_subset_1(D_2094,k1_zfmisc_1(k2_zfmisc_1(A_2097,B_2096)))
      | ~ v1_funct_2(D_2094,A_2097,B_2096)
      | ~ v1_funct_1(D_2094) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1903,plain,(
    ! [D_2411,B_2412] :
      ( r2_hidden(k1_funct_1(D_2411,'#skF_5'),B_2412)
      | k1_xboole_0 = B_2412
      | ~ m1_subset_1(D_2411,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_2412)))
      | ~ v1_funct_2(D_2411,'#skF_3',B_2412)
      | ~ v1_funct_1(D_2411) ) ),
    inference(resolution,[status(thm)],[c_32,c_1639])).

tff(c_1912,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_1903])).

tff(c_1915,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1912])).

tff(c_1916,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1915])).

tff(c_41,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [D_7,A_2] : r2_hidden(D_7,k2_tarski(A_2,D_7)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_47,plain,(
    ! [A_20] : r2_hidden(A_20,k1_tarski(A_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_6])).

tff(c_59,plain,(
    ! [B_24,A_25] :
      ( ~ r1_tarski(B_24,A_25)
      | ~ r2_hidden(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_73,plain,(
    ! [A_20] : ~ r1_tarski(k1_tarski(A_20),A_20) ),
    inference(resolution,[status(thm)],[c_47,c_59])).

tff(c_1928,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1916,c_73])).

tff(c_1973,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1928])).

tff(c_1974,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1915])).

tff(c_22,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_94,plain,(
    ! [D_33,B_34,A_35] :
      ( D_33 = B_34
      | D_33 = A_35
      | ~ r2_hidden(D_33,k2_tarski(A_35,B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_100,plain,(
    ! [D_33,A_8] :
      ( D_33 = A_8
      | D_33 = A_8
      | ~ r2_hidden(D_33,k1_tarski(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_94])).

tff(c_1986,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1974,c_100])).

tff(c_2033,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_30,c_1986])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:09:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.65  
% 3.49/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.65  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.49/1.65  
% 3.49/1.65  %Foreground sorts:
% 3.49/1.65  
% 3.49/1.65  
% 3.49/1.65  %Background operators:
% 3.49/1.65  
% 3.49/1.65  
% 3.49/1.65  %Foreground operators:
% 3.49/1.65  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.49/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.49/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.49/1.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.49/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.49/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.49/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.49/1.65  tff('#skF_5', type, '#skF_5': $i).
% 3.49/1.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.49/1.65  tff('#skF_6', type, '#skF_6': $i).
% 3.49/1.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.49/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.49/1.65  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.49/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.49/1.65  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.49/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.49/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.49/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.49/1.65  
% 3.49/1.66  tff(f_68, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 3.49/1.66  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.49/1.66  tff(f_57, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 3.49/1.66  tff(f_38, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.49/1.66  tff(f_36, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.49/1.66  tff(f_45, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.49/1.66  tff(c_30, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.49/1.66  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.49/1.66  tff(c_38, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.49/1.66  tff(c_36, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.49/1.66  tff(c_34, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.49/1.66  tff(c_32, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.49/1.66  tff(c_1639, plain, (![D_2094, C_2095, B_2096, A_2097]: (r2_hidden(k1_funct_1(D_2094, C_2095), B_2096) | k1_xboole_0=B_2096 | ~r2_hidden(C_2095, A_2097) | ~m1_subset_1(D_2094, k1_zfmisc_1(k2_zfmisc_1(A_2097, B_2096))) | ~v1_funct_2(D_2094, A_2097, B_2096) | ~v1_funct_1(D_2094))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.49/1.66  tff(c_1903, plain, (![D_2411, B_2412]: (r2_hidden(k1_funct_1(D_2411, '#skF_5'), B_2412) | k1_xboole_0=B_2412 | ~m1_subset_1(D_2411, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_2412))) | ~v1_funct_2(D_2411, '#skF_3', B_2412) | ~v1_funct_1(D_2411))), inference(resolution, [status(thm)], [c_32, c_1639])).
% 3.49/1.66  tff(c_1912, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_34, c_1903])).
% 3.49/1.66  tff(c_1915, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1912])).
% 3.49/1.66  tff(c_1916, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1915])).
% 3.49/1.66  tff(c_41, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.49/1.66  tff(c_6, plain, (![D_7, A_2]: (r2_hidden(D_7, k2_tarski(A_2, D_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.49/1.66  tff(c_47, plain, (![A_20]: (r2_hidden(A_20, k1_tarski(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_41, c_6])).
% 3.49/1.66  tff(c_59, plain, (![B_24, A_25]: (~r1_tarski(B_24, A_25) | ~r2_hidden(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.49/1.66  tff(c_73, plain, (![A_20]: (~r1_tarski(k1_tarski(A_20), A_20))), inference(resolution, [status(thm)], [c_47, c_59])).
% 3.49/1.66  tff(c_1928, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1916, c_73])).
% 3.49/1.66  tff(c_1973, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1928])).
% 3.49/1.66  tff(c_1974, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_1915])).
% 3.49/1.66  tff(c_22, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.49/1.66  tff(c_94, plain, (![D_33, B_34, A_35]: (D_33=B_34 | D_33=A_35 | ~r2_hidden(D_33, k2_tarski(A_35, B_34)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.49/1.66  tff(c_100, plain, (![D_33, A_8]: (D_33=A_8 | D_33=A_8 | ~r2_hidden(D_33, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_94])).
% 3.49/1.66  tff(c_1986, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_1974, c_100])).
% 3.49/1.66  tff(c_2033, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_30, c_1986])).
% 3.49/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.66  
% 3.49/1.66  Inference rules
% 3.49/1.66  ----------------------
% 3.49/1.66  #Ref     : 0
% 3.49/1.66  #Sup     : 281
% 3.49/1.66  #Fact    : 6
% 3.49/1.66  #Define  : 0
% 3.49/1.66  #Split   : 5
% 3.49/1.66  #Chain   : 0
% 3.49/1.66  #Close   : 0
% 3.49/1.66  
% 3.49/1.66  Ordering : KBO
% 3.49/1.66  
% 3.49/1.66  Simplification rules
% 3.49/1.66  ----------------------
% 3.49/1.66  #Subsume      : 50
% 3.49/1.66  #Demod        : 39
% 3.49/1.66  #Tautology    : 75
% 3.49/1.66  #SimpNegUnit  : 1
% 3.49/1.66  #BackRed      : 2
% 3.49/1.66  
% 3.49/1.66  #Partial instantiations: 1911
% 3.49/1.66  #Strategies tried      : 1
% 3.49/1.66  
% 3.49/1.66  Timing (in seconds)
% 3.49/1.66  ----------------------
% 3.49/1.66  Preprocessing        : 0.39
% 3.49/1.66  Parsing              : 0.22
% 3.49/1.66  CNF conversion       : 0.02
% 3.49/1.66  Main loop            : 0.49
% 3.49/1.66  Inferencing          : 0.26
% 3.49/1.66  Reduction            : 0.11
% 3.49/1.66  Demodulation         : 0.08
% 3.49/1.66  BG Simplification    : 0.03
% 3.49/1.66  Subsumption          : 0.06
% 3.49/1.66  Abstraction          : 0.03
% 3.49/1.66  MUC search           : 0.00
% 3.49/1.66  Cooper               : 0.00
% 3.49/1.66  Total                : 0.91
% 3.49/1.66  Index Insertion      : 0.00
% 3.49/1.66  Index Deletion       : 0.00
% 3.49/1.66  Index Matching       : 0.00
% 3.49/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
