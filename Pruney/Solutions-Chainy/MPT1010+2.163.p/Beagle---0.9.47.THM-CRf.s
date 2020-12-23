%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:27 EST 2020

% Result     : Theorem 4.06s
% Output     : CNFRefutation 4.06s
% Verified   : 
% Statistics : Number of formulae       :   51 (  73 expanded)
%              Number of leaves         :   27 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   64 ( 145 expanded)
%              Number of equality atoms :   13 (  33 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_28,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_34,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_32,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_30,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_158,plain,(
    ! [D_57,C_58,B_59,A_60] :
      ( r2_hidden(k1_funct_1(D_57,C_58),B_59)
      | k1_xboole_0 = B_59
      | ~ r2_hidden(C_58,A_60)
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(A_60,B_59)))
      | ~ v1_funct_2(D_57,A_60,B_59)
      | ~ v1_funct_1(D_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4050,plain,(
    ! [D_1735,B_1736] :
      ( r2_hidden(k1_funct_1(D_1735,'#skF_5'),B_1736)
      | k1_xboole_0 = B_1736
      | ~ m1_subset_1(D_1735,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_1736)))
      | ~ v1_funct_2(D_1735,'#skF_3',B_1736)
      | ~ v1_funct_1(D_1735) ) ),
    inference(resolution,[status(thm)],[c_30,c_158])).

tff(c_4057,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_4050])).

tff(c_4061,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_4057])).

tff(c_4113,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_4061])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [C_6] : r2_hidden(C_6,k1_tarski(C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_73,plain,(
    ! [C_31,A_32,B_33] :
      ( r2_hidden(C_31,A_32)
      | ~ r2_hidden(C_31,B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_97,plain,(
    ! [C_39,A_40] :
      ( r2_hidden(C_39,A_40)
      | ~ m1_subset_1(k1_tarski(C_39),k1_zfmisc_1(A_40)) ) ),
    inference(resolution,[status(thm)],[c_6,c_73])).

tff(c_102,plain,(
    ! [C_39,B_15] :
      ( r2_hidden(C_39,B_15)
      | ~ r1_tarski(k1_tarski(C_39),B_15) ) ),
    inference(resolution,[status(thm)],[c_24,c_97])).

tff(c_4136,plain,(
    ! [B_15] :
      ( r2_hidden('#skF_4',B_15)
      | ~ r1_tarski(k1_xboole_0,B_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4113,c_102])).

tff(c_4158,plain,(
    ! [B_1748] : r2_hidden('#skF_4',B_1748) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4136])).

tff(c_4,plain,(
    ! [C_6,A_2] :
      ( C_6 = A_2
      | ~ r2_hidden(C_6,k1_tarski(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4171,plain,(
    ! [A_1749] : A_1749 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4158,c_4])).

tff(c_4294,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_4171,c_28])).

tff(c_4295,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4061])).

tff(c_4303,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4295,c_4])).

tff(c_4309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_4303])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:52:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.06/1.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.06/1.71  
% 4.06/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.06/1.71  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.06/1.71  
% 4.06/1.71  %Foreground sorts:
% 4.06/1.71  
% 4.06/1.71  
% 4.06/1.71  %Background operators:
% 4.06/1.71  
% 4.06/1.71  
% 4.06/1.71  %Foreground operators:
% 4.06/1.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.06/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.06/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.06/1.71  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.06/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.06/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.06/1.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.06/1.71  tff('#skF_5', type, '#skF_5': $i).
% 4.06/1.71  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.06/1.71  tff('#skF_6', type, '#skF_6': $i).
% 4.06/1.71  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.06/1.71  tff('#skF_3', type, '#skF_3': $i).
% 4.06/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.06/1.71  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.06/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.06/1.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.06/1.71  tff('#skF_4', type, '#skF_4': $i).
% 4.06/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.06/1.71  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.06/1.71  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.06/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.06/1.71  
% 4.06/1.72  tff(f_72, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 4.06/1.72  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.06/1.72  tff(f_61, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 4.06/1.72  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.06/1.72  tff(f_34, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.06/1.72  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 4.06/1.72  tff(c_28, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.06/1.72  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.06/1.72  tff(c_36, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.06/1.72  tff(c_34, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.06/1.72  tff(c_32, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.06/1.72  tff(c_30, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.06/1.72  tff(c_158, plain, (![D_57, C_58, B_59, A_60]: (r2_hidden(k1_funct_1(D_57, C_58), B_59) | k1_xboole_0=B_59 | ~r2_hidden(C_58, A_60) | ~m1_subset_1(D_57, k1_zfmisc_1(k2_zfmisc_1(A_60, B_59))) | ~v1_funct_2(D_57, A_60, B_59) | ~v1_funct_1(D_57))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.06/1.72  tff(c_4050, plain, (![D_1735, B_1736]: (r2_hidden(k1_funct_1(D_1735, '#skF_5'), B_1736) | k1_xboole_0=B_1736 | ~m1_subset_1(D_1735, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_1736))) | ~v1_funct_2(D_1735, '#skF_3', B_1736) | ~v1_funct_1(D_1735))), inference(resolution, [status(thm)], [c_30, c_158])).
% 4.06/1.72  tff(c_4057, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_32, c_4050])).
% 4.06/1.72  tff(c_4061, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_4057])).
% 4.06/1.72  tff(c_4113, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_4061])).
% 4.06/1.72  tff(c_24, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.06/1.72  tff(c_6, plain, (![C_6]: (r2_hidden(C_6, k1_tarski(C_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.06/1.72  tff(c_73, plain, (![C_31, A_32, B_33]: (r2_hidden(C_31, A_32) | ~r2_hidden(C_31, B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.06/1.72  tff(c_97, plain, (![C_39, A_40]: (r2_hidden(C_39, A_40) | ~m1_subset_1(k1_tarski(C_39), k1_zfmisc_1(A_40)))), inference(resolution, [status(thm)], [c_6, c_73])).
% 4.06/1.72  tff(c_102, plain, (![C_39, B_15]: (r2_hidden(C_39, B_15) | ~r1_tarski(k1_tarski(C_39), B_15))), inference(resolution, [status(thm)], [c_24, c_97])).
% 4.06/1.72  tff(c_4136, plain, (![B_15]: (r2_hidden('#skF_4', B_15) | ~r1_tarski(k1_xboole_0, B_15))), inference(superposition, [status(thm), theory('equality')], [c_4113, c_102])).
% 4.06/1.72  tff(c_4158, plain, (![B_1748]: (r2_hidden('#skF_4', B_1748))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4136])).
% 4.06/1.72  tff(c_4, plain, (![C_6, A_2]: (C_6=A_2 | ~r2_hidden(C_6, k1_tarski(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.06/1.72  tff(c_4171, plain, (![A_1749]: (A_1749='#skF_4')), inference(resolution, [status(thm)], [c_4158, c_4])).
% 4.06/1.72  tff(c_4294, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_4171, c_28])).
% 4.06/1.72  tff(c_4295, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_4061])).
% 4.06/1.72  tff(c_4303, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_4295, c_4])).
% 4.06/1.72  tff(c_4309, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_4303])).
% 4.06/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.06/1.72  
% 4.06/1.72  Inference rules
% 4.06/1.72  ----------------------
% 4.06/1.72  #Ref     : 0
% 4.06/1.72  #Sup     : 619
% 4.06/1.72  #Fact    : 3
% 4.06/1.72  #Define  : 0
% 4.06/1.72  #Split   : 2
% 4.06/1.72  #Chain   : 0
% 4.06/1.72  #Close   : 0
% 4.06/1.72  
% 4.06/1.72  Ordering : KBO
% 4.06/1.72  
% 4.06/1.72  Simplification rules
% 4.06/1.72  ----------------------
% 4.06/1.72  #Subsume      : 159
% 4.06/1.72  #Demod        : 100
% 4.06/1.72  #Tautology    : 64
% 4.06/1.72  #SimpNegUnit  : 1
% 4.06/1.72  #BackRed      : 3
% 4.06/1.72  
% 4.06/1.72  #Partial instantiations: 1404
% 4.06/1.72  #Strategies tried      : 1
% 4.06/1.72  
% 4.06/1.72  Timing (in seconds)
% 4.06/1.72  ----------------------
% 4.06/1.72  Preprocessing        : 0.31
% 4.06/1.72  Parsing              : 0.16
% 4.06/1.72  CNF conversion       : 0.02
% 4.06/1.72  Main loop            : 0.63
% 4.06/1.72  Inferencing          : 0.26
% 4.06/1.72  Reduction            : 0.15
% 4.06/1.72  Demodulation         : 0.11
% 4.06/1.72  BG Simplification    : 0.03
% 4.06/1.72  Subsumption          : 0.15
% 4.06/1.72  Abstraction          : 0.04
% 4.06/1.72  MUC search           : 0.00
% 4.06/1.72  Cooper               : 0.00
% 4.06/1.72  Total                : 0.97
% 4.06/1.72  Index Insertion      : 0.00
% 4.06/1.72  Index Deletion       : 0.00
% 4.06/1.72  Index Matching       : 0.00
% 4.06/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
