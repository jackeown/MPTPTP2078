%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:23 EST 2020

% Result     : Theorem 12.31s
% Output     : CNFRefutation 12.31s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 101 expanded)
%              Number of leaves         :   33 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :   65 ( 204 expanded)
%              Number of equality atoms :   14 (  45 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_41,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_34,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_86,plain,(
    k1_funct_1('#skF_8','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_94,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_92,plain,(
    v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_90,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_88,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_5920,plain,(
    ! [D_5914,C_5915,B_5916,A_5917] :
      ( r2_hidden(k1_funct_1(D_5914,C_5915),B_5916)
      | k1_xboole_0 = B_5916
      | ~ r2_hidden(C_5915,A_5917)
      | ~ m1_subset_1(D_5914,k1_zfmisc_1(k2_zfmisc_1(A_5917,B_5916)))
      | ~ v1_funct_2(D_5914,A_5917,B_5916)
      | ~ v1_funct_1(D_5914) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_19921,plain,(
    ! [D_30482,B_30483] :
      ( r2_hidden(k1_funct_1(D_30482,'#skF_7'),B_30483)
      | k1_xboole_0 = B_30483
      | ~ m1_subset_1(D_30482,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_30483)))
      | ~ v1_funct_2(D_30482,'#skF_5',B_30483)
      | ~ v1_funct_1(D_30482) ) ),
    inference(resolution,[status(thm)],[c_88,c_5920])).

tff(c_19936,plain,
    ( r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6'))
    | k1_tarski('#skF_6') = k1_xboole_0
    | ~ v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6'))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_90,c_19921])).

tff(c_19939,plain,
    ( r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6'))
    | k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_19936])).

tff(c_19940,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_19939])).

tff(c_18,plain,(
    ! [C_9] : r2_hidden(C_9,k1_tarski(C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_19958,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_19940,c_18])).

tff(c_14,plain,(
    ! [A_4] : k5_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_157,plain,(
    ! [A_105,B_106,C_107] :
      ( r2_hidden(A_105,B_106)
      | ~ r2_hidden(A_105,C_107)
      | r2_hidden(A_105,k5_xboole_0(B_106,C_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_163,plain,(
    ! [A_105,A_4] :
      ( r2_hidden(A_105,A_4)
      | ~ r2_hidden(A_105,k1_xboole_0)
      | r2_hidden(A_105,A_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_157])).

tff(c_19977,plain,(
    ! [A_4] : r2_hidden('#skF_6',A_4) ),
    inference(resolution,[status(thm)],[c_19958,c_163])).

tff(c_19980,plain,(
    ! [A_31948] : r2_hidden('#skF_6',A_31948) ),
    inference(resolution,[status(thm)],[c_19958,c_163])).

tff(c_153,plain,(
    ! [A_102,C_103,B_104] :
      ( ~ r2_hidden(A_102,C_103)
      | ~ r2_hidden(A_102,B_104)
      | ~ r2_hidden(A_102,k5_xboole_0(B_104,C_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_156,plain,(
    ! [A_102,A_4] :
      ( ~ r2_hidden(A_102,k1_xboole_0)
      | ~ r2_hidden(A_102,A_4)
      | ~ r2_hidden(A_102,A_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_153])).

tff(c_20000,plain,(
    ! [A_4] : ~ r2_hidden('#skF_6',A_4) ),
    inference(resolution,[status(thm)],[c_19980,c_156])).

tff(c_20020,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19977,c_20000])).

tff(c_20021,plain,(
    r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_19939])).

tff(c_16,plain,(
    ! [C_9,A_5] :
      ( C_9 = A_5
      | ~ r2_hidden(C_9,k1_tarski(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20027,plain,(
    k1_funct_1('#skF_8','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_20021,c_16])).

tff(c_20032,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_20027])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:23:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.31/5.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.31/5.21  
% 12.31/5.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.31/5.21  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_4 > #skF_1
% 12.31/5.21  
% 12.31/5.21  %Foreground sorts:
% 12.31/5.21  
% 12.31/5.21  
% 12.31/5.21  %Background operators:
% 12.31/5.21  
% 12.31/5.21  
% 12.31/5.21  %Foreground operators:
% 12.31/5.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.31/5.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.31/5.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 12.31/5.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.31/5.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.31/5.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.31/5.21  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 12.31/5.21  tff('#skF_7', type, '#skF_7': $i).
% 12.31/5.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.31/5.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.31/5.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.31/5.21  tff('#skF_5', type, '#skF_5': $i).
% 12.31/5.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.31/5.21  tff('#skF_6', type, '#skF_6': $i).
% 12.31/5.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.31/5.21  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.31/5.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.31/5.21  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 12.31/5.21  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 12.31/5.21  tff('#skF_8', type, '#skF_8': $i).
% 12.31/5.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.31/5.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.31/5.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.31/5.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 12.31/5.21  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 12.31/5.21  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 12.31/5.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.31/5.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.31/5.21  
% 12.31/5.22  tff(f_102, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 12.31/5.22  tff(f_91, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 12.31/5.22  tff(f_41, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 12.31/5.22  tff(f_34, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 12.31/5.22  tff(f_32, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 12.31/5.22  tff(c_86, plain, (k1_funct_1('#skF_8', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.31/5.22  tff(c_94, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.31/5.22  tff(c_92, plain, (v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.31/5.22  tff(c_90, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.31/5.22  tff(c_88, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.31/5.22  tff(c_5920, plain, (![D_5914, C_5915, B_5916, A_5917]: (r2_hidden(k1_funct_1(D_5914, C_5915), B_5916) | k1_xboole_0=B_5916 | ~r2_hidden(C_5915, A_5917) | ~m1_subset_1(D_5914, k1_zfmisc_1(k2_zfmisc_1(A_5917, B_5916))) | ~v1_funct_2(D_5914, A_5917, B_5916) | ~v1_funct_1(D_5914))), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.31/5.22  tff(c_19921, plain, (![D_30482, B_30483]: (r2_hidden(k1_funct_1(D_30482, '#skF_7'), B_30483) | k1_xboole_0=B_30483 | ~m1_subset_1(D_30482, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_30483))) | ~v1_funct_2(D_30482, '#skF_5', B_30483) | ~v1_funct_1(D_30482))), inference(resolution, [status(thm)], [c_88, c_5920])).
% 12.31/5.22  tff(c_19936, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6')) | k1_tarski('#skF_6')=k1_xboole_0 | ~v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6')) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_90, c_19921])).
% 12.31/5.22  tff(c_19939, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6')) | k1_tarski('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_19936])).
% 12.31/5.22  tff(c_19940, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_19939])).
% 12.31/5.22  tff(c_18, plain, (![C_9]: (r2_hidden(C_9, k1_tarski(C_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.31/5.22  tff(c_19958, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_19940, c_18])).
% 12.31/5.22  tff(c_14, plain, (![A_4]: (k5_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.31/5.22  tff(c_157, plain, (![A_105, B_106, C_107]: (r2_hidden(A_105, B_106) | ~r2_hidden(A_105, C_107) | r2_hidden(A_105, k5_xboole_0(B_106, C_107)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.31/5.22  tff(c_163, plain, (![A_105, A_4]: (r2_hidden(A_105, A_4) | ~r2_hidden(A_105, k1_xboole_0) | r2_hidden(A_105, A_4))), inference(superposition, [status(thm), theory('equality')], [c_14, c_157])).
% 12.31/5.22  tff(c_19977, plain, (![A_4]: (r2_hidden('#skF_6', A_4))), inference(resolution, [status(thm)], [c_19958, c_163])).
% 12.31/5.22  tff(c_19980, plain, (![A_31948]: (r2_hidden('#skF_6', A_31948))), inference(resolution, [status(thm)], [c_19958, c_163])).
% 12.31/5.22  tff(c_153, plain, (![A_102, C_103, B_104]: (~r2_hidden(A_102, C_103) | ~r2_hidden(A_102, B_104) | ~r2_hidden(A_102, k5_xboole_0(B_104, C_103)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.31/5.22  tff(c_156, plain, (![A_102, A_4]: (~r2_hidden(A_102, k1_xboole_0) | ~r2_hidden(A_102, A_4) | ~r2_hidden(A_102, A_4))), inference(superposition, [status(thm), theory('equality')], [c_14, c_153])).
% 12.31/5.22  tff(c_20000, plain, (![A_4]: (~r2_hidden('#skF_6', A_4))), inference(resolution, [status(thm)], [c_19980, c_156])).
% 12.31/5.22  tff(c_20020, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19977, c_20000])).
% 12.31/5.22  tff(c_20021, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6'))), inference(splitRight, [status(thm)], [c_19939])).
% 12.31/5.22  tff(c_16, plain, (![C_9, A_5]: (C_9=A_5 | ~r2_hidden(C_9, k1_tarski(A_5)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.31/5.22  tff(c_20027, plain, (k1_funct_1('#skF_8', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_20021, c_16])).
% 12.31/5.22  tff(c_20032, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_20027])).
% 12.31/5.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.31/5.22  
% 12.31/5.22  Inference rules
% 12.31/5.22  ----------------------
% 12.31/5.22  #Ref     : 0
% 12.31/5.22  #Sup     : 3290
% 12.31/5.22  #Fact    : 183
% 12.31/5.22  #Define  : 0
% 12.31/5.22  #Split   : 1
% 12.31/5.22  #Chain   : 0
% 12.31/5.22  #Close   : 0
% 12.31/5.22  
% 12.31/5.22  Ordering : KBO
% 12.31/5.22  
% 12.31/5.22  Simplification rules
% 12.31/5.22  ----------------------
% 12.31/5.22  #Subsume      : 1584
% 12.31/5.22  #Demod        : 370
% 12.31/5.22  #Tautology    : 475
% 12.31/5.22  #SimpNegUnit  : 1
% 12.31/5.22  #BackRed      : 2
% 12.31/5.22  
% 12.31/5.22  #Partial instantiations: 11235
% 12.31/5.22  #Strategies tried      : 1
% 12.31/5.22  
% 12.31/5.22  Timing (in seconds)
% 12.31/5.22  ----------------------
% 12.31/5.22  Preprocessing        : 0.36
% 12.31/5.22  Parsing              : 0.17
% 12.31/5.22  CNF conversion       : 0.03
% 12.31/5.22  Main loop            : 4.11
% 12.31/5.22  Inferencing          : 1.99
% 12.31/5.22  Reduction            : 0.76
% 12.31/5.22  Demodulation         : 0.60
% 12.31/5.22  BG Simplification    : 0.18
% 12.31/5.22  Subsumption          : 1.05
% 12.31/5.22  Abstraction          : 0.41
% 12.31/5.22  MUC search           : 0.00
% 12.31/5.22  Cooper               : 0.00
% 12.31/5.22  Total                : 4.50
% 12.31/5.22  Index Insertion      : 0.00
% 12.31/5.22  Index Deletion       : 0.00
% 12.31/5.22  Index Matching       : 0.00
% 12.31/5.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
