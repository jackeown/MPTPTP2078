%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:26 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :   54 (  89 expanded)
%              Number of leaves         :   33 (  49 expanded)
%              Depth                    :    8
%              Number of atoms          :   57 ( 180 expanded)
%              Number of equality atoms :   14 (  41 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_97,axiom,(
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

tff(c_98,plain,(
    k1_funct_1('#skF_8','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_106,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_104,plain,(
    v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_102,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_100,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_508,plain,(
    ! [D_199,C_200,B_201,A_202] :
      ( r2_hidden(k1_funct_1(D_199,C_200),B_201)
      | k1_xboole_0 = B_201
      | ~ r2_hidden(C_200,A_202)
      | ~ m1_subset_1(D_199,k1_zfmisc_1(k2_zfmisc_1(A_202,B_201)))
      | ~ v1_funct_2(D_199,A_202,B_201)
      | ~ v1_funct_1(D_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_582,plain,(
    ! [D_212,B_213] :
      ( r2_hidden(k1_funct_1(D_212,'#skF_7'),B_213)
      | k1_xboole_0 = B_213
      | ~ m1_subset_1(D_212,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_213)))
      | ~ v1_funct_2(D_212,'#skF_5',B_213)
      | ~ v1_funct_1(D_212) ) ),
    inference(resolution,[status(thm)],[c_100,c_508])).

tff(c_585,plain,
    ( r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6'))
    | k1_tarski('#skF_6') = k1_xboole_0
    | ~ v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6'))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_102,c_582])).

tff(c_588,plain,
    ( r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6'))
    | k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_104,c_585])).

tff(c_589,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_588])).

tff(c_18,plain,(
    ! [C_9] : r2_hidden(C_9,k1_tarski(C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_598,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_18])).

tff(c_14,plain,(
    ! [A_4] : k5_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_174,plain,(
    ! [A_124,C_125,B_126] :
      ( ~ r2_hidden(A_124,C_125)
      | ~ r2_hidden(A_124,B_126)
      | ~ r2_hidden(A_124,k5_xboole_0(B_126,C_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_183,plain,(
    ! [A_124,A_4] :
      ( ~ r2_hidden(A_124,k1_xboole_0)
      | ~ r2_hidden(A_124,A_4)
      | ~ r2_hidden(A_124,A_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_174])).

tff(c_609,plain,(
    ! [A_4] : ~ r2_hidden('#skF_6',A_4) ),
    inference(resolution,[status(thm)],[c_598,c_183])).

tff(c_612,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_609,c_598])).

tff(c_613,plain,(
    r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_588])).

tff(c_16,plain,(
    ! [C_9,A_5] :
      ( C_9 = A_5
      | ~ r2_hidden(C_9,k1_tarski(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_673,plain,(
    k1_funct_1('#skF_8','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_613,c_16])).

tff(c_678,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_673])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n024.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 12:54:36 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.38/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.55  
% 3.38/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.55  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_2 > #skF_1
% 3.38/1.55  
% 3.38/1.55  %Foreground sorts:
% 3.38/1.55  
% 3.38/1.55  
% 3.38/1.55  %Background operators:
% 3.38/1.55  
% 3.38/1.55  
% 3.38/1.55  %Foreground operators:
% 3.38/1.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.38/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.38/1.55  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.38/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.38/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.38/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.38/1.55  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.38/1.55  tff('#skF_7', type, '#skF_7': $i).
% 3.38/1.55  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.38/1.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.38/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.38/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.38/1.55  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.38/1.55  tff('#skF_6', type, '#skF_6': $i).
% 3.38/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.38/1.55  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.38/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.38/1.55  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.38/1.55  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.38/1.55  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.38/1.55  tff('#skF_8', type, '#skF_8': $i).
% 3.38/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.38/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.38/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.38/1.55  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.38/1.55  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.38/1.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.38/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.38/1.55  
% 3.38/1.56  tff(f_108, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 3.38/1.56  tff(f_97, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 3.38/1.56  tff(f_41, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.38/1.56  tff(f_34, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.38/1.56  tff(f_32, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.38/1.56  tff(c_98, plain, (k1_funct_1('#skF_8', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.38/1.56  tff(c_106, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.38/1.56  tff(c_104, plain, (v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.38/1.56  tff(c_102, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.38/1.56  tff(c_100, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.38/1.56  tff(c_508, plain, (![D_199, C_200, B_201, A_202]: (r2_hidden(k1_funct_1(D_199, C_200), B_201) | k1_xboole_0=B_201 | ~r2_hidden(C_200, A_202) | ~m1_subset_1(D_199, k1_zfmisc_1(k2_zfmisc_1(A_202, B_201))) | ~v1_funct_2(D_199, A_202, B_201) | ~v1_funct_1(D_199))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.38/1.56  tff(c_582, plain, (![D_212, B_213]: (r2_hidden(k1_funct_1(D_212, '#skF_7'), B_213) | k1_xboole_0=B_213 | ~m1_subset_1(D_212, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_213))) | ~v1_funct_2(D_212, '#skF_5', B_213) | ~v1_funct_1(D_212))), inference(resolution, [status(thm)], [c_100, c_508])).
% 3.38/1.56  tff(c_585, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6')) | k1_tarski('#skF_6')=k1_xboole_0 | ~v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6')) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_102, c_582])).
% 3.38/1.56  tff(c_588, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6')) | k1_tarski('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_106, c_104, c_585])).
% 3.38/1.56  tff(c_589, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_588])).
% 3.38/1.56  tff(c_18, plain, (![C_9]: (r2_hidden(C_9, k1_tarski(C_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.38/1.56  tff(c_598, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_589, c_18])).
% 3.38/1.56  tff(c_14, plain, (![A_4]: (k5_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.38/1.56  tff(c_174, plain, (![A_124, C_125, B_126]: (~r2_hidden(A_124, C_125) | ~r2_hidden(A_124, B_126) | ~r2_hidden(A_124, k5_xboole_0(B_126, C_125)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.38/1.56  tff(c_183, plain, (![A_124, A_4]: (~r2_hidden(A_124, k1_xboole_0) | ~r2_hidden(A_124, A_4) | ~r2_hidden(A_124, A_4))), inference(superposition, [status(thm), theory('equality')], [c_14, c_174])).
% 3.38/1.56  tff(c_609, plain, (![A_4]: (~r2_hidden('#skF_6', A_4))), inference(resolution, [status(thm)], [c_598, c_183])).
% 3.38/1.56  tff(c_612, plain, $false, inference(negUnitSimplification, [status(thm)], [c_609, c_598])).
% 3.38/1.56  tff(c_613, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6'))), inference(splitRight, [status(thm)], [c_588])).
% 3.38/1.56  tff(c_16, plain, (![C_9, A_5]: (C_9=A_5 | ~r2_hidden(C_9, k1_tarski(A_5)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.38/1.56  tff(c_673, plain, (k1_funct_1('#skF_8', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_613, c_16])).
% 3.38/1.56  tff(c_678, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_673])).
% 3.38/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.56  
% 3.38/1.56  Inference rules
% 3.38/1.56  ----------------------
% 3.38/1.56  #Ref     : 0
% 3.38/1.56  #Sup     : 134
% 3.38/1.56  #Fact    : 0
% 3.38/1.56  #Define  : 0
% 3.38/1.56  #Split   : 2
% 3.38/1.56  #Chain   : 0
% 3.38/1.56  #Close   : 0
% 3.38/1.56  
% 3.38/1.56  Ordering : KBO
% 3.38/1.56  
% 3.38/1.56  Simplification rules
% 3.38/1.56  ----------------------
% 3.38/1.56  #Subsume      : 14
% 3.38/1.56  #Demod        : 22
% 3.38/1.56  #Tautology    : 59
% 3.38/1.56  #SimpNegUnit  : 2
% 3.38/1.56  #BackRed      : 3
% 3.38/1.56  
% 3.38/1.56  #Partial instantiations: 0
% 3.38/1.56  #Strategies tried      : 1
% 3.38/1.56  
% 3.38/1.56  Timing (in seconds)
% 3.38/1.56  ----------------------
% 3.38/1.57  Preprocessing        : 0.39
% 3.38/1.57  Parsing              : 0.19
% 3.38/1.57  CNF conversion       : 0.03
% 3.38/1.57  Main loop            : 0.37
% 3.38/1.57  Inferencing          : 0.11
% 3.38/1.57  Reduction            : 0.10
% 3.38/1.57  Demodulation         : 0.08
% 3.38/1.57  BG Simplification    : 0.03
% 3.38/1.57  Subsumption          : 0.11
% 3.38/1.57  Abstraction          : 0.03
% 3.38/1.57  MUC search           : 0.00
% 3.38/1.57  Cooper               : 0.00
% 3.38/1.57  Total                : 0.78
% 3.38/1.57  Index Insertion      : 0.00
% 3.38/1.57  Index Deletion       : 0.00
% 3.38/1.57  Index Matching       : 0.00
% 3.38/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
