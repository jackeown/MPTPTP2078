%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:25 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :   52 (  70 expanded)
%              Number of leaves         :   32 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :   52 ( 122 expanded)
%              Number of equality atoms :   16 (  31 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_2 > #skF_1

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

tff(f_52,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_92,plain,(
    k1_funct_1('#skF_8','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_30,plain,(
    ! [A_34] : k2_zfmisc_1(A_34,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_133,plain,(
    ! [A_58,B_59] : ~ r2_hidden(A_58,k2_zfmisc_1(A_58,B_59)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_136,plain,(
    ! [A_34] : ~ r2_hidden(A_34,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_133])).

tff(c_100,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_98,plain,(
    v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_96,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_94,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_333,plain,(
    ! [D_170,C_171,B_172,A_173] :
      ( r2_hidden(k1_funct_1(D_170,C_171),B_172)
      | k1_xboole_0 = B_172
      | ~ r2_hidden(C_171,A_173)
      | ~ m1_subset_1(D_170,k1_zfmisc_1(k2_zfmisc_1(A_173,B_172)))
      | ~ v1_funct_2(D_170,A_173,B_172)
      | ~ v1_funct_1(D_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_481,plain,(
    ! [D_223,B_224] :
      ( r2_hidden(k1_funct_1(D_223,'#skF_7'),B_224)
      | k1_xboole_0 = B_224
      | ~ m1_subset_1(D_223,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_224)))
      | ~ v1_funct_2(D_223,'#skF_5',B_224)
      | ~ v1_funct_1(D_223) ) ),
    inference(resolution,[status(thm)],[c_94,c_333])).

tff(c_484,plain,
    ( r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6'))
    | k1_tarski('#skF_6') = k1_xboole_0
    | ~ v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6'))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_96,c_481])).

tff(c_491,plain,
    ( r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6'))
    | k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_484])).

tff(c_523,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_491])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_543,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_4])).

tff(c_550,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_543])).

tff(c_551,plain,(
    r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_491])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_557,plain,(
    k1_funct_1('#skF_8','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_551,c_2])).

tff(c_562,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_557])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:42:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.35/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.57  
% 3.35/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.57  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_2 > #skF_1
% 3.35/1.57  
% 3.35/1.57  %Foreground sorts:
% 3.35/1.57  
% 3.35/1.57  
% 3.35/1.57  %Background operators:
% 3.35/1.57  
% 3.35/1.57  
% 3.35/1.57  %Foreground operators:
% 3.35/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.35/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.35/1.57  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.35/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.35/1.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.35/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.35/1.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.35/1.57  tff('#skF_7', type, '#skF_7': $i).
% 3.35/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.35/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.35/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.35/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.35/1.57  tff('#skF_6', type, '#skF_6': $i).
% 3.35/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.35/1.57  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.35/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.35/1.57  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.35/1.57  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.35/1.57  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.35/1.57  tff('#skF_8', type, '#skF_8': $i).
% 3.35/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.35/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.35/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.35/1.57  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.35/1.57  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.35/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.35/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.35/1.57  
% 3.35/1.58  tff(f_108, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 3.35/1.58  tff(f_52, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.35/1.58  tff(f_55, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.35/1.58  tff(f_97, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 3.35/1.58  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.35/1.58  tff(c_92, plain, (k1_funct_1('#skF_8', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.35/1.58  tff(c_30, plain, (![A_34]: (k2_zfmisc_1(A_34, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.35/1.58  tff(c_133, plain, (![A_58, B_59]: (~r2_hidden(A_58, k2_zfmisc_1(A_58, B_59)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.35/1.58  tff(c_136, plain, (![A_34]: (~r2_hidden(A_34, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_133])).
% 3.35/1.58  tff(c_100, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.35/1.58  tff(c_98, plain, (v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.35/1.58  tff(c_96, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.35/1.58  tff(c_94, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.35/1.58  tff(c_333, plain, (![D_170, C_171, B_172, A_173]: (r2_hidden(k1_funct_1(D_170, C_171), B_172) | k1_xboole_0=B_172 | ~r2_hidden(C_171, A_173) | ~m1_subset_1(D_170, k1_zfmisc_1(k2_zfmisc_1(A_173, B_172))) | ~v1_funct_2(D_170, A_173, B_172) | ~v1_funct_1(D_170))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.35/1.58  tff(c_481, plain, (![D_223, B_224]: (r2_hidden(k1_funct_1(D_223, '#skF_7'), B_224) | k1_xboole_0=B_224 | ~m1_subset_1(D_223, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_224))) | ~v1_funct_2(D_223, '#skF_5', B_224) | ~v1_funct_1(D_223))), inference(resolution, [status(thm)], [c_94, c_333])).
% 3.35/1.58  tff(c_484, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6')) | k1_tarski('#skF_6')=k1_xboole_0 | ~v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6')) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_96, c_481])).
% 3.35/1.58  tff(c_491, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6')) | k1_tarski('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_484])).
% 3.35/1.58  tff(c_523, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_491])).
% 3.35/1.58  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.35/1.58  tff(c_543, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_523, c_4])).
% 3.35/1.58  tff(c_550, plain, $false, inference(negUnitSimplification, [status(thm)], [c_136, c_543])).
% 3.35/1.58  tff(c_551, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6'))), inference(splitRight, [status(thm)], [c_491])).
% 3.35/1.58  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.35/1.58  tff(c_557, plain, (k1_funct_1('#skF_8', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_551, c_2])).
% 3.35/1.58  tff(c_562, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_557])).
% 3.35/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.58  
% 3.35/1.58  Inference rules
% 3.35/1.58  ----------------------
% 3.35/1.58  #Ref     : 0
% 3.35/1.58  #Sup     : 109
% 3.35/1.58  #Fact    : 0
% 3.35/1.58  #Define  : 0
% 3.35/1.58  #Split   : 2
% 3.35/1.58  #Chain   : 0
% 3.35/1.58  #Close   : 0
% 3.35/1.58  
% 3.35/1.58  Ordering : KBO
% 3.35/1.58  
% 3.35/1.58  Simplification rules
% 3.35/1.58  ----------------------
% 3.35/1.58  #Subsume      : 7
% 3.35/1.58  #Demod        : 25
% 3.35/1.58  #Tautology    : 48
% 3.35/1.58  #SimpNegUnit  : 4
% 3.35/1.58  #BackRed      : 2
% 3.35/1.58  
% 3.35/1.58  #Partial instantiations: 0
% 3.35/1.58  #Strategies tried      : 1
% 3.35/1.58  
% 3.35/1.58  Timing (in seconds)
% 3.35/1.58  ----------------------
% 3.35/1.58  Preprocessing        : 0.38
% 3.35/1.58  Parsing              : 0.19
% 3.35/1.58  CNF conversion       : 0.03
% 3.35/1.58  Main loop            : 0.36
% 3.35/1.58  Inferencing          : 0.10
% 3.35/1.58  Reduction            : 0.10
% 3.35/1.58  Demodulation         : 0.07
% 3.35/1.58  BG Simplification    : 0.03
% 3.35/1.58  Subsumption          : 0.11
% 3.35/1.58  Abstraction          : 0.03
% 3.35/1.58  MUC search           : 0.00
% 3.35/1.58  Cooper               : 0.00
% 3.35/1.58  Total                : 0.76
% 3.35/1.58  Index Insertion      : 0.00
% 3.35/1.58  Index Deletion       : 0.00
% 3.35/1.58  Index Matching       : 0.00
% 3.35/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
