%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:23 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :   56 (  95 expanded)
%              Number of leaves         :   29 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :   71 ( 206 expanded)
%              Number of equality atoms :   26 (  61 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_58,axiom,(
    ! [A,B] :
      ( A != k1_xboole_0
     => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
        & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_38,plain,(
    k1_funct_1('#skF_7','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_139,plain,(
    ! [A_43,B_44] :
      ( ~ r2_hidden('#skF_1'(A_43,B_44),B_44)
      | r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_144,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_139])).

tff(c_26,plain,(
    ! [A_14] : k2_zfmisc_1(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_46,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_44,plain,(
    v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_42,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_tarski('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_40,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_481,plain,(
    ! [D_94,C_95,B_96,A_97] :
      ( r2_hidden(k1_funct_1(D_94,C_95),B_96)
      | k1_xboole_0 = B_96
      | ~ r2_hidden(C_95,A_97)
      | ~ m1_subset_1(D_94,k1_zfmisc_1(k2_zfmisc_1(A_97,B_96)))
      | ~ v1_funct_2(D_94,A_97,B_96)
      | ~ v1_funct_1(D_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_623,plain,(
    ! [D_107,B_108] :
      ( r2_hidden(k1_funct_1(D_107,'#skF_6'),B_108)
      | k1_xboole_0 = B_108
      | ~ m1_subset_1(D_107,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_108)))
      | ~ v1_funct_2(D_107,'#skF_4',B_108)
      | ~ v1_funct_1(D_107) ) ),
    inference(resolution,[status(thm)],[c_40,c_481])).

tff(c_626,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_6'),k1_tarski('#skF_5'))
    | k1_tarski('#skF_5') = k1_xboole_0
    | ~ v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5'))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_42,c_623])).

tff(c_633,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_6'),k1_tarski('#skF_5'))
    | k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_626])).

tff(c_635,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_633])).

tff(c_30,plain,(
    ! [A_16,B_17] :
      ( k2_zfmisc_1(A_16,k1_tarski(B_17)) != k1_xboole_0
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_681,plain,(
    ! [A_16] :
      ( k2_zfmisc_1(A_16,k1_xboole_0) != k1_xboole_0
      | k1_xboole_0 = A_16 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_635,c_30])).

tff(c_717,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_681])).

tff(c_703,plain,(
    ! [A_16] : k1_xboole_0 = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_681])).

tff(c_947,plain,(
    ! [A_1714] : A_1714 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_717,c_703])).

tff(c_79,plain,(
    ! [B_28,A_29] :
      ( ~ r1_tarski(B_28,A_29)
      | ~ r2_hidden(A_29,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_87,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_79])).

tff(c_1037,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_947,c_87])).

tff(c_1060,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_1037])).

tff(c_1061,plain,(
    r2_hidden(k1_funct_1('#skF_7','#skF_6'),k1_tarski('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_633])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( C_10 = A_6
      | ~ r2_hidden(C_10,k1_tarski(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1084,plain,(
    k1_funct_1('#skF_7','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1061,c_8])).

tff(c_1093,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1084])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:34:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.33/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.52  
% 3.33/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.52  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 3.33/1.52  
% 3.33/1.52  %Foreground sorts:
% 3.33/1.52  
% 3.33/1.52  
% 3.33/1.52  %Background operators:
% 3.33/1.52  
% 3.33/1.52  
% 3.33/1.52  %Foreground operators:
% 3.33/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.33/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.33/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.33/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.33/1.52  tff('#skF_7', type, '#skF_7': $i).
% 3.33/1.52  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.33/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.33/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.33/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.33/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.33/1.52  tff('#skF_6', type, '#skF_6': $i).
% 3.33/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.33/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.33/1.52  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.33/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.33/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.33/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.33/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.33/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.33/1.52  
% 3.33/1.53  tff(f_86, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 3.33/1.53  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.33/1.53  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.33/1.53  tff(f_75, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 3.33/1.53  tff(f_58, axiom, (![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 3.33/1.53  tff(f_63, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.33/1.53  tff(f_39, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.33/1.53  tff(c_38, plain, (k1_funct_1('#skF_7', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.33/1.53  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.33/1.53  tff(c_139, plain, (![A_43, B_44]: (~r2_hidden('#skF_1'(A_43, B_44), B_44) | r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.33/1.53  tff(c_144, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_139])).
% 3.33/1.53  tff(c_26, plain, (![A_14]: (k2_zfmisc_1(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.33/1.53  tff(c_46, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.33/1.53  tff(c_44, plain, (v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.33/1.53  tff(c_42, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_tarski('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.33/1.53  tff(c_40, plain, (r2_hidden('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.33/1.53  tff(c_481, plain, (![D_94, C_95, B_96, A_97]: (r2_hidden(k1_funct_1(D_94, C_95), B_96) | k1_xboole_0=B_96 | ~r2_hidden(C_95, A_97) | ~m1_subset_1(D_94, k1_zfmisc_1(k2_zfmisc_1(A_97, B_96))) | ~v1_funct_2(D_94, A_97, B_96) | ~v1_funct_1(D_94))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.33/1.53  tff(c_623, plain, (![D_107, B_108]: (r2_hidden(k1_funct_1(D_107, '#skF_6'), B_108) | k1_xboole_0=B_108 | ~m1_subset_1(D_107, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_108))) | ~v1_funct_2(D_107, '#skF_4', B_108) | ~v1_funct_1(D_107))), inference(resolution, [status(thm)], [c_40, c_481])).
% 3.33/1.53  tff(c_626, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_6'), k1_tarski('#skF_5')) | k1_tarski('#skF_5')=k1_xboole_0 | ~v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5')) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_42, c_623])).
% 3.33/1.53  tff(c_633, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_6'), k1_tarski('#skF_5')) | k1_tarski('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_626])).
% 3.33/1.53  tff(c_635, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_633])).
% 3.33/1.53  tff(c_30, plain, (![A_16, B_17]: (k2_zfmisc_1(A_16, k1_tarski(B_17))!=k1_xboole_0 | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.33/1.53  tff(c_681, plain, (![A_16]: (k2_zfmisc_1(A_16, k1_xboole_0)!=k1_xboole_0 | k1_xboole_0=A_16)), inference(superposition, [status(thm), theory('equality')], [c_635, c_30])).
% 3.33/1.53  tff(c_717, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_681])).
% 3.33/1.53  tff(c_703, plain, (![A_16]: (k1_xboole_0=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_681])).
% 3.33/1.53  tff(c_947, plain, (![A_1714]: (A_1714='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_717, c_703])).
% 3.33/1.53  tff(c_79, plain, (![B_28, A_29]: (~r1_tarski(B_28, A_29) | ~r2_hidden(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.33/1.53  tff(c_87, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_40, c_79])).
% 3.33/1.53  tff(c_1037, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_947, c_87])).
% 3.33/1.53  tff(c_1060, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_144, c_1037])).
% 3.33/1.53  tff(c_1061, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_6'), k1_tarski('#skF_5'))), inference(splitRight, [status(thm)], [c_633])).
% 3.33/1.53  tff(c_8, plain, (![C_10, A_6]: (C_10=A_6 | ~r2_hidden(C_10, k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.33/1.53  tff(c_1084, plain, (k1_funct_1('#skF_7', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_1061, c_8])).
% 3.33/1.53  tff(c_1093, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_1084])).
% 3.33/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.53  
% 3.33/1.53  Inference rules
% 3.33/1.53  ----------------------
% 3.33/1.53  #Ref     : 0
% 3.33/1.53  #Sup     : 323
% 3.33/1.53  #Fact    : 0
% 3.33/1.53  #Define  : 0
% 3.33/1.53  #Split   : 1
% 3.33/1.53  #Chain   : 0
% 3.33/1.53  #Close   : 0
% 3.33/1.53  
% 3.33/1.53  Ordering : KBO
% 3.33/1.53  
% 3.33/1.53  Simplification rules
% 3.33/1.53  ----------------------
% 3.33/1.53  #Subsume      : 62
% 3.33/1.53  #Demod        : 42
% 3.33/1.53  #Tautology    : 64
% 3.33/1.53  #SimpNegUnit  : 11
% 3.33/1.53  #BackRed      : 2
% 3.33/1.53  
% 3.33/1.53  #Partial instantiations: 329
% 3.33/1.53  #Strategies tried      : 1
% 3.33/1.53  
% 3.33/1.53  Timing (in seconds)
% 3.33/1.53  ----------------------
% 3.33/1.53  Preprocessing        : 0.32
% 3.33/1.53  Parsing              : 0.17
% 3.33/1.53  CNF conversion       : 0.02
% 3.33/1.53  Main loop            : 0.44
% 3.33/1.53  Inferencing          : 0.18
% 3.33/1.53  Reduction            : 0.11
% 3.33/1.53  Demodulation         : 0.08
% 3.33/1.53  BG Simplification    : 0.02
% 3.33/1.53  Subsumption          : 0.09
% 3.33/1.53  Abstraction          : 0.03
% 3.33/1.53  MUC search           : 0.00
% 3.33/1.53  Cooper               : 0.00
% 3.33/1.53  Total                : 0.80
% 3.33/1.53  Index Insertion      : 0.00
% 3.33/1.53  Index Deletion       : 0.00
% 3.33/1.53  Index Matching       : 0.00
% 3.33/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
