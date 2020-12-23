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
% DateTime   : Thu Dec  3 10:15:21 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   48 (  52 expanded)
%              Number of leaves         :   30 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 (  73 expanded)
%              Number of equality atoms :   18 (  22 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_34,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_71,plain,(
    ! [A_35,B_36] :
      ( k2_xboole_0(A_35,B_36) = B_36
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_76,plain,(
    ! [B_37] : k2_xboole_0(B_37,B_37) = B_37 ),
    inference(resolution,[status(thm)],[c_6,c_71])).

tff(c_30,plain,(
    ! [A_20,B_21] : k2_xboole_0(k1_tarski(A_20),B_21) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_83,plain,(
    ! [A_20] : k1_tarski(A_20) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_30])).

tff(c_42,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_40,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_36,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_153,plain,(
    ! [D_60,C_61,B_62,A_63] :
      ( r2_hidden(k1_funct_1(D_60,C_61),B_62)
      | k1_xboole_0 = B_62
      | ~ r2_hidden(C_61,A_63)
      | ~ m1_subset_1(D_60,k1_zfmisc_1(k2_zfmisc_1(A_63,B_62)))
      | ~ v1_funct_2(D_60,A_63,B_62)
      | ~ v1_funct_1(D_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_166,plain,(
    ! [D_64,B_65] :
      ( r2_hidden(k1_funct_1(D_64,'#skF_5'),B_65)
      | k1_xboole_0 = B_65
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_65)))
      | ~ v1_funct_2(D_64,'#skF_3',B_65)
      | ~ v1_funct_1(D_64) ) ),
    inference(resolution,[status(thm)],[c_36,c_153])).

tff(c_169,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_166])).

tff(c_172,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_169])).

tff(c_173,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_172])).

tff(c_10,plain,(
    ! [C_9,A_5] :
      ( C_9 = A_5
      | ~ r2_hidden(C_9,k1_tarski(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_179,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_173,c_10])).

tff(c_184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_179])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:55:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.19  
% 1.89/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.20  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.89/1.20  
% 1.89/1.20  %Foreground sorts:
% 1.89/1.20  
% 1.89/1.20  
% 1.89/1.20  %Background operators:
% 1.89/1.20  
% 1.89/1.20  
% 1.89/1.20  %Foreground operators:
% 1.89/1.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.89/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.89/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.89/1.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.89/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.89/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.89/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.89/1.20  tff('#skF_5', type, '#skF_5': $i).
% 1.89/1.20  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.89/1.20  tff('#skF_6', type, '#skF_6': $i).
% 1.89/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.89/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.89/1.20  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.89/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.89/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.89/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.20  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.89/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.89/1.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.89/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.89/1.20  
% 1.89/1.21  tff(f_76, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 1.89/1.21  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.89/1.21  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.89/1.21  tff(f_53, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.89/1.21  tff(f_65, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 1.89/1.21  tff(f_42, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.89/1.21  tff(c_34, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.89/1.21  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.89/1.21  tff(c_71, plain, (![A_35, B_36]: (k2_xboole_0(A_35, B_36)=B_36 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.89/1.21  tff(c_76, plain, (![B_37]: (k2_xboole_0(B_37, B_37)=B_37)), inference(resolution, [status(thm)], [c_6, c_71])).
% 1.89/1.21  tff(c_30, plain, (![A_20, B_21]: (k2_xboole_0(k1_tarski(A_20), B_21)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.89/1.21  tff(c_83, plain, (![A_20]: (k1_tarski(A_20)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_76, c_30])).
% 1.89/1.21  tff(c_42, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.89/1.21  tff(c_40, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.89/1.21  tff(c_38, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.89/1.21  tff(c_36, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.89/1.21  tff(c_153, plain, (![D_60, C_61, B_62, A_63]: (r2_hidden(k1_funct_1(D_60, C_61), B_62) | k1_xboole_0=B_62 | ~r2_hidden(C_61, A_63) | ~m1_subset_1(D_60, k1_zfmisc_1(k2_zfmisc_1(A_63, B_62))) | ~v1_funct_2(D_60, A_63, B_62) | ~v1_funct_1(D_60))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.89/1.21  tff(c_166, plain, (![D_64, B_65]: (r2_hidden(k1_funct_1(D_64, '#skF_5'), B_65) | k1_xboole_0=B_65 | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_65))) | ~v1_funct_2(D_64, '#skF_3', B_65) | ~v1_funct_1(D_64))), inference(resolution, [status(thm)], [c_36, c_153])).
% 1.89/1.21  tff(c_169, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_166])).
% 1.89/1.21  tff(c_172, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_169])).
% 1.89/1.21  tff(c_173, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_83, c_172])).
% 1.89/1.21  tff(c_10, plain, (![C_9, A_5]: (C_9=A_5 | ~r2_hidden(C_9, k1_tarski(A_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.89/1.21  tff(c_179, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_173, c_10])).
% 1.89/1.21  tff(c_184, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_179])).
% 1.89/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.21  
% 1.89/1.21  Inference rules
% 1.89/1.21  ----------------------
% 1.89/1.21  #Ref     : 0
% 1.89/1.21  #Sup     : 28
% 1.89/1.21  #Fact    : 0
% 1.89/1.21  #Define  : 0
% 1.89/1.21  #Split   : 0
% 1.89/1.21  #Chain   : 0
% 1.89/1.21  #Close   : 0
% 1.89/1.21  
% 1.89/1.21  Ordering : KBO
% 1.89/1.21  
% 1.89/1.21  Simplification rules
% 1.89/1.21  ----------------------
% 1.89/1.21  #Subsume      : 0
% 1.89/1.21  #Demod        : 6
% 1.89/1.21  #Tautology    : 18
% 1.89/1.21  #SimpNegUnit  : 2
% 1.89/1.21  #BackRed      : 0
% 1.89/1.21  
% 1.89/1.21  #Partial instantiations: 0
% 1.89/1.21  #Strategies tried      : 1
% 1.89/1.21  
% 1.89/1.21  Timing (in seconds)
% 1.89/1.21  ----------------------
% 1.89/1.21  Preprocessing        : 0.31
% 1.89/1.21  Parsing              : 0.16
% 1.89/1.21  CNF conversion       : 0.02
% 1.89/1.21  Main loop            : 0.16
% 1.89/1.21  Inferencing          : 0.06
% 1.89/1.21  Reduction            : 0.05
% 1.89/1.21  Demodulation         : 0.03
% 1.89/1.21  BG Simplification    : 0.01
% 1.89/1.21  Subsumption          : 0.03
% 1.89/1.21  Abstraction          : 0.01
% 1.89/1.21  MUC search           : 0.00
% 1.89/1.21  Cooper               : 0.00
% 1.89/1.21  Total                : 0.49
% 1.89/1.21  Index Insertion      : 0.00
% 1.89/1.21  Index Deletion       : 0.00
% 1.89/1.21  Index Matching       : 0.00
% 1.89/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
