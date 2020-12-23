%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:24 EST 2020

% Result     : Theorem 4.86s
% Output     : CNFRefutation 5.03s
% Verified   : 
% Statistics : Number of formulae       :   57 (  62 expanded)
%              Number of leaves         :   35 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :   65 (  89 expanded)
%              Number of equality atoms :   24 (  29 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_58,plain,(
    k1_funct_1('#skF_8','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2233,plain,(
    ! [A_3570,B_3571,C_3572] :
      ( r2_hidden('#skF_1'(A_3570,B_3571,C_3572),A_3570)
      | r2_hidden('#skF_2'(A_3570,B_3571,C_3572),C_3572)
      | k4_xboole_0(A_3570,B_3571) = C_3572 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2371,plain,(
    ! [A_3626,C_3627] :
      ( r2_hidden('#skF_2'(A_3626,A_3626,C_3627),C_3627)
      | k4_xboole_0(A_3626,A_3626) = C_3627 ) ),
    inference(resolution,[status(thm)],[c_2233,c_16])).

tff(c_20,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_133,plain,(
    ! [A_67,B_68] :
      ( ~ r2_hidden(A_67,B_68)
      | k4_xboole_0(k1_tarski(A_67),B_68) != k1_tarski(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_142,plain,(
    ! [A_67] : ~ r2_hidden(A_67,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_133])).

tff(c_2435,plain,(
    ! [A_3626] : k4_xboole_0(A_3626,A_3626) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2371,c_142])).

tff(c_52,plain,(
    ! [B_44] : k4_xboole_0(k1_tarski(B_44),k1_tarski(B_44)) != k1_tarski(B_44) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2440,plain,(
    ! [B_44] : k1_tarski(B_44) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2435,c_52])).

tff(c_66,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_64,plain,(
    v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_62,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_60,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3287,plain,(
    ! [D_4341,C_4342,B_4343,A_4344] :
      ( r2_hidden(k1_funct_1(D_4341,C_4342),B_4343)
      | k1_xboole_0 = B_4343
      | ~ r2_hidden(C_4342,A_4344)
      | ~ m1_subset_1(D_4341,k1_zfmisc_1(k2_zfmisc_1(A_4344,B_4343)))
      | ~ v1_funct_2(D_4341,A_4344,B_4343)
      | ~ v1_funct_1(D_4341) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3616,plain,(
    ! [D_4565,B_4566] :
      ( r2_hidden(k1_funct_1(D_4565,'#skF_7'),B_4566)
      | k1_xboole_0 = B_4566
      | ~ m1_subset_1(D_4565,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_4566)))
      | ~ v1_funct_2(D_4565,'#skF_5',B_4566)
      | ~ v1_funct_1(D_4565) ) ),
    inference(resolution,[status(thm)],[c_60,c_3287])).

tff(c_3621,plain,
    ( r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6'))
    | k1_tarski('#skF_6') = k1_xboole_0
    | ~ v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6'))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_62,c_3616])).

tff(c_3624,plain,
    ( r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6'))
    | k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_3621])).

tff(c_3625,plain,(
    r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_2440,c_3624])).

tff(c_22,plain,(
    ! [C_12,A_8] :
      ( C_12 = A_8
      | ~ r2_hidden(C_12,k1_tarski(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3654,plain,(
    k1_funct_1('#skF_8','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3625,c_22])).

tff(c_3717,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_3654])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:29:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.86/1.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.86/1.85  
% 4.86/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.86/1.86  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4
% 4.86/1.86  
% 4.86/1.86  %Foreground sorts:
% 4.86/1.86  
% 4.86/1.86  
% 4.86/1.86  %Background operators:
% 4.86/1.86  
% 4.86/1.86  
% 4.86/1.86  %Foreground operators:
% 4.86/1.86  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.86/1.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.86/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.86/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.86/1.86  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.86/1.86  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.86/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.86/1.86  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.86/1.86  tff('#skF_7', type, '#skF_7': $i).
% 4.86/1.86  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.86/1.86  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.86/1.86  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.86/1.86  tff('#skF_5', type, '#skF_5': $i).
% 4.86/1.86  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.86/1.86  tff('#skF_6', type, '#skF_6': $i).
% 4.86/1.86  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.86/1.86  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.86/1.86  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.86/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.86/1.86  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.86/1.86  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.86/1.86  tff('#skF_8', type, '#skF_8': $i).
% 4.86/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.86/1.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.86/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.86/1.86  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.86/1.86  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.86/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.86/1.86  
% 5.03/1.87  tff(f_91, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 5.03/1.87  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.03/1.87  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.03/1.87  tff(f_63, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 5.03/1.87  tff(f_68, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 5.03/1.87  tff(f_80, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 5.03/1.87  tff(f_44, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 5.03/1.87  tff(c_58, plain, (k1_funct_1('#skF_8', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.03/1.87  tff(c_2233, plain, (![A_3570, B_3571, C_3572]: (r2_hidden('#skF_1'(A_3570, B_3571, C_3572), A_3570) | r2_hidden('#skF_2'(A_3570, B_3571, C_3572), C_3572) | k4_xboole_0(A_3570, B_3571)=C_3572)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.03/1.87  tff(c_16, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.03/1.87  tff(c_2371, plain, (![A_3626, C_3627]: (r2_hidden('#skF_2'(A_3626, A_3626, C_3627), C_3627) | k4_xboole_0(A_3626, A_3626)=C_3627)), inference(resolution, [status(thm)], [c_2233, c_16])).
% 5.03/1.87  tff(c_20, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.03/1.87  tff(c_133, plain, (![A_67, B_68]: (~r2_hidden(A_67, B_68) | k4_xboole_0(k1_tarski(A_67), B_68)!=k1_tarski(A_67))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.03/1.87  tff(c_142, plain, (![A_67]: (~r2_hidden(A_67, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_133])).
% 5.03/1.87  tff(c_2435, plain, (![A_3626]: (k4_xboole_0(A_3626, A_3626)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2371, c_142])).
% 5.03/1.87  tff(c_52, plain, (![B_44]: (k4_xboole_0(k1_tarski(B_44), k1_tarski(B_44))!=k1_tarski(B_44))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.03/1.87  tff(c_2440, plain, (![B_44]: (k1_tarski(B_44)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2435, c_52])).
% 5.03/1.87  tff(c_66, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.03/1.87  tff(c_64, plain, (v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.03/1.87  tff(c_62, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.03/1.87  tff(c_60, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.03/1.87  tff(c_3287, plain, (![D_4341, C_4342, B_4343, A_4344]: (r2_hidden(k1_funct_1(D_4341, C_4342), B_4343) | k1_xboole_0=B_4343 | ~r2_hidden(C_4342, A_4344) | ~m1_subset_1(D_4341, k1_zfmisc_1(k2_zfmisc_1(A_4344, B_4343))) | ~v1_funct_2(D_4341, A_4344, B_4343) | ~v1_funct_1(D_4341))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.03/1.87  tff(c_3616, plain, (![D_4565, B_4566]: (r2_hidden(k1_funct_1(D_4565, '#skF_7'), B_4566) | k1_xboole_0=B_4566 | ~m1_subset_1(D_4565, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_4566))) | ~v1_funct_2(D_4565, '#skF_5', B_4566) | ~v1_funct_1(D_4565))), inference(resolution, [status(thm)], [c_60, c_3287])).
% 5.03/1.87  tff(c_3621, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6')) | k1_tarski('#skF_6')=k1_xboole_0 | ~v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6')) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_62, c_3616])).
% 5.03/1.87  tff(c_3624, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6')) | k1_tarski('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_3621])).
% 5.03/1.87  tff(c_3625, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_2440, c_3624])).
% 5.03/1.87  tff(c_22, plain, (![C_12, A_8]: (C_12=A_8 | ~r2_hidden(C_12, k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.03/1.87  tff(c_3654, plain, (k1_funct_1('#skF_8', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_3625, c_22])).
% 5.03/1.87  tff(c_3717, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_3654])).
% 5.03/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.03/1.87  
% 5.03/1.87  Inference rules
% 5.03/1.87  ----------------------
% 5.03/1.87  #Ref     : 0
% 5.03/1.87  #Sup     : 584
% 5.03/1.87  #Fact    : 0
% 5.03/1.87  #Define  : 0
% 5.03/1.87  #Split   : 4
% 5.03/1.87  #Chain   : 0
% 5.03/1.87  #Close   : 0
% 5.03/1.87  
% 5.03/1.87  Ordering : KBO
% 5.03/1.87  
% 5.03/1.87  Simplification rules
% 5.03/1.87  ----------------------
% 5.03/1.87  #Subsume      : 67
% 5.03/1.87  #Demod        : 95
% 5.03/1.87  #Tautology    : 172
% 5.03/1.87  #SimpNegUnit  : 48
% 5.03/1.87  #BackRed      : 2
% 5.03/1.87  
% 5.03/1.87  #Partial instantiations: 1743
% 5.03/1.87  #Strategies tried      : 1
% 5.03/1.87  
% 5.03/1.87  Timing (in seconds)
% 5.03/1.87  ----------------------
% 5.03/1.87  Preprocessing        : 0.33
% 5.03/1.87  Parsing              : 0.17
% 5.03/1.87  CNF conversion       : 0.02
% 5.03/1.87  Main loop            : 0.79
% 5.03/1.87  Inferencing          : 0.34
% 5.03/1.87  Reduction            : 0.19
% 5.03/1.87  Demodulation         : 0.12
% 5.03/1.87  BG Simplification    : 0.04
% 5.03/1.87  Subsumption          : 0.16
% 5.03/1.87  Abstraction          : 0.05
% 5.03/1.87  MUC search           : 0.00
% 5.03/1.87  Cooper               : 0.00
% 5.03/1.87  Total                : 1.14
% 5.03/1.87  Index Insertion      : 0.00
% 5.03/1.87  Index Deletion       : 0.00
% 5.03/1.87  Index Matching       : 0.00
% 5.03/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
