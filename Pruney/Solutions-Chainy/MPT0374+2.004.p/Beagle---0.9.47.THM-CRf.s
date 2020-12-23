%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:59 EST 2020

% Result     : Theorem 3.76s
% Output     : CNFRefutation 4.11s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 126 expanded)
%              Number of leaves         :   36 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  100 ( 235 expanded)
%              Number of equality atoms :   24 (  51 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_135,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,A)
       => ! [C] :
            ( m1_subset_1(C,A)
           => ( A != k1_xboole_0
             => m1_subset_1(k2_tarski(B,C),k1_zfmisc_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_subset_1)).

tff(f_124,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_xboole_0
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(c_26,plain,(
    ! [A_11] : k4_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | k4_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_32,plain,(
    ! [C_17] : r2_hidden(C_17,k1_tarski(C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2433,plain,(
    ! [D_3299,B_3300,A_3301] :
      ( ~ r2_hidden(D_3299,B_3300)
      | ~ r2_hidden(D_3299,k4_xboole_0(A_3301,B_3300)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2440,plain,(
    ! [D_3302,A_3303] :
      ( ~ r2_hidden(D_3302,A_3303)
      | ~ r2_hidden(D_3302,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2433])).

tff(c_2449,plain,(
    ! [C_17] : ~ r2_hidden(C_17,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32,c_2440])).

tff(c_90,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_92,plain,(
    m1_subset_1('#skF_9','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_86,plain,(
    ! [B_48,A_47] :
      ( m1_subset_1(k1_tarski(B_48),k1_zfmisc_1(A_47))
      | k1_xboole_0 = A_47
      | ~ m1_subset_1(B_48,A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1655,plain,(
    ! [C_1807,A_1808,B_1809] :
      ( r2_hidden(C_1807,A_1808)
      | ~ r2_hidden(C_1807,B_1809)
      | ~ m1_subset_1(B_1809,k1_zfmisc_1(A_1808)) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1665,plain,(
    ! [C_1810,A_1811] :
      ( r2_hidden(C_1810,A_1811)
      | ~ m1_subset_1(k1_tarski(C_1810),k1_zfmisc_1(A_1811)) ) ),
    inference(resolution,[status(thm)],[c_32,c_1655])).

tff(c_1672,plain,(
    ! [B_48,A_47] :
      ( r2_hidden(B_48,A_47)
      | k1_xboole_0 = A_47
      | ~ m1_subset_1(B_48,A_47) ) ),
    inference(resolution,[status(thm)],[c_86,c_1665])).

tff(c_94,plain,(
    m1_subset_1('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_60,plain,(
    ! [A_27,B_28,C_29] :
      ( k4_xboole_0(k2_tarski(A_27,B_28),C_29) = k1_xboole_0
      | ~ r2_hidden(B_28,C_29)
      | ~ r2_hidden(A_27,C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1518,plain,(
    ! [B_1773,A_1774] :
      ( m1_subset_1(B_1773,A_1774)
      | ~ v1_xboole_0(B_1773)
      | ~ v1_xboole_0(A_1774) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_88,plain,(
    ~ m1_subset_1(k2_tarski('#skF_8','#skF_9'),k1_zfmisc_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1526,plain,
    ( ~ v1_xboole_0(k2_tarski('#skF_8','#skF_9'))
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_1518,c_88])).

tff(c_1527,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1526])).

tff(c_44,plain,(
    ! [C_22,A_18] :
      ( r2_hidden(C_22,k1_zfmisc_1(A_18))
      | ~ r1_tarski(C_22,A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1560,plain,(
    ! [B_1786,A_1787] :
      ( m1_subset_1(B_1786,A_1787)
      | ~ r2_hidden(B_1786,A_1787)
      | v1_xboole_0(A_1787) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2271,plain,(
    ! [C_3105,A_3106] :
      ( m1_subset_1(C_3105,k1_zfmisc_1(A_3106))
      | v1_xboole_0(k1_zfmisc_1(A_3106))
      | ~ r1_tarski(C_3105,A_3106) ) ),
    inference(resolution,[status(thm)],[c_44,c_1560])).

tff(c_2284,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_7'))
    | ~ r1_tarski(k2_tarski('#skF_8','#skF_9'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_2271,c_88])).

tff(c_2291,plain,(
    ~ r1_tarski(k2_tarski('#skF_8','#skF_9'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_1527,c_2284])).

tff(c_2325,plain,(
    k4_xboole_0(k2_tarski('#skF_8','#skF_9'),'#skF_7') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_2291])).

tff(c_2331,plain,
    ( ~ r2_hidden('#skF_9','#skF_7')
    | ~ r2_hidden('#skF_8','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_2325])).

tff(c_2332,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_2331])).

tff(c_2335,plain,
    ( k1_xboole_0 = '#skF_7'
    | ~ m1_subset_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_1672,c_2332])).

tff(c_2341,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_2335])).

tff(c_2343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_2341])).

tff(c_2344,plain,(
    ~ r2_hidden('#skF_9','#skF_7') ),
    inference(splitRight,[status(thm)],[c_2331])).

tff(c_2357,plain,
    ( k1_xboole_0 = '#skF_7'
    | ~ m1_subset_1('#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_1672,c_2344])).

tff(c_2363,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_2357])).

tff(c_2365,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_2363])).

tff(c_2367,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1526])).

tff(c_28,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2371,plain,(
    k1_zfmisc_1('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2367,c_28])).

tff(c_2381,plain,(
    ! [C_22] :
      ( r2_hidden(C_22,k1_xboole_0)
      | ~ r1_tarski(C_22,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2371,c_44])).

tff(c_2464,plain,(
    ! [C_3307] : ~ r1_tarski(C_3307,'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_2449,c_2381])).

tff(c_2470,plain,(
    ! [A_3308] : k4_xboole_0(A_3308,'#skF_7') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_2464])).

tff(c_2484,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2470])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:29:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.76/1.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.76/1.80  
% 3.76/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.76/1.80  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4
% 3.76/1.80  
% 3.76/1.80  %Foreground sorts:
% 3.76/1.80  
% 3.76/1.80  
% 3.76/1.80  %Background operators:
% 3.76/1.80  
% 3.76/1.80  
% 3.76/1.80  %Foreground operators:
% 3.76/1.80  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.76/1.80  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.76/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.76/1.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.76/1.80  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.76/1.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.76/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.76/1.80  tff('#skF_7', type, '#skF_7': $i).
% 3.76/1.80  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.76/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.76/1.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.76/1.80  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.76/1.80  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.76/1.80  tff('#skF_9', type, '#skF_9': $i).
% 3.76/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.76/1.80  tff('#skF_8', type, '#skF_8': $i).
% 3.76/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.76/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.76/1.80  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.76/1.80  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.76/1.80  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.76/1.80  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.76/1.80  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.76/1.80  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.76/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.76/1.80  
% 4.11/1.82  tff(f_43, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 4.11/1.82  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 4.11/1.82  tff(f_54, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.11/1.82  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.11/1.82  tff(f_135, negated_conjecture, ~(![A, B]: (m1_subset_1(B, A) => (![C]: (m1_subset_1(C, A) => (~(A = k1_xboole_0) => m1_subset_1(k2_tarski(B, C), k1_zfmisc_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_subset_1)).
% 4.11/1.82  tff(f_124, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 4.11/1.82  tff(f_101, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 4.11/1.82  tff(f_75, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_xboole_0) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 4.11/1.82  tff(f_88, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.11/1.82  tff(f_61, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.11/1.82  tff(f_47, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_boole)).
% 4.11/1.82  tff(c_26, plain, (![A_11]: (k4_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.11/1.82  tff(c_20, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | k4_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.11/1.82  tff(c_32, plain, (![C_17]: (r2_hidden(C_17, k1_tarski(C_17)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.11/1.82  tff(c_2433, plain, (![D_3299, B_3300, A_3301]: (~r2_hidden(D_3299, B_3300) | ~r2_hidden(D_3299, k4_xboole_0(A_3301, B_3300)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.11/1.82  tff(c_2440, plain, (![D_3302, A_3303]: (~r2_hidden(D_3302, A_3303) | ~r2_hidden(D_3302, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2433])).
% 4.11/1.82  tff(c_2449, plain, (![C_17]: (~r2_hidden(C_17, k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_2440])).
% 4.11/1.82  tff(c_90, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.11/1.82  tff(c_92, plain, (m1_subset_1('#skF_9', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.11/1.82  tff(c_86, plain, (![B_48, A_47]: (m1_subset_1(k1_tarski(B_48), k1_zfmisc_1(A_47)) | k1_xboole_0=A_47 | ~m1_subset_1(B_48, A_47))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.11/1.82  tff(c_1655, plain, (![C_1807, A_1808, B_1809]: (r2_hidden(C_1807, A_1808) | ~r2_hidden(C_1807, B_1809) | ~m1_subset_1(B_1809, k1_zfmisc_1(A_1808)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.11/1.82  tff(c_1665, plain, (![C_1810, A_1811]: (r2_hidden(C_1810, A_1811) | ~m1_subset_1(k1_tarski(C_1810), k1_zfmisc_1(A_1811)))), inference(resolution, [status(thm)], [c_32, c_1655])).
% 4.11/1.82  tff(c_1672, plain, (![B_48, A_47]: (r2_hidden(B_48, A_47) | k1_xboole_0=A_47 | ~m1_subset_1(B_48, A_47))), inference(resolution, [status(thm)], [c_86, c_1665])).
% 4.11/1.82  tff(c_94, plain, (m1_subset_1('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.11/1.82  tff(c_60, plain, (![A_27, B_28, C_29]: (k4_xboole_0(k2_tarski(A_27, B_28), C_29)=k1_xboole_0 | ~r2_hidden(B_28, C_29) | ~r2_hidden(A_27, C_29))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.11/1.82  tff(c_1518, plain, (![B_1773, A_1774]: (m1_subset_1(B_1773, A_1774) | ~v1_xboole_0(B_1773) | ~v1_xboole_0(A_1774))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.11/1.82  tff(c_88, plain, (~m1_subset_1(k2_tarski('#skF_8', '#skF_9'), k1_zfmisc_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.11/1.82  tff(c_1526, plain, (~v1_xboole_0(k2_tarski('#skF_8', '#skF_9')) | ~v1_xboole_0(k1_zfmisc_1('#skF_7'))), inference(resolution, [status(thm)], [c_1518, c_88])).
% 4.11/1.82  tff(c_1527, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_1526])).
% 4.11/1.82  tff(c_44, plain, (![C_22, A_18]: (r2_hidden(C_22, k1_zfmisc_1(A_18)) | ~r1_tarski(C_22, A_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.11/1.82  tff(c_1560, plain, (![B_1786, A_1787]: (m1_subset_1(B_1786, A_1787) | ~r2_hidden(B_1786, A_1787) | v1_xboole_0(A_1787))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.11/1.82  tff(c_2271, plain, (![C_3105, A_3106]: (m1_subset_1(C_3105, k1_zfmisc_1(A_3106)) | v1_xboole_0(k1_zfmisc_1(A_3106)) | ~r1_tarski(C_3105, A_3106))), inference(resolution, [status(thm)], [c_44, c_1560])).
% 4.11/1.82  tff(c_2284, plain, (v1_xboole_0(k1_zfmisc_1('#skF_7')) | ~r1_tarski(k2_tarski('#skF_8', '#skF_9'), '#skF_7')), inference(resolution, [status(thm)], [c_2271, c_88])).
% 4.11/1.82  tff(c_2291, plain, (~r1_tarski(k2_tarski('#skF_8', '#skF_9'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_1527, c_2284])).
% 4.11/1.82  tff(c_2325, plain, (k4_xboole_0(k2_tarski('#skF_8', '#skF_9'), '#skF_7')!=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_2291])).
% 4.11/1.82  tff(c_2331, plain, (~r2_hidden('#skF_9', '#skF_7') | ~r2_hidden('#skF_8', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_60, c_2325])).
% 4.11/1.82  tff(c_2332, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(splitLeft, [status(thm)], [c_2331])).
% 4.11/1.82  tff(c_2335, plain, (k1_xboole_0='#skF_7' | ~m1_subset_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_1672, c_2332])).
% 4.11/1.82  tff(c_2341, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_2335])).
% 4.11/1.82  tff(c_2343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_2341])).
% 4.11/1.82  tff(c_2344, plain, (~r2_hidden('#skF_9', '#skF_7')), inference(splitRight, [status(thm)], [c_2331])).
% 4.11/1.82  tff(c_2357, plain, (k1_xboole_0='#skF_7' | ~m1_subset_1('#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_1672, c_2344])).
% 4.11/1.82  tff(c_2363, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_2357])).
% 4.11/1.82  tff(c_2365, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_2363])).
% 4.11/1.82  tff(c_2367, plain, (v1_xboole_0(k1_zfmisc_1('#skF_7'))), inference(splitRight, [status(thm)], [c_1526])).
% 4.11/1.82  tff(c_28, plain, (![A_12]: (k1_xboole_0=A_12 | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.11/1.82  tff(c_2371, plain, (k1_zfmisc_1('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_2367, c_28])).
% 4.11/1.82  tff(c_2381, plain, (![C_22]: (r2_hidden(C_22, k1_xboole_0) | ~r1_tarski(C_22, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2371, c_44])).
% 4.11/1.82  tff(c_2464, plain, (![C_3307]: (~r1_tarski(C_3307, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_2449, c_2381])).
% 4.11/1.82  tff(c_2470, plain, (![A_3308]: (k4_xboole_0(A_3308, '#skF_7')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_2464])).
% 4.11/1.82  tff(c_2484, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_26, c_2470])).
% 4.11/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.11/1.82  
% 4.11/1.82  Inference rules
% 4.11/1.82  ----------------------
% 4.11/1.82  #Ref     : 0
% 4.11/1.82  #Sup     : 363
% 4.11/1.82  #Fact    : 0
% 4.11/1.82  #Define  : 0
% 4.11/1.82  #Split   : 7
% 4.11/1.82  #Chain   : 0
% 4.11/1.82  #Close   : 0
% 4.11/1.82  
% 4.11/1.82  Ordering : KBO
% 4.11/1.82  
% 4.11/1.82  Simplification rules
% 4.11/1.82  ----------------------
% 4.11/1.82  #Subsume      : 59
% 4.11/1.82  #Demod        : 36
% 4.11/1.82  #Tautology    : 107
% 4.11/1.82  #SimpNegUnit  : 22
% 4.11/1.82  #BackRed      : 3
% 4.11/1.82  
% 4.11/1.82  #Partial instantiations: 2106
% 4.11/1.82  #Strategies tried      : 1
% 4.11/1.82  
% 4.11/1.82  Timing (in seconds)
% 4.11/1.82  ----------------------
% 4.11/1.82  Preprocessing        : 0.39
% 4.11/1.82  Parsing              : 0.19
% 4.11/1.82  CNF conversion       : 0.03
% 4.11/1.82  Main loop            : 0.55
% 4.11/1.82  Inferencing          : 0.25
% 4.11/1.82  Reduction            : 0.14
% 4.11/1.82  Demodulation         : 0.09
% 4.11/1.82  BG Simplification    : 0.03
% 4.11/1.82  Subsumption          : 0.09
% 4.11/1.82  Abstraction          : 0.02
% 4.11/1.82  MUC search           : 0.00
% 4.11/1.82  Cooper               : 0.00
% 4.11/1.82  Total                : 0.97
% 4.11/1.82  Index Insertion      : 0.00
% 4.11/1.82  Index Deletion       : 0.00
% 4.11/1.82  Index Matching       : 0.00
% 4.11/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
