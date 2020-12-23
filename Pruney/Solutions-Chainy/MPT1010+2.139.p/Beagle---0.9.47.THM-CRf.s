%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:24 EST 2020

% Result     : Theorem 7.62s
% Output     : CNFRefutation 7.97s
% Verified   : 
% Statistics : Number of formulae       :   69 (  75 expanded)
%              Number of leaves         :   42 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :   83 ( 113 expanded)
%              Number of equality atoms :   29 (  35 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_96,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_108,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_76,plain,(
    k1_funct_1('#skF_9','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_72,plain,(
    ! [A_51] :
      ( r2_hidden('#skF_5'(A_51),A_51)
      | k1_xboole_0 = A_51 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_155,plain,(
    ! [D_91,B_92,A_93] :
      ( r2_hidden(D_91,B_92)
      | ~ r2_hidden(D_91,k3_xboole_0(A_93,B_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_160,plain,(
    ! [A_93,B_92] :
      ( r2_hidden('#skF_5'(k3_xboole_0(A_93,B_92)),B_92)
      | k3_xboole_0(A_93,B_92) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_72,c_155])).

tff(c_38,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1011,plain,(
    ! [A_1993,C_1994,B_1995] :
      ( ~ r2_hidden(A_1993,C_1994)
      | ~ r2_hidden(A_1993,B_1995)
      | ~ r2_hidden(A_1993,k5_xboole_0(B_1995,C_1994)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1050,plain,(
    ! [A_2115,A_2116] :
      ( ~ r2_hidden(A_2115,k1_xboole_0)
      | ~ r2_hidden(A_2115,A_2116)
      | ~ r2_hidden(A_2115,A_2116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1011])).

tff(c_1078,plain,(
    ! [A_2235,A_2236] :
      ( ~ r2_hidden('#skF_5'(k3_xboole_0(A_2235,k1_xboole_0)),A_2236)
      | k3_xboole_0(A_2235,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_160,c_1050])).

tff(c_1107,plain,(
    ! [A_2235] : k3_xboole_0(A_2235,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_72,c_1078])).

tff(c_34,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_161,plain,(
    ! [A_94,B_95] : k4_xboole_0(A_94,k4_xboole_0(A_94,B_95)) = k3_xboole_0(A_94,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_176,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k3_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_161])).

tff(c_66,plain,(
    ! [B_50] : k4_xboole_0(k1_tarski(B_50),k1_tarski(B_50)) != k1_tarski(B_50) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_179,plain,(
    ! [B_50] : k3_xboole_0(k1_tarski(B_50),k1_xboole_0) != k1_tarski(B_50) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_66])).

tff(c_1113,plain,(
    ! [B_50] : k1_tarski(B_50) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1107,c_179])).

tff(c_84,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_82,plain,(
    v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_80,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k1_tarski('#skF_7')))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_78,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_12369,plain,(
    ! [D_46523,C_46524,B_46525,A_46526] :
      ( r2_hidden(k1_funct_1(D_46523,C_46524),B_46525)
      | k1_xboole_0 = B_46525
      | ~ r2_hidden(C_46524,A_46526)
      | ~ m1_subset_1(D_46523,k1_zfmisc_1(k2_zfmisc_1(A_46526,B_46525)))
      | ~ v1_funct_2(D_46523,A_46526,B_46525)
      | ~ v1_funct_1(D_46523) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_12825,plain,(
    ! [D_47928,B_47929] :
      ( r2_hidden(k1_funct_1(D_47928,'#skF_8'),B_47929)
      | k1_xboole_0 = B_47929
      | ~ m1_subset_1(D_47928,k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_47929)))
      | ~ v1_funct_2(D_47928,'#skF_6',B_47929)
      | ~ v1_funct_1(D_47928) ) ),
    inference(resolution,[status(thm)],[c_78,c_12369])).

tff(c_12840,plain,
    ( r2_hidden(k1_funct_1('#skF_9','#skF_8'),k1_tarski('#skF_7'))
    | k1_tarski('#skF_7') = k1_xboole_0
    | ~ v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7'))
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_80,c_12825])).

tff(c_12843,plain,
    ( r2_hidden(k1_funct_1('#skF_9','#skF_8'),k1_tarski('#skF_7'))
    | k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_12840])).

tff(c_12844,plain,(
    r2_hidden(k1_funct_1('#skF_9','#skF_8'),k1_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_1113,c_12843])).

tff(c_40,plain,(
    ! [C_20,A_16] :
      ( C_20 = A_16
      | ~ r2_hidden(C_20,k1_tarski(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12857,plain,(
    k1_funct_1('#skF_9','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_12844,c_40])).

tff(c_12928,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_12857])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:03:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.62/2.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.62/2.78  
% 7.62/2.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.62/2.78  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4
% 7.62/2.78  
% 7.62/2.78  %Foreground sorts:
% 7.62/2.78  
% 7.62/2.78  
% 7.62/2.78  %Background operators:
% 7.62/2.78  
% 7.62/2.78  
% 7.62/2.78  %Foreground operators:
% 7.62/2.78  tff('#skF_5', type, '#skF_5': $i > $i).
% 7.62/2.78  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.62/2.78  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.62/2.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.62/2.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.62/2.78  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.62/2.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.62/2.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.62/2.78  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.62/2.78  tff('#skF_7', type, '#skF_7': $i).
% 7.62/2.78  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.62/2.78  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.62/2.78  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.62/2.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.62/2.78  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.62/2.78  tff('#skF_6', type, '#skF_6': $i).
% 7.62/2.78  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.62/2.78  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.62/2.78  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.62/2.78  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.62/2.78  tff('#skF_9', type, '#skF_9': $i).
% 7.62/2.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.62/2.78  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.62/2.78  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.62/2.78  tff('#skF_8', type, '#skF_8': $i).
% 7.62/2.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.62/2.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.62/2.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.62/2.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.62/2.78  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.62/2.78  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.62/2.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.62/2.78  
% 7.97/2.79  tff(f_119, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 7.97/2.79  tff(f_96, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 7.97/2.79  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 7.97/2.79  tff(f_49, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 7.97/2.79  tff(f_41, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 7.97/2.79  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 7.97/2.79  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.97/2.79  tff(f_75, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 7.97/2.79  tff(f_108, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 7.97/2.79  tff(f_56, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 7.97/2.79  tff(c_76, plain, (k1_funct_1('#skF_9', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.97/2.79  tff(c_72, plain, (![A_51]: (r2_hidden('#skF_5'(A_51), A_51) | k1_xboole_0=A_51)), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.97/2.79  tff(c_155, plain, (![D_91, B_92, A_93]: (r2_hidden(D_91, B_92) | ~r2_hidden(D_91, k3_xboole_0(A_93, B_92)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.97/2.79  tff(c_160, plain, (![A_93, B_92]: (r2_hidden('#skF_5'(k3_xboole_0(A_93, B_92)), B_92) | k3_xboole_0(A_93, B_92)=k1_xboole_0)), inference(resolution, [status(thm)], [c_72, c_155])).
% 7.97/2.79  tff(c_38, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.97/2.79  tff(c_1011, plain, (![A_1993, C_1994, B_1995]: (~r2_hidden(A_1993, C_1994) | ~r2_hidden(A_1993, B_1995) | ~r2_hidden(A_1993, k5_xboole_0(B_1995, C_1994)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.97/2.79  tff(c_1050, plain, (![A_2115, A_2116]: (~r2_hidden(A_2115, k1_xboole_0) | ~r2_hidden(A_2115, A_2116) | ~r2_hidden(A_2115, A_2116))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1011])).
% 7.97/2.79  tff(c_1078, plain, (![A_2235, A_2236]: (~r2_hidden('#skF_5'(k3_xboole_0(A_2235, k1_xboole_0)), A_2236) | k3_xboole_0(A_2235, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_160, c_1050])).
% 7.97/2.79  tff(c_1107, plain, (![A_2235]: (k3_xboole_0(A_2235, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_72, c_1078])).
% 7.97/2.79  tff(c_34, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.97/2.79  tff(c_161, plain, (![A_94, B_95]: (k4_xboole_0(A_94, k4_xboole_0(A_94, B_95))=k3_xboole_0(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.97/2.79  tff(c_176, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k3_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_161])).
% 7.97/2.79  tff(c_66, plain, (![B_50]: (k4_xboole_0(k1_tarski(B_50), k1_tarski(B_50))!=k1_tarski(B_50))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.97/2.79  tff(c_179, plain, (![B_50]: (k3_xboole_0(k1_tarski(B_50), k1_xboole_0)!=k1_tarski(B_50))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_66])).
% 7.97/2.79  tff(c_1113, plain, (![B_50]: (k1_tarski(B_50)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1107, c_179])).
% 7.97/2.79  tff(c_84, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.97/2.79  tff(c_82, plain, (v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.97/2.79  tff(c_80, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k1_tarski('#skF_7'))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.97/2.79  tff(c_78, plain, (r2_hidden('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.97/2.79  tff(c_12369, plain, (![D_46523, C_46524, B_46525, A_46526]: (r2_hidden(k1_funct_1(D_46523, C_46524), B_46525) | k1_xboole_0=B_46525 | ~r2_hidden(C_46524, A_46526) | ~m1_subset_1(D_46523, k1_zfmisc_1(k2_zfmisc_1(A_46526, B_46525))) | ~v1_funct_2(D_46523, A_46526, B_46525) | ~v1_funct_1(D_46523))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.97/2.79  tff(c_12825, plain, (![D_47928, B_47929]: (r2_hidden(k1_funct_1(D_47928, '#skF_8'), B_47929) | k1_xboole_0=B_47929 | ~m1_subset_1(D_47928, k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_47929))) | ~v1_funct_2(D_47928, '#skF_6', B_47929) | ~v1_funct_1(D_47928))), inference(resolution, [status(thm)], [c_78, c_12369])).
% 7.97/2.79  tff(c_12840, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_8'), k1_tarski('#skF_7')) | k1_tarski('#skF_7')=k1_xboole_0 | ~v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7')) | ~v1_funct_1('#skF_9')), inference(resolution, [status(thm)], [c_80, c_12825])).
% 7.97/2.79  tff(c_12843, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_8'), k1_tarski('#skF_7')) | k1_tarski('#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_12840])).
% 7.97/2.79  tff(c_12844, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_8'), k1_tarski('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_1113, c_12843])).
% 7.97/2.79  tff(c_40, plain, (![C_20, A_16]: (C_20=A_16 | ~r2_hidden(C_20, k1_tarski(A_16)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.97/2.79  tff(c_12857, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_12844, c_40])).
% 7.97/2.79  tff(c_12928, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_12857])).
% 7.97/2.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.97/2.79  
% 7.97/2.79  Inference rules
% 7.97/2.79  ----------------------
% 7.97/2.79  #Ref     : 0
% 7.97/2.79  #Sup     : 1781
% 7.97/2.79  #Fact    : 3
% 7.97/2.79  #Define  : 0
% 7.97/2.79  #Split   : 8
% 7.97/2.79  #Chain   : 0
% 7.97/2.79  #Close   : 0
% 7.97/2.79  
% 7.97/2.79  Ordering : KBO
% 7.97/2.79  
% 7.97/2.79  Simplification rules
% 7.97/2.79  ----------------------
% 7.97/2.79  #Subsume      : 375
% 7.97/2.79  #Demod        : 593
% 7.97/2.79  #Tautology    : 593
% 7.97/2.79  #SimpNegUnit  : 262
% 7.97/2.79  #BackRed      : 6
% 7.97/2.79  
% 7.97/2.79  #Partial instantiations: 12216
% 7.97/2.79  #Strategies tried      : 1
% 7.97/2.79  
% 7.97/2.79  Timing (in seconds)
% 7.97/2.79  ----------------------
% 8.02/2.80  Preprocessing        : 0.37
% 8.02/2.80  Parsing              : 0.19
% 8.02/2.80  CNF conversion       : 0.03
% 8.02/2.80  Main loop            : 1.62
% 8.02/2.80  Inferencing          : 0.84
% 8.02/2.80  Reduction            : 0.38
% 8.02/2.80  Demodulation         : 0.25
% 8.02/2.80  BG Simplification    : 0.06
% 8.02/2.80  Subsumption          : 0.25
% 8.02/2.80  Abstraction          : 0.07
% 8.02/2.80  MUC search           : 0.00
% 8.02/2.80  Cooper               : 0.00
% 8.02/2.80  Total                : 2.01
% 8.02/2.80  Index Insertion      : 0.00
% 8.02/2.80  Index Deletion       : 0.00
% 8.02/2.80  Index Matching       : 0.00
% 8.02/2.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
