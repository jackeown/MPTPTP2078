%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:46 EST 2020

% Result     : Theorem 5.06s
% Output     : CNFRefutation 5.06s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 116 expanded)
%              Number of leaves         :   30 (  54 expanded)
%              Depth                    :   13
%              Number of atoms          :   88 ( 220 expanded)
%              Number of equality atoms :   17 (  59 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k1_enumset1 > k7_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ~ ( B != k1_xboole_0
            & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_40,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_206,plain,(
    ! [A_67,C_68,B_69] :
      ( m1_subset_1(A_67,C_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(C_68))
      | ~ r2_hidden(A_67,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_212,plain,(
    ! [A_67] :
      ( m1_subset_1(A_67,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_67,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_206])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k3_subset_1(A_16,B_17),k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    ! [A_10] : k4_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_86,plain,(
    ! [B_44,A_45] :
      ( ~ r2_hidden(B_44,A_45)
      | k4_xboole_0(A_45,k1_tarski(B_44)) != A_45 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_91,plain,(
    ! [B_44] : ~ r2_hidden(B_44,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_86])).

tff(c_46,plain,(
    k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_213,plain,(
    ! [A_70,B_71] :
      ( m1_subset_1(k7_setfam_1(A_70,B_71),k1_zfmisc_1(k1_zfmisc_1(A_70)))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k1_zfmisc_1(A_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_220,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_213])).

tff(c_224,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_220])).

tff(c_231,plain,(
    ! [A_72] :
      ( m1_subset_1(A_72,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_72,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_206])).

tff(c_26,plain,(
    ! [A_18,B_19] :
      ( k3_subset_1(A_18,k3_subset_1(A_18,B_19)) = B_19
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_237,plain,(
    ! [A_72] :
      ( k3_subset_1('#skF_3',k3_subset_1('#skF_3',A_72)) = A_72
      | ~ r2_hidden(A_72,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_231,c_26])).

tff(c_482,plain,(
    ! [D_108,A_109,B_110] :
      ( r2_hidden(D_108,k7_setfam_1(A_109,B_110))
      | ~ r2_hidden(k3_subset_1(A_109,D_108),B_110)
      | ~ m1_subset_1(D_108,k1_zfmisc_1(A_109))
      | ~ m1_subset_1(k7_setfam_1(A_109,B_110),k1_zfmisc_1(k1_zfmisc_1(A_109)))
      | ~ m1_subset_1(B_110,k1_zfmisc_1(k1_zfmisc_1(A_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2611,plain,(
    ! [A_273,B_274] :
      ( r2_hidden(k3_subset_1('#skF_3',A_273),k7_setfam_1('#skF_3',B_274))
      | ~ r2_hidden(A_273,B_274)
      | ~ m1_subset_1(k3_subset_1('#skF_3',A_273),k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1(k7_setfam_1('#skF_3',B_274),k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
      | ~ m1_subset_1(B_274,k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
      | ~ r2_hidden(A_273,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_482])).

tff(c_2618,plain,(
    ! [A_273] :
      ( r2_hidden(k3_subset_1('#skF_3',A_273),k7_setfam_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_273,'#skF_4')
      | ~ m1_subset_1(k3_subset_1('#skF_3',A_273),k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
      | ~ r2_hidden(A_273,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2611])).

tff(c_2624,plain,(
    ! [A_273] :
      ( r2_hidden(k3_subset_1('#skF_3',A_273),k1_xboole_0)
      | ~ m1_subset_1(k3_subset_1('#skF_3',A_273),k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_273,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_224,c_46,c_2618])).

tff(c_2626,plain,(
    ! [A_275] :
      ( ~ m1_subset_1(k3_subset_1('#skF_3',A_275),k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_275,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_2624])).

tff(c_2649,plain,(
    ! [B_276] :
      ( ~ r2_hidden(B_276,'#skF_4')
      | ~ m1_subset_1(B_276,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_24,c_2626])).

tff(c_2683,plain,(
    ! [A_67] : ~ r2_hidden(A_67,'#skF_4') ),
    inference(resolution,[status(thm)],[c_212,c_2649])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2685,plain,(
    ! [A_277] : ~ r2_hidden(A_277,'#skF_4') ),
    inference(resolution,[status(thm)],[c_212,c_2649])).

tff(c_2713,plain,(
    ! [B_278] : r1_tarski('#skF_4',B_278) ),
    inference(resolution,[status(thm)],[c_6,c_2685])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = k1_xboole_0
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2753,plain,(
    ! [B_279] : k4_xboole_0('#skF_4',B_279) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2713,c_10])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,k1_tarski(B_15)) = A_14
      | r2_hidden(B_15,A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2771,plain,(
    ! [B_15] :
      ( k1_xboole_0 = '#skF_4'
      | r2_hidden(B_15,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2753,c_22])).

tff(c_2796,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2683,c_48,c_2771])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:52:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.06/2.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.06/2.23  
% 5.06/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.06/2.23  %$ r2_hidden > r1_tarski > m1_subset_1 > k1_enumset1 > k7_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 5.06/2.23  
% 5.06/2.23  %Foreground sorts:
% 5.06/2.23  
% 5.06/2.23  
% 5.06/2.23  %Background operators:
% 5.06/2.23  
% 5.06/2.23  
% 5.06/2.23  %Foreground operators:
% 5.06/2.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.06/2.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.06/2.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.06/2.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.06/2.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.06/2.23  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 5.06/2.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.06/2.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.06/2.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.06/2.23  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.06/2.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.06/2.23  tff('#skF_3', type, '#skF_3': $i).
% 5.06/2.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.06/2.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.06/2.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.06/2.23  tff('#skF_4', type, '#skF_4': $i).
% 5.06/2.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.06/2.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.06/2.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.06/2.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.06/2.23  
% 5.06/2.25  tff(f_90, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_setfam_1)).
% 5.06/2.25  tff(f_81, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 5.06/2.25  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 5.06/2.25  tff(f_40, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 5.06/2.25  tff(f_49, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 5.06/2.25  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 5.06/2.25  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 5.06/2.25  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_setfam_1)).
% 5.06/2.25  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.06/2.25  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.06/2.25  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.06/2.25  tff(c_206, plain, (![A_67, C_68, B_69]: (m1_subset_1(A_67, C_68) | ~m1_subset_1(B_69, k1_zfmisc_1(C_68)) | ~r2_hidden(A_67, B_69))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.06/2.25  tff(c_212, plain, (![A_67]: (m1_subset_1(A_67, k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_67, '#skF_4'))), inference(resolution, [status(thm)], [c_50, c_206])).
% 5.06/2.25  tff(c_24, plain, (![A_16, B_17]: (m1_subset_1(k3_subset_1(A_16, B_17), k1_zfmisc_1(A_16)) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.06/2.25  tff(c_14, plain, (![A_10]: (k4_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.06/2.25  tff(c_86, plain, (![B_44, A_45]: (~r2_hidden(B_44, A_45) | k4_xboole_0(A_45, k1_tarski(B_44))!=A_45)), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.06/2.25  tff(c_91, plain, (![B_44]: (~r2_hidden(B_44, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_86])).
% 5.06/2.25  tff(c_46, plain, (k7_setfam_1('#skF_3', '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.06/2.25  tff(c_213, plain, (![A_70, B_71]: (m1_subset_1(k7_setfam_1(A_70, B_71), k1_zfmisc_1(k1_zfmisc_1(A_70))) | ~m1_subset_1(B_71, k1_zfmisc_1(k1_zfmisc_1(A_70))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.06/2.25  tff(c_220, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_46, c_213])).
% 5.06/2.25  tff(c_224, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_220])).
% 5.06/2.25  tff(c_231, plain, (![A_72]: (m1_subset_1(A_72, k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_72, '#skF_4'))), inference(resolution, [status(thm)], [c_50, c_206])).
% 5.06/2.25  tff(c_26, plain, (![A_18, B_19]: (k3_subset_1(A_18, k3_subset_1(A_18, B_19))=B_19 | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.06/2.25  tff(c_237, plain, (![A_72]: (k3_subset_1('#skF_3', k3_subset_1('#skF_3', A_72))=A_72 | ~r2_hidden(A_72, '#skF_4'))), inference(resolution, [status(thm)], [c_231, c_26])).
% 5.06/2.25  tff(c_482, plain, (![D_108, A_109, B_110]: (r2_hidden(D_108, k7_setfam_1(A_109, B_110)) | ~r2_hidden(k3_subset_1(A_109, D_108), B_110) | ~m1_subset_1(D_108, k1_zfmisc_1(A_109)) | ~m1_subset_1(k7_setfam_1(A_109, B_110), k1_zfmisc_1(k1_zfmisc_1(A_109))) | ~m1_subset_1(B_110, k1_zfmisc_1(k1_zfmisc_1(A_109))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.06/2.25  tff(c_2611, plain, (![A_273, B_274]: (r2_hidden(k3_subset_1('#skF_3', A_273), k7_setfam_1('#skF_3', B_274)) | ~r2_hidden(A_273, B_274) | ~m1_subset_1(k3_subset_1('#skF_3', A_273), k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k7_setfam_1('#skF_3', B_274), k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) | ~m1_subset_1(B_274, k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) | ~r2_hidden(A_273, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_237, c_482])).
% 5.06/2.25  tff(c_2618, plain, (![A_273]: (r2_hidden(k3_subset_1('#skF_3', A_273), k7_setfam_1('#skF_3', '#skF_4')) | ~r2_hidden(A_273, '#skF_4') | ~m1_subset_1(k3_subset_1('#skF_3', A_273), k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) | ~r2_hidden(A_273, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_2611])).
% 5.06/2.25  tff(c_2624, plain, (![A_273]: (r2_hidden(k3_subset_1('#skF_3', A_273), k1_xboole_0) | ~m1_subset_1(k3_subset_1('#skF_3', A_273), k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_273, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_224, c_46, c_2618])).
% 5.06/2.25  tff(c_2626, plain, (![A_275]: (~m1_subset_1(k3_subset_1('#skF_3', A_275), k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_275, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_91, c_2624])).
% 5.06/2.25  tff(c_2649, plain, (![B_276]: (~r2_hidden(B_276, '#skF_4') | ~m1_subset_1(B_276, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_24, c_2626])).
% 5.06/2.25  tff(c_2683, plain, (![A_67]: (~r2_hidden(A_67, '#skF_4'))), inference(resolution, [status(thm)], [c_212, c_2649])).
% 5.06/2.25  tff(c_48, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.06/2.25  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.06/2.25  tff(c_2685, plain, (![A_277]: (~r2_hidden(A_277, '#skF_4'))), inference(resolution, [status(thm)], [c_212, c_2649])).
% 5.06/2.25  tff(c_2713, plain, (![B_278]: (r1_tarski('#skF_4', B_278))), inference(resolution, [status(thm)], [c_6, c_2685])).
% 5.06/2.25  tff(c_10, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=k1_xboole_0 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.06/2.25  tff(c_2753, plain, (![B_279]: (k4_xboole_0('#skF_4', B_279)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2713, c_10])).
% 5.06/2.25  tff(c_22, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k1_tarski(B_15))=A_14 | r2_hidden(B_15, A_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.06/2.25  tff(c_2771, plain, (![B_15]: (k1_xboole_0='#skF_4' | r2_hidden(B_15, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2753, c_22])).
% 5.06/2.25  tff(c_2796, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2683, c_48, c_2771])).
% 5.06/2.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.06/2.25  
% 5.06/2.25  Inference rules
% 5.06/2.25  ----------------------
% 5.06/2.25  #Ref     : 0
% 5.06/2.25  #Sup     : 622
% 5.06/2.25  #Fact    : 0
% 5.06/2.25  #Define  : 0
% 5.06/2.25  #Split   : 11
% 5.06/2.25  #Chain   : 0
% 5.06/2.25  #Close   : 0
% 5.06/2.25  
% 5.06/2.25  Ordering : KBO
% 5.06/2.25  
% 5.06/2.25  Simplification rules
% 5.06/2.25  ----------------------
% 5.06/2.25  #Subsume      : 121
% 5.06/2.25  #Demod        : 184
% 5.06/2.25  #Tautology    : 171
% 5.06/2.25  #SimpNegUnit  : 14
% 5.06/2.25  #BackRed      : 23
% 5.06/2.25  
% 5.06/2.25  #Partial instantiations: 0
% 5.06/2.25  #Strategies tried      : 1
% 5.06/2.25  
% 5.06/2.25  Timing (in seconds)
% 5.06/2.25  ----------------------
% 5.06/2.25  Preprocessing        : 0.51
% 5.06/2.25  Parsing              : 0.26
% 5.06/2.25  CNF conversion       : 0.04
% 5.06/2.25  Main loop            : 0.81
% 5.06/2.25  Inferencing          : 0.28
% 5.06/2.25  Reduction            : 0.23
% 5.06/2.25  Demodulation         : 0.15
% 5.06/2.25  BG Simplification    : 0.04
% 5.06/2.25  Subsumption          : 0.21
% 5.06/2.25  Abstraction          : 0.04
% 5.06/2.25  MUC search           : 0.00
% 5.06/2.25  Cooper               : 0.00
% 5.06/2.25  Total                : 1.36
% 5.06/2.25  Index Insertion      : 0.00
% 5.06/2.25  Index Deletion       : 0.00
% 5.06/2.25  Index Matching       : 0.00
% 5.06/2.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
