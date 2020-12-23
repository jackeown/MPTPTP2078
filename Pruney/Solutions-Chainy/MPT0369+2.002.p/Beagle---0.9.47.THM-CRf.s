%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:51 EST 2020

% Result     : Theorem 11.11s
% Output     : CNFRefutation 11.26s
% Verified   : 
% Statistics : Number of formulae       :   74 (  89 expanded)
%              Number of leaves         :   33 (  43 expanded)
%              Depth                    :   14
%              Number of atoms          :   95 ( 156 expanded)
%              Number of equality atoms :   27 (  34 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( A != k1_xboole_0
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(A))
           => ! [C] :
                ( m1_subset_1(C,A)
               => ( ~ r2_hidden(C,B)
                 => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_50,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_54,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_83,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_42,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_62,plain,(
    m1_subset_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_276,plain,(
    ! [B_57,A_58] :
      ( v1_xboole_0(B_57)
      | ~ m1_subset_1(B_57,A_58)
      | ~ v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_288,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_276])).

tff(c_289,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_288])).

tff(c_48,plain,(
    ! [B_28,A_27] :
      ( r2_hidden(B_28,A_27)
      | ~ m1_subset_1(B_28,A_27)
      | v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_60,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_26,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_30,plain,(
    ! [A_19] : k5_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_629,plain,(
    ! [A_81,B_82,C_83] : k5_xboole_0(k5_xboole_0(A_81,B_82),C_83) = k5_xboole_0(A_81,k5_xboole_0(B_82,C_83)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_56,plain,(
    ! [A_31] : ~ v1_xboole_0(k1_zfmisc_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_302,plain,(
    ! [B_63,A_64] :
      ( r2_hidden(B_63,A_64)
      | ~ m1_subset_1(B_63,A_64)
      | v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_34,plain,(
    ! [C_26,A_22] :
      ( r1_tarski(C_26,A_22)
      | ~ r2_hidden(C_26,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_309,plain,(
    ! [B_63,A_22] :
      ( r1_tarski(B_63,A_22)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_22))
      | v1_xboole_0(k1_zfmisc_1(A_22)) ) ),
    inference(resolution,[status(thm)],[c_302,c_34])).

tff(c_454,plain,(
    ! [B_72,A_73] :
      ( r1_tarski(B_72,A_73)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_73)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_309])).

tff(c_467,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_454])).

tff(c_22,plain,(
    ! [A_11,B_12] :
      ( k2_xboole_0(A_11,B_12) = B_12
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_471,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_467,c_22])).

tff(c_32,plain,(
    ! [A_20,B_21] : k5_xboole_0(k5_xboole_0(A_20,B_21),k2_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_489,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4','#skF_3'),'#skF_3') = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_32])).

tff(c_646,plain,(
    k5_xboole_0('#skF_4',k5_xboole_0('#skF_3','#skF_3')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_629,c_489])).

tff(c_755,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_30,c_646])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_472,plain,(
    ! [A_74,B_75] :
      ( k4_xboole_0(A_74,B_75) = k3_subset_1(A_74,B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_485,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_472])).

tff(c_20,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1484,plain,(
    ! [A_98,C_99,B_100] :
      ( r2_hidden(A_98,C_99)
      | ~ r2_hidden(A_98,B_100)
      | r2_hidden(A_98,k5_xboole_0(B_100,C_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_22996,plain,(
    ! [A_289,A_290,B_291] :
      ( r2_hidden(A_289,k3_xboole_0(A_290,B_291))
      | ~ r2_hidden(A_289,A_290)
      | r2_hidden(A_289,k4_xboole_0(A_290,B_291)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1484])).

tff(c_23059,plain,(
    ! [A_289] :
      ( r2_hidden(A_289,k3_xboole_0('#skF_3','#skF_4'))
      | ~ r2_hidden(A_289,'#skF_3')
      | r2_hidden(A_289,k3_subset_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_485,c_22996])).

tff(c_23083,plain,(
    ! [A_292] :
      ( r2_hidden(A_292,'#skF_4')
      | ~ r2_hidden(A_292,'#skF_3')
      | r2_hidden(A_292,k3_subset_1('#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_755,c_2,c_23059])).

tff(c_58,plain,(
    ~ r2_hidden('#skF_5',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_23098,plain,
    ( r2_hidden('#skF_5','#skF_4')
    | ~ r2_hidden('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_23083,c_58])).

tff(c_23107,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_23098])).

tff(c_23110,plain,
    ( ~ m1_subset_1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_23107])).

tff(c_23113,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_23110])).

tff(c_23115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_289,c_23113])).

tff(c_23117,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_288])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_23124,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_23117,c_6])).

tff(c_23128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_23124])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:34:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.11/4.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.11/4.68  
% 11.11/4.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.11/4.68  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 11.11/4.68  
% 11.11/4.68  %Foreground sorts:
% 11.11/4.68  
% 11.11/4.68  
% 11.11/4.68  %Background operators:
% 11.11/4.68  
% 11.11/4.68  
% 11.11/4.68  %Foreground operators:
% 11.11/4.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.11/4.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.11/4.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.11/4.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.11/4.68  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.11/4.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.11/4.68  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 11.11/4.68  tff('#skF_5', type, '#skF_5': $i).
% 11.11/4.68  tff('#skF_3', type, '#skF_3': $i).
% 11.11/4.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.11/4.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.11/4.68  tff('#skF_4', type, '#skF_4': $i).
% 11.11/4.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.11/4.68  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.11/4.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.11/4.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.11/4.68  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.11/4.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.11/4.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.11/4.68  
% 11.26/4.70  tff(f_98, negated_conjecture, ~(![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_subset_1)).
% 11.26/4.70  tff(f_76, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 11.26/4.70  tff(f_50, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 11.26/4.70  tff(f_54, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 11.26/4.70  tff(f_52, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 11.26/4.70  tff(f_83, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 11.26/4.70  tff(f_63, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 11.26/4.70  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 11.26/4.70  tff(f_56, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 11.26/4.70  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.26/4.70  tff(f_80, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 11.26/4.70  tff(f_42, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.26/4.70  tff(f_40, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 11.26/4.70  tff(f_33, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 11.26/4.70  tff(c_66, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.26/4.70  tff(c_62, plain, (m1_subset_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.26/4.70  tff(c_276, plain, (![B_57, A_58]: (v1_xboole_0(B_57) | ~m1_subset_1(B_57, A_58) | ~v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.26/4.70  tff(c_288, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_276])).
% 11.26/4.70  tff(c_289, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_288])).
% 11.26/4.70  tff(c_48, plain, (![B_28, A_27]: (r2_hidden(B_28, A_27) | ~m1_subset_1(B_28, A_27) | v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.26/4.70  tff(c_60, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.26/4.70  tff(c_26, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.26/4.70  tff(c_30, plain, (![A_19]: (k5_xboole_0(A_19, A_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.26/4.70  tff(c_629, plain, (![A_81, B_82, C_83]: (k5_xboole_0(k5_xboole_0(A_81, B_82), C_83)=k5_xboole_0(A_81, k5_xboole_0(B_82, C_83)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.26/4.70  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.26/4.70  tff(c_56, plain, (![A_31]: (~v1_xboole_0(k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.26/4.70  tff(c_302, plain, (![B_63, A_64]: (r2_hidden(B_63, A_64) | ~m1_subset_1(B_63, A_64) | v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.26/4.70  tff(c_34, plain, (![C_26, A_22]: (r1_tarski(C_26, A_22) | ~r2_hidden(C_26, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.26/4.70  tff(c_309, plain, (![B_63, A_22]: (r1_tarski(B_63, A_22) | ~m1_subset_1(B_63, k1_zfmisc_1(A_22)) | v1_xboole_0(k1_zfmisc_1(A_22)))), inference(resolution, [status(thm)], [c_302, c_34])).
% 11.26/4.70  tff(c_454, plain, (![B_72, A_73]: (r1_tarski(B_72, A_73) | ~m1_subset_1(B_72, k1_zfmisc_1(A_73)))), inference(negUnitSimplification, [status(thm)], [c_56, c_309])).
% 11.26/4.70  tff(c_467, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_454])).
% 11.26/4.70  tff(c_22, plain, (![A_11, B_12]: (k2_xboole_0(A_11, B_12)=B_12 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.26/4.70  tff(c_471, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_467, c_22])).
% 11.26/4.70  tff(c_32, plain, (![A_20, B_21]: (k5_xboole_0(k5_xboole_0(A_20, B_21), k2_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.26/4.70  tff(c_489, plain, (k5_xboole_0(k5_xboole_0('#skF_4', '#skF_3'), '#skF_3')=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_471, c_32])).
% 11.26/4.70  tff(c_646, plain, (k5_xboole_0('#skF_4', k5_xboole_0('#skF_3', '#skF_3'))=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_629, c_489])).
% 11.26/4.70  tff(c_755, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_30, c_646])).
% 11.26/4.70  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.26/4.70  tff(c_472, plain, (![A_74, B_75]: (k4_xboole_0(A_74, B_75)=k3_subset_1(A_74, B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.26/4.70  tff(c_485, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_64, c_472])).
% 11.26/4.70  tff(c_20, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.26/4.70  tff(c_1484, plain, (![A_98, C_99, B_100]: (r2_hidden(A_98, C_99) | ~r2_hidden(A_98, B_100) | r2_hidden(A_98, k5_xboole_0(B_100, C_99)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.26/4.70  tff(c_22996, plain, (![A_289, A_290, B_291]: (r2_hidden(A_289, k3_xboole_0(A_290, B_291)) | ~r2_hidden(A_289, A_290) | r2_hidden(A_289, k4_xboole_0(A_290, B_291)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1484])).
% 11.26/4.70  tff(c_23059, plain, (![A_289]: (r2_hidden(A_289, k3_xboole_0('#skF_3', '#skF_4')) | ~r2_hidden(A_289, '#skF_3') | r2_hidden(A_289, k3_subset_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_485, c_22996])).
% 11.26/4.70  tff(c_23083, plain, (![A_292]: (r2_hidden(A_292, '#skF_4') | ~r2_hidden(A_292, '#skF_3') | r2_hidden(A_292, k3_subset_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_755, c_2, c_23059])).
% 11.26/4.70  tff(c_58, plain, (~r2_hidden('#skF_5', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.26/4.70  tff(c_23098, plain, (r2_hidden('#skF_5', '#skF_4') | ~r2_hidden('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_23083, c_58])).
% 11.26/4.70  tff(c_23107, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_23098])).
% 11.26/4.70  tff(c_23110, plain, (~m1_subset_1('#skF_5', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_23107])).
% 11.26/4.70  tff(c_23113, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_23110])).
% 11.26/4.70  tff(c_23115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_289, c_23113])).
% 11.26/4.70  tff(c_23117, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_288])).
% 11.26/4.70  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.26/4.70  tff(c_23124, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_23117, c_6])).
% 11.26/4.70  tff(c_23128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_23124])).
% 11.26/4.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.26/4.70  
% 11.26/4.70  Inference rules
% 11.26/4.70  ----------------------
% 11.26/4.70  #Ref     : 0
% 11.26/4.70  #Sup     : 5804
% 11.26/4.70  #Fact    : 0
% 11.26/4.70  #Define  : 0
% 11.26/4.70  #Split   : 6
% 11.26/4.70  #Chain   : 0
% 11.26/4.70  #Close   : 0
% 11.26/4.70  
% 11.26/4.70  Ordering : KBO
% 11.26/4.70  
% 11.26/4.70  Simplification rules
% 11.26/4.70  ----------------------
% 11.26/4.70  #Subsume      : 310
% 11.26/4.70  #Demod        : 6427
% 11.26/4.70  #Tautology    : 2878
% 11.26/4.70  #SimpNegUnit  : 8
% 11.26/4.70  #BackRed      : 3
% 11.26/4.70  
% 11.26/4.70  #Partial instantiations: 0
% 11.26/4.70  #Strategies tried      : 1
% 11.26/4.70  
% 11.26/4.70  Timing (in seconds)
% 11.26/4.70  ----------------------
% 11.26/4.70  Preprocessing        : 0.33
% 11.26/4.70  Parsing              : 0.17
% 11.26/4.70  CNF conversion       : 0.02
% 11.26/4.70  Main loop            : 3.60
% 11.26/4.70  Inferencing          : 0.62
% 11.26/4.70  Reduction            : 2.14
% 11.26/4.70  Demodulation         : 1.92
% 11.26/4.70  BG Simplification    : 0.10
% 11.26/4.70  Subsumption          : 0.54
% 11.26/4.70  Abstraction          : 0.12
% 11.26/4.70  MUC search           : 0.00
% 11.26/4.70  Cooper               : 0.00
% 11.26/4.70  Total                : 3.96
% 11.26/4.70  Index Insertion      : 0.00
% 11.26/4.70  Index Deletion       : 0.00
% 11.26/4.70  Index Matching       : 0.00
% 11.26/4.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
