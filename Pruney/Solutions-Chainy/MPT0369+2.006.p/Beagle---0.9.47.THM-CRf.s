%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:51 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   72 (  86 expanded)
%              Number of leaves         :   32 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :   95 ( 150 expanded)
%              Number of equality atoms :   24 (  31 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( A != k1_xboole_0
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(A))
           => ! [C] :
                ( m1_subset_1(C,A)
               => ( ~ r2_hidden(C,B)
                 => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_80,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_61,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_63,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_69,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_46,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_48,plain,(
    m1_subset_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_116,plain,(
    ! [B_36,A_37] :
      ( v1_xboole_0(B_36)
      | ~ m1_subset_1(B_36,A_37)
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_128,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_116])).

tff(c_129,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( r2_hidden(B_13,A_12)
      | ~ m1_subset_1(B_13,A_12)
      | v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_46,plain,(
    ~ r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_50,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_42,plain,(
    ! [A_23] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_32,plain,(
    ! [A_14] : k1_subset_1(A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_34,plain,(
    ! [A_15] : k2_subset_1(A_15) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_38,plain,(
    ! [A_18] : k3_subset_1(A_18,k1_subset_1(A_18)) = k2_subset_1(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_53,plain,(
    ! [A_18] : k3_subset_1(A_18,k1_subset_1(A_18)) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_38])).

tff(c_54,plain,(
    ! [A_18] : k3_subset_1(A_18,k1_xboole_0) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_53])).

tff(c_22,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_601,plain,(
    ! [C_95,A_96,B_97] :
      ( r1_tarski(C_95,k3_subset_1(A_96,B_97))
      | ~ r1_tarski(B_97,k3_subset_1(A_96,C_95))
      | ~ m1_subset_1(C_95,k1_zfmisc_1(A_96))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_606,plain,(
    ! [C_95,A_96] :
      ( r1_tarski(C_95,k3_subset_1(A_96,k1_xboole_0))
      | ~ m1_subset_1(C_95,k1_zfmisc_1(A_96))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_96)) ) ),
    inference(resolution,[status(thm)],[c_22,c_601])).

tff(c_612,plain,(
    ! [C_98,A_99] :
      ( r1_tarski(C_98,A_99)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(A_99)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_54,c_606])).

tff(c_624,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_612])).

tff(c_20,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_630,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_624,c_20])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_640,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_630,c_2])).

tff(c_271,plain,(
    ! [A_53,B_54] :
      ( k4_xboole_0(A_53,B_54) = k3_subset_1(A_53,B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_283,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_271])).

tff(c_18,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_328,plain,(
    ! [A_58,C_59,B_60] :
      ( r2_hidden(A_58,C_59)
      | ~ r2_hidden(A_58,B_60)
      | r2_hidden(A_58,k5_xboole_0(B_60,C_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_522,plain,(
    ! [A_86,A_87,B_88] :
      ( r2_hidden(A_86,k3_xboole_0(A_87,B_88))
      | ~ r2_hidden(A_86,A_87)
      | r2_hidden(A_86,k4_xboole_0(A_87,B_88)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_328])).

tff(c_534,plain,(
    ! [A_86] :
      ( r2_hidden(A_86,k3_xboole_0('#skF_1','#skF_2'))
      | ~ r2_hidden(A_86,'#skF_1')
      | r2_hidden(A_86,k3_subset_1('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_522])).

tff(c_748,plain,(
    ! [A_105] :
      ( r2_hidden(A_105,'#skF_2')
      | ~ r2_hidden(A_105,'#skF_1')
      | r2_hidden(A_105,k3_subset_1('#skF_1','#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_640,c_534])).

tff(c_44,plain,(
    ~ r2_hidden('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_757,plain,
    ( r2_hidden('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_748,c_44])).

tff(c_764,plain,(
    ~ r2_hidden('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_757])).

tff(c_767,plain,
    ( ~ m1_subset_1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_764])).

tff(c_770,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_767])).

tff(c_772,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_770])).

tff(c_774,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_781,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_774,c_4])).

tff(c_785,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_781])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:05:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.45  
% 2.92/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.45  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.92/1.45  
% 2.92/1.45  %Foreground sorts:
% 2.92/1.45  
% 2.92/1.45  
% 2.92/1.45  %Background operators:
% 2.92/1.45  
% 2.92/1.45  
% 2.92/1.45  %Foreground operators:
% 2.92/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.92/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.92/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.92/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.92/1.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.92/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.92/1.45  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.92/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.92/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.92/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.92/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.92/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.92/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.92/1.45  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.92/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.92/1.45  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.92/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.92/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.92/1.45  
% 3.00/1.47  tff(f_95, negated_conjecture, ~(![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_subset_1)).
% 3.00/1.47  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.00/1.47  tff(f_80, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.00/1.47  tff(f_61, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 3.00/1.47  tff(f_63, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.00/1.47  tff(f_69, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 3.00/1.47  tff(f_46, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.00/1.47  tff(f_78, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_subset_1)).
% 3.00/1.47  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.00/1.47  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.00/1.47  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.00/1.47  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.00/1.47  tff(f_38, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.00/1.47  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.00/1.47  tff(c_52, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.00/1.47  tff(c_48, plain, (m1_subset_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.00/1.47  tff(c_116, plain, (![B_36, A_37]: (v1_xboole_0(B_36) | ~m1_subset_1(B_36, A_37) | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.00/1.47  tff(c_128, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_116])).
% 3.00/1.47  tff(c_129, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_128])).
% 3.00/1.47  tff(c_26, plain, (![B_13, A_12]: (r2_hidden(B_13, A_12) | ~m1_subset_1(B_13, A_12) | v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.00/1.47  tff(c_46, plain, (~r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.00/1.47  tff(c_50, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.00/1.47  tff(c_42, plain, (![A_23]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.00/1.47  tff(c_32, plain, (![A_14]: (k1_subset_1(A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.00/1.47  tff(c_34, plain, (![A_15]: (k2_subset_1(A_15)=A_15)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.00/1.47  tff(c_38, plain, (![A_18]: (k3_subset_1(A_18, k1_subset_1(A_18))=k2_subset_1(A_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.00/1.47  tff(c_53, plain, (![A_18]: (k3_subset_1(A_18, k1_subset_1(A_18))=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_38])).
% 3.00/1.47  tff(c_54, plain, (![A_18]: (k3_subset_1(A_18, k1_xboole_0)=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_53])).
% 3.00/1.47  tff(c_22, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.00/1.47  tff(c_601, plain, (![C_95, A_96, B_97]: (r1_tarski(C_95, k3_subset_1(A_96, B_97)) | ~r1_tarski(B_97, k3_subset_1(A_96, C_95)) | ~m1_subset_1(C_95, k1_zfmisc_1(A_96)) | ~m1_subset_1(B_97, k1_zfmisc_1(A_96)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.00/1.47  tff(c_606, plain, (![C_95, A_96]: (r1_tarski(C_95, k3_subset_1(A_96, k1_xboole_0)) | ~m1_subset_1(C_95, k1_zfmisc_1(A_96)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_96)))), inference(resolution, [status(thm)], [c_22, c_601])).
% 3.00/1.47  tff(c_612, plain, (![C_98, A_99]: (r1_tarski(C_98, A_99) | ~m1_subset_1(C_98, k1_zfmisc_1(A_99)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_54, c_606])).
% 3.00/1.47  tff(c_624, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_612])).
% 3.00/1.47  tff(c_20, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.00/1.47  tff(c_630, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_624, c_20])).
% 3.00/1.47  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.00/1.47  tff(c_640, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_630, c_2])).
% 3.00/1.47  tff(c_271, plain, (![A_53, B_54]: (k4_xboole_0(A_53, B_54)=k3_subset_1(A_53, B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.00/1.47  tff(c_283, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_50, c_271])).
% 3.00/1.47  tff(c_18, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.00/1.47  tff(c_328, plain, (![A_58, C_59, B_60]: (r2_hidden(A_58, C_59) | ~r2_hidden(A_58, B_60) | r2_hidden(A_58, k5_xboole_0(B_60, C_59)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.00/1.47  tff(c_522, plain, (![A_86, A_87, B_88]: (r2_hidden(A_86, k3_xboole_0(A_87, B_88)) | ~r2_hidden(A_86, A_87) | r2_hidden(A_86, k4_xboole_0(A_87, B_88)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_328])).
% 3.00/1.47  tff(c_534, plain, (![A_86]: (r2_hidden(A_86, k3_xboole_0('#skF_1', '#skF_2')) | ~r2_hidden(A_86, '#skF_1') | r2_hidden(A_86, k3_subset_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_283, c_522])).
% 3.00/1.47  tff(c_748, plain, (![A_105]: (r2_hidden(A_105, '#skF_2') | ~r2_hidden(A_105, '#skF_1') | r2_hidden(A_105, k3_subset_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_640, c_534])).
% 3.00/1.47  tff(c_44, plain, (~r2_hidden('#skF_3', k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.00/1.47  tff(c_757, plain, (r2_hidden('#skF_3', '#skF_2') | ~r2_hidden('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_748, c_44])).
% 3.00/1.47  tff(c_764, plain, (~r2_hidden('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_46, c_757])).
% 3.00/1.47  tff(c_767, plain, (~m1_subset_1('#skF_3', '#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_764])).
% 3.00/1.47  tff(c_770, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_767])).
% 3.00/1.47  tff(c_772, plain, $false, inference(negUnitSimplification, [status(thm)], [c_129, c_770])).
% 3.00/1.47  tff(c_774, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_128])).
% 3.00/1.47  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.00/1.47  tff(c_781, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_774, c_4])).
% 3.00/1.47  tff(c_785, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_781])).
% 3.00/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.47  
% 3.00/1.47  Inference rules
% 3.00/1.47  ----------------------
% 3.00/1.47  #Ref     : 0
% 3.00/1.47  #Sup     : 175
% 3.00/1.47  #Fact    : 0
% 3.00/1.47  #Define  : 0
% 3.00/1.47  #Split   : 8
% 3.00/1.47  #Chain   : 0
% 3.00/1.47  #Close   : 0
% 3.00/1.47  
% 3.00/1.47  Ordering : KBO
% 3.00/1.47  
% 3.00/1.47  Simplification rules
% 3.00/1.47  ----------------------
% 3.00/1.47  #Subsume      : 14
% 3.00/1.47  #Demod        : 63
% 3.00/1.47  #Tautology    : 99
% 3.00/1.47  #SimpNegUnit  : 6
% 3.00/1.47  #BackRed      : 4
% 3.00/1.47  
% 3.00/1.47  #Partial instantiations: 0
% 3.00/1.47  #Strategies tried      : 1
% 3.00/1.47  
% 3.00/1.47  Timing (in seconds)
% 3.00/1.47  ----------------------
% 3.00/1.47  Preprocessing        : 0.33
% 3.00/1.47  Parsing              : 0.18
% 3.00/1.47  CNF conversion       : 0.02
% 3.00/1.47  Main loop            : 0.35
% 3.00/1.47  Inferencing          : 0.13
% 3.00/1.47  Reduction            : 0.11
% 3.00/1.47  Demodulation         : 0.08
% 3.00/1.47  BG Simplification    : 0.02
% 3.00/1.47  Subsumption          : 0.06
% 3.00/1.47  Abstraction          : 0.01
% 3.00/1.47  MUC search           : 0.00
% 3.00/1.47  Cooper               : 0.00
% 3.00/1.47  Total                : 0.71
% 3.00/1.47  Index Insertion      : 0.00
% 3.00/1.48  Index Deletion       : 0.00
% 3.00/1.48  Index Matching       : 0.00
% 3.00/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
