%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:52 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   73 (  87 expanded)
%              Number of leaves         :   33 (  42 expanded)
%              Depth                    :   14
%              Number of atoms          :   96 ( 151 expanded)
%              Number of equality atoms :   24 (  31 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_46,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_61,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_63,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_69,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

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

tff(c_54,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_50,plain,(
    m1_subset_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_119,plain,(
    ! [B_38,A_39] :
      ( v1_xboole_0(B_38)
      | ~ m1_subset_1(B_38,A_39)
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_131,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_119])).

tff(c_132,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( r2_hidden(B_13,A_12)
      | ~ m1_subset_1(B_13,A_12)
      | v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_48,plain,(
    ~ r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_52,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_44,plain,(
    ! [A_23] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_22,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_32,plain,(
    ! [A_14] : k1_subset_1(A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_34,plain,(
    ! [A_15] : k2_subset_1(A_15) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_38,plain,(
    ! [A_18] : k3_subset_1(A_18,k1_subset_1(A_18)) = k2_subset_1(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_55,plain,(
    ! [A_18] : k3_subset_1(A_18,k1_subset_1(A_18)) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_38])).

tff(c_56,plain,(
    ! [A_18] : k3_subset_1(A_18,k1_xboole_0) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_55])).

tff(c_353,plain,(
    ! [B_75,A_76,C_77] :
      ( r1_tarski(B_75,k3_subset_1(A_76,C_77))
      | ~ r1_xboole_0(B_75,C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(A_76))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_359,plain,(
    ! [B_75,A_18] :
      ( r1_tarski(B_75,A_18)
      | ~ r1_xboole_0(B_75,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_18))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_353])).

tff(c_363,plain,(
    ! [B_78,A_79] :
      ( r1_tarski(B_78,A_79)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_79)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_22,c_359])).

tff(c_375,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_363])).

tff(c_20,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_380,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_375,c_20])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_395,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_380,c_2])).

tff(c_174,plain,(
    ! [A_49,B_50] :
      ( k4_xboole_0(A_49,B_50) = k3_subset_1(A_49,B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_186,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_174])).

tff(c_18,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_248,plain,(
    ! [A_57,C_58,B_59] :
      ( r2_hidden(A_57,C_58)
      | ~ r2_hidden(A_57,B_59)
      | r2_hidden(A_57,k5_xboole_0(B_59,C_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_684,plain,(
    ! [A_97,A_98,B_99] :
      ( r2_hidden(A_97,k3_xboole_0(A_98,B_99))
      | ~ r2_hidden(A_97,A_98)
      | r2_hidden(A_97,k4_xboole_0(A_98,B_99)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_248])).

tff(c_699,plain,(
    ! [A_97] :
      ( r2_hidden(A_97,k3_xboole_0('#skF_1','#skF_2'))
      | ~ r2_hidden(A_97,'#skF_1')
      | r2_hidden(A_97,k3_subset_1('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_684])).

tff(c_719,plain,(
    ! [A_104] :
      ( r2_hidden(A_104,'#skF_2')
      | ~ r2_hidden(A_104,'#skF_1')
      | r2_hidden(A_104,k3_subset_1('#skF_1','#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_699])).

tff(c_46,plain,(
    ~ r2_hidden('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_731,plain,
    ( r2_hidden('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_719,c_46])).

tff(c_739,plain,(
    ~ r2_hidden('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_731])).

tff(c_742,plain,
    ( ~ m1_subset_1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_739])).

tff(c_745,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_742])).

tff(c_747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_745])).

tff(c_749,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_756,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_749,c_4])).

tff(c_760,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_756])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:34:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.37  
% 2.67/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.37  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.67/1.37  
% 2.67/1.37  %Foreground sorts:
% 2.67/1.37  
% 2.67/1.37  
% 2.67/1.37  %Background operators:
% 2.67/1.37  
% 2.67/1.37  
% 2.67/1.37  %Foreground operators:
% 2.67/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.67/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.67/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.67/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.67/1.37  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.67/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.67/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.67/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.67/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.67/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.67/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.37  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.67/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.67/1.37  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.67/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.67/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.67/1.37  
% 2.67/1.39  tff(f_95, negated_conjecture, ~(![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_subset_1)).
% 2.67/1.39  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.67/1.39  tff(f_80, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.67/1.39  tff(f_46, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.67/1.39  tff(f_61, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.67/1.39  tff(f_63, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.67/1.39  tff(f_69, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.67/1.39  tff(f_78, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 2.67/1.39  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.67/1.39  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.67/1.39  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.67/1.39  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.67/1.39  tff(f_38, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.67/1.39  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.67/1.39  tff(c_54, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.67/1.39  tff(c_50, plain, (m1_subset_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.67/1.39  tff(c_119, plain, (![B_38, A_39]: (v1_xboole_0(B_38) | ~m1_subset_1(B_38, A_39) | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.67/1.39  tff(c_131, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_119])).
% 2.67/1.39  tff(c_132, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_131])).
% 2.67/1.39  tff(c_26, plain, (![B_13, A_12]: (r2_hidden(B_13, A_12) | ~m1_subset_1(B_13, A_12) | v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.67/1.39  tff(c_48, plain, (~r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.67/1.39  tff(c_52, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.67/1.39  tff(c_44, plain, (![A_23]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.67/1.39  tff(c_22, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.67/1.39  tff(c_32, plain, (![A_14]: (k1_subset_1(A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.67/1.39  tff(c_34, plain, (![A_15]: (k2_subset_1(A_15)=A_15)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.67/1.39  tff(c_38, plain, (![A_18]: (k3_subset_1(A_18, k1_subset_1(A_18))=k2_subset_1(A_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.67/1.39  tff(c_55, plain, (![A_18]: (k3_subset_1(A_18, k1_subset_1(A_18))=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_38])).
% 2.67/1.39  tff(c_56, plain, (![A_18]: (k3_subset_1(A_18, k1_xboole_0)=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_55])).
% 2.67/1.39  tff(c_353, plain, (![B_75, A_76, C_77]: (r1_tarski(B_75, k3_subset_1(A_76, C_77)) | ~r1_xboole_0(B_75, C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(A_76)) | ~m1_subset_1(B_75, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.67/1.39  tff(c_359, plain, (![B_75, A_18]: (r1_tarski(B_75, A_18) | ~r1_xboole_0(B_75, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_18)) | ~m1_subset_1(B_75, k1_zfmisc_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_353])).
% 2.67/1.39  tff(c_363, plain, (![B_78, A_79]: (r1_tarski(B_78, A_79) | ~m1_subset_1(B_78, k1_zfmisc_1(A_79)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_22, c_359])).
% 2.67/1.39  tff(c_375, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_52, c_363])).
% 2.67/1.39  tff(c_20, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.67/1.39  tff(c_380, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_375, c_20])).
% 2.67/1.39  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.67/1.39  tff(c_395, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_380, c_2])).
% 2.67/1.39  tff(c_174, plain, (![A_49, B_50]: (k4_xboole_0(A_49, B_50)=k3_subset_1(A_49, B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.67/1.39  tff(c_186, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_174])).
% 2.67/1.39  tff(c_18, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.67/1.39  tff(c_248, plain, (![A_57, C_58, B_59]: (r2_hidden(A_57, C_58) | ~r2_hidden(A_57, B_59) | r2_hidden(A_57, k5_xboole_0(B_59, C_58)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.67/1.39  tff(c_684, plain, (![A_97, A_98, B_99]: (r2_hidden(A_97, k3_xboole_0(A_98, B_99)) | ~r2_hidden(A_97, A_98) | r2_hidden(A_97, k4_xboole_0(A_98, B_99)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_248])).
% 2.67/1.39  tff(c_699, plain, (![A_97]: (r2_hidden(A_97, k3_xboole_0('#skF_1', '#skF_2')) | ~r2_hidden(A_97, '#skF_1') | r2_hidden(A_97, k3_subset_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_186, c_684])).
% 2.67/1.39  tff(c_719, plain, (![A_104]: (r2_hidden(A_104, '#skF_2') | ~r2_hidden(A_104, '#skF_1') | r2_hidden(A_104, k3_subset_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_395, c_699])).
% 2.67/1.39  tff(c_46, plain, (~r2_hidden('#skF_3', k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.67/1.39  tff(c_731, plain, (r2_hidden('#skF_3', '#skF_2') | ~r2_hidden('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_719, c_46])).
% 2.67/1.39  tff(c_739, plain, (~r2_hidden('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_48, c_731])).
% 2.67/1.39  tff(c_742, plain, (~m1_subset_1('#skF_3', '#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_739])).
% 2.67/1.39  tff(c_745, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_742])).
% 2.67/1.39  tff(c_747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_132, c_745])).
% 2.67/1.39  tff(c_749, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_131])).
% 2.67/1.39  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.67/1.39  tff(c_756, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_749, c_4])).
% 2.67/1.39  tff(c_760, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_756])).
% 2.67/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.39  
% 2.67/1.39  Inference rules
% 2.67/1.39  ----------------------
% 2.67/1.39  #Ref     : 0
% 2.67/1.39  #Sup     : 165
% 2.67/1.39  #Fact    : 0
% 2.67/1.39  #Define  : 0
% 2.67/1.39  #Split   : 7
% 2.67/1.39  #Chain   : 0
% 2.67/1.39  #Close   : 0
% 2.67/1.39  
% 2.67/1.39  Ordering : KBO
% 2.67/1.39  
% 2.67/1.39  Simplification rules
% 2.67/1.39  ----------------------
% 2.67/1.39  #Subsume      : 17
% 2.67/1.39  #Demod        : 46
% 2.67/1.39  #Tautology    : 84
% 2.67/1.39  #SimpNegUnit  : 6
% 2.67/1.39  #BackRed      : 3
% 2.67/1.39  
% 2.67/1.39  #Partial instantiations: 0
% 2.67/1.39  #Strategies tried      : 1
% 2.67/1.39  
% 2.67/1.39  Timing (in seconds)
% 2.67/1.39  ----------------------
% 2.67/1.39  Preprocessing        : 0.30
% 2.67/1.39  Parsing              : 0.16
% 2.67/1.39  CNF conversion       : 0.02
% 2.67/1.39  Main loop            : 0.32
% 2.67/1.39  Inferencing          : 0.12
% 2.67/1.39  Reduction            : 0.10
% 2.67/1.39  Demodulation         : 0.07
% 2.67/1.39  BG Simplification    : 0.02
% 2.67/1.39  Subsumption          : 0.06
% 2.67/1.39  Abstraction          : 0.01
% 2.67/1.39  MUC search           : 0.00
% 2.67/1.39  Cooper               : 0.00
% 2.67/1.39  Total                : 0.65
% 2.67/1.39  Index Insertion      : 0.00
% 2.67/1.39  Index Deletion       : 0.00
% 2.67/1.39  Index Matching       : 0.00
% 2.67/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
