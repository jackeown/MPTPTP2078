%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:51 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   79 (  95 expanded)
%              Number of leaves         :   34 (  44 expanded)
%              Depth                    :   16
%              Number of atoms          :  101 ( 158 expanded)
%              Number of equality atoms :   30 (  39 expanded)
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

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( A != k1_xboole_0
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(A))
           => ! [C] :
                ( m1_subset_1(C,A)
               => ( ~ r2_hidden(C,B)
                 => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_63,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_69,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_46,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_61,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_75,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_86,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_54,plain,(
    m1_subset_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_130,plain,(
    ! [B_44,A_45] :
      ( v1_xboole_0(B_44)
      | ~ m1_subset_1(B_44,A_45)
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_150,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_130])).

tff(c_172,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( r2_hidden(B_13,A_12)
      | ~ m1_subset_1(B_13,A_12)
      | v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_52,plain,(
    ~ r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_56,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_308,plain,(
    ! [A_59,B_60] :
      ( k4_xboole_0(A_59,B_60) = k3_subset_1(A_59,B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_323,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_308])).

tff(c_34,plain,(
    ! [A_15] : k2_subset_1(A_15) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_38,plain,(
    ! [A_18] : m1_subset_1(k2_subset_1(A_18),k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_60,plain,(
    ! [A_18] : m1_subset_1(A_18,k1_zfmisc_1(A_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_38])).

tff(c_22,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_32,plain,(
    ! [A_14] : k1_subset_1(A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_42,plain,(
    ! [A_21] : k3_subset_1(A_21,k1_subset_1(A_21)) = k2_subset_1(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_59,plain,(
    ! [A_21] : k3_subset_1(A_21,k1_subset_1(A_21)) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_42])).

tff(c_61,plain,(
    ! [A_21] : k3_subset_1(A_21,k1_xboole_0) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_59])).

tff(c_48,plain,(
    ! [A_26] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_418,plain,(
    ! [A_65,B_66] :
      ( k3_subset_1(A_65,k3_subset_1(A_65,B_66)) = B_66
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_427,plain,(
    ! [A_26] : k3_subset_1(A_26,k3_subset_1(A_26,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_418])).

tff(c_432,plain,(
    ! [A_26] : k3_subset_1(A_26,A_26) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_427])).

tff(c_736,plain,(
    ! [B_97,C_98,A_99] :
      ( r1_tarski(B_97,C_98)
      | ~ r1_tarski(k3_subset_1(A_99,C_98),k3_subset_1(A_99,B_97))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(A_99))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_752,plain,(
    ! [B_97,A_26] :
      ( r1_tarski(B_97,A_26)
      | ~ r1_tarski(k1_xboole_0,k3_subset_1(A_26,B_97))
      | ~ m1_subset_1(A_26,k1_zfmisc_1(A_26))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_736])).

tff(c_774,plain,(
    ! [B_100,A_101] :
      ( r1_tarski(B_100,A_101)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_101)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_22,c_752])).

tff(c_789,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_774])).

tff(c_20,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_797,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_789,c_20])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_227,plain,(
    ! [A_51,B_52] : k5_xboole_0(A_51,k3_xboole_0(A_51,B_52)) = k4_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_242,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_227])).

tff(c_801,plain,(
    k5_xboole_0('#skF_1','#skF_2') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_797,c_242])).

tff(c_819,plain,(
    k5_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_801])).

tff(c_16,plain,(
    ! [A_4,C_6,B_5] :
      ( r2_hidden(A_4,C_6)
      | ~ r2_hidden(A_4,B_5)
      | r2_hidden(A_4,k5_xboole_0(B_5,C_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1049,plain,(
    ! [A_118] :
      ( r2_hidden(A_118,'#skF_2')
      | ~ r2_hidden(A_118,'#skF_1')
      | r2_hidden(A_118,k3_subset_1('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_819,c_16])).

tff(c_50,plain,(
    ~ r2_hidden('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1061,plain,
    ( r2_hidden('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_1049,c_50])).

tff(c_1069,plain,(
    ~ r2_hidden('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1061])).

tff(c_1072,plain,
    ( ~ m1_subset_1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_1069])).

tff(c_1075,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1072])).

tff(c_1077,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_1075])).

tff(c_1079,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1086,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1079,c_4])).

tff(c_1090,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1086])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:08:19 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.42  
% 2.96/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.42  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.96/1.42  
% 2.96/1.42  %Foreground sorts:
% 2.96/1.42  
% 2.96/1.42  
% 2.96/1.42  %Background operators:
% 2.96/1.42  
% 2.96/1.42  
% 2.96/1.42  %Foreground operators:
% 2.96/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.96/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.96/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.96/1.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.96/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.96/1.42  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.96/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.96/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.96/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.96/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.96/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.42  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.96/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.96/1.42  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.96/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.96/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.96/1.42  
% 2.96/1.44  tff(f_101, negated_conjecture, ~(![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_subset_1)).
% 2.96/1.44  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.96/1.44  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.96/1.44  tff(f_63, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.96/1.44  tff(f_69, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.96/1.44  tff(f_46, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.96/1.44  tff(f_61, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.96/1.44  tff(f_75, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 2.96/1.44  tff(f_86, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.96/1.44  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.96/1.44  tff(f_84, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 2.96/1.44  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.96/1.44  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.96/1.44  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.96/1.44  tff(f_38, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.96/1.44  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.96/1.44  tff(c_58, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.96/1.44  tff(c_54, plain, (m1_subset_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.96/1.44  tff(c_130, plain, (![B_44, A_45]: (v1_xboole_0(B_44) | ~m1_subset_1(B_44, A_45) | ~v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.96/1.44  tff(c_150, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_54, c_130])).
% 2.96/1.44  tff(c_172, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_150])).
% 2.96/1.44  tff(c_26, plain, (![B_13, A_12]: (r2_hidden(B_13, A_12) | ~m1_subset_1(B_13, A_12) | v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.96/1.44  tff(c_52, plain, (~r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.96/1.44  tff(c_56, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.96/1.44  tff(c_308, plain, (![A_59, B_60]: (k4_xboole_0(A_59, B_60)=k3_subset_1(A_59, B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.96/1.44  tff(c_323, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_308])).
% 2.96/1.44  tff(c_34, plain, (![A_15]: (k2_subset_1(A_15)=A_15)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.96/1.44  tff(c_38, plain, (![A_18]: (m1_subset_1(k2_subset_1(A_18), k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.96/1.44  tff(c_60, plain, (![A_18]: (m1_subset_1(A_18, k1_zfmisc_1(A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_38])).
% 2.96/1.44  tff(c_22, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.96/1.44  tff(c_32, plain, (![A_14]: (k1_subset_1(A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.96/1.44  tff(c_42, plain, (![A_21]: (k3_subset_1(A_21, k1_subset_1(A_21))=k2_subset_1(A_21))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.96/1.44  tff(c_59, plain, (![A_21]: (k3_subset_1(A_21, k1_subset_1(A_21))=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_42])).
% 2.96/1.44  tff(c_61, plain, (![A_21]: (k3_subset_1(A_21, k1_xboole_0)=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_59])).
% 2.96/1.44  tff(c_48, plain, (![A_26]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.96/1.44  tff(c_418, plain, (![A_65, B_66]: (k3_subset_1(A_65, k3_subset_1(A_65, B_66))=B_66 | ~m1_subset_1(B_66, k1_zfmisc_1(A_65)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.96/1.44  tff(c_427, plain, (![A_26]: (k3_subset_1(A_26, k3_subset_1(A_26, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_418])).
% 2.96/1.44  tff(c_432, plain, (![A_26]: (k3_subset_1(A_26, A_26)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_61, c_427])).
% 2.96/1.44  tff(c_736, plain, (![B_97, C_98, A_99]: (r1_tarski(B_97, C_98) | ~r1_tarski(k3_subset_1(A_99, C_98), k3_subset_1(A_99, B_97)) | ~m1_subset_1(C_98, k1_zfmisc_1(A_99)) | ~m1_subset_1(B_97, k1_zfmisc_1(A_99)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.96/1.44  tff(c_752, plain, (![B_97, A_26]: (r1_tarski(B_97, A_26) | ~r1_tarski(k1_xboole_0, k3_subset_1(A_26, B_97)) | ~m1_subset_1(A_26, k1_zfmisc_1(A_26)) | ~m1_subset_1(B_97, k1_zfmisc_1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_432, c_736])).
% 2.96/1.44  tff(c_774, plain, (![B_100, A_101]: (r1_tarski(B_100, A_101) | ~m1_subset_1(B_100, k1_zfmisc_1(A_101)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_22, c_752])).
% 2.96/1.44  tff(c_789, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_56, c_774])).
% 2.96/1.44  tff(c_20, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.96/1.44  tff(c_797, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_789, c_20])).
% 2.96/1.44  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.96/1.44  tff(c_227, plain, (![A_51, B_52]: (k5_xboole_0(A_51, k3_xboole_0(A_51, B_52))=k4_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.96/1.44  tff(c_242, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_227])).
% 2.96/1.44  tff(c_801, plain, (k5_xboole_0('#skF_1', '#skF_2')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_797, c_242])).
% 2.96/1.44  tff(c_819, plain, (k5_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_323, c_801])).
% 2.96/1.44  tff(c_16, plain, (![A_4, C_6, B_5]: (r2_hidden(A_4, C_6) | ~r2_hidden(A_4, B_5) | r2_hidden(A_4, k5_xboole_0(B_5, C_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.96/1.44  tff(c_1049, plain, (![A_118]: (r2_hidden(A_118, '#skF_2') | ~r2_hidden(A_118, '#skF_1') | r2_hidden(A_118, k3_subset_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_819, c_16])).
% 2.96/1.44  tff(c_50, plain, (~r2_hidden('#skF_3', k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.96/1.44  tff(c_1061, plain, (r2_hidden('#skF_3', '#skF_2') | ~r2_hidden('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_1049, c_50])).
% 2.96/1.44  tff(c_1069, plain, (~r2_hidden('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_1061])).
% 2.96/1.44  tff(c_1072, plain, (~m1_subset_1('#skF_3', '#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_1069])).
% 2.96/1.44  tff(c_1075, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1072])).
% 2.96/1.44  tff(c_1077, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172, c_1075])).
% 2.96/1.44  tff(c_1079, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_150])).
% 2.96/1.44  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.96/1.44  tff(c_1086, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_1079, c_4])).
% 2.96/1.44  tff(c_1090, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1086])).
% 2.96/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.44  
% 2.96/1.44  Inference rules
% 2.96/1.44  ----------------------
% 2.96/1.44  #Ref     : 0
% 2.96/1.44  #Sup     : 244
% 2.96/1.44  #Fact    : 0
% 2.96/1.44  #Define  : 0
% 2.96/1.44  #Split   : 10
% 2.96/1.44  #Chain   : 0
% 2.96/1.44  #Close   : 0
% 2.96/1.44  
% 2.96/1.44  Ordering : KBO
% 2.96/1.44  
% 2.96/1.44  Simplification rules
% 2.96/1.44  ----------------------
% 2.96/1.44  #Subsume      : 45
% 2.96/1.44  #Demod        : 85
% 2.96/1.44  #Tautology    : 134
% 2.96/1.44  #SimpNegUnit  : 10
% 2.96/1.44  #BackRed      : 3
% 2.96/1.44  
% 2.96/1.44  #Partial instantiations: 0
% 2.96/1.44  #Strategies tried      : 1
% 2.96/1.44  
% 2.96/1.44  Timing (in seconds)
% 2.96/1.44  ----------------------
% 2.96/1.44  Preprocessing        : 0.31
% 2.96/1.44  Parsing              : 0.17
% 2.96/1.44  CNF conversion       : 0.02
% 2.96/1.44  Main loop            : 0.38
% 2.96/1.44  Inferencing          : 0.14
% 2.96/1.44  Reduction            : 0.13
% 2.96/1.44  Demodulation         : 0.09
% 2.96/1.44  BG Simplification    : 0.02
% 2.96/1.44  Subsumption          : 0.07
% 2.96/1.44  Abstraction          : 0.02
% 2.96/1.44  MUC search           : 0.00
% 2.96/1.44  Cooper               : 0.00
% 2.96/1.44  Total                : 0.72
% 2.96/1.44  Index Insertion      : 0.00
% 2.96/1.44  Index Deletion       : 0.00
% 2.96/1.44  Index Matching       : 0.00
% 2.96/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
