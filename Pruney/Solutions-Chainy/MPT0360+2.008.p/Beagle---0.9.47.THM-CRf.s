%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:19 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 195 expanded)
%              Number of leaves         :   33 (  79 expanded)
%              Depth                    :   18
%              Number of atoms          :   89 ( 300 expanded)
%              Number of equality atoms :   28 (  88 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_64,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_61,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_59,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_50,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_122,plain,(
    ! [A_45,B_46] :
      ( k3_xboole_0(A_45,B_46) = A_45
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_130,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_122])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_36,plain,(
    ! [A_22] : ~ v1_xboole_0(k1_zfmisc_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_245,plain,(
    ! [B_57,A_58] :
      ( r2_hidden(B_57,A_58)
      | ~ m1_subset_1(B_57,A_58)
      | v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    ! [C_16,A_12] :
      ( r1_tarski(C_16,A_12)
      | ~ r2_hidden(C_16,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_249,plain,(
    ! [B_57,A_12] :
      ( r1_tarski(B_57,A_12)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_12))
      | v1_xboole_0(k1_zfmisc_1(A_12)) ) ),
    inference(resolution,[status(thm)],[c_245,c_12])).

tff(c_258,plain,(
    ! [B_59,A_60] :
      ( r1_tarski(B_59,A_60)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_249])).

tff(c_293,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_258])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_297,plain,(
    k3_xboole_0('#skF_5','#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_293,c_8])).

tff(c_547,plain,(
    ! [A_72,B_73,C_74] : k3_xboole_0(k3_xboole_0(A_72,B_73),C_74) = k3_xboole_0(A_72,k3_xboole_0(B_73,C_74)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_169,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k4_xboole_0(A_51,B_52)) = k3_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_38,plain,(
    ! [A_23,B_24] : k6_subset_1(A_23,B_24) = k4_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_34,plain,(
    ! [A_20,B_21] : m1_subset_1(k6_subset_1(A_20,B_21),k1_zfmisc_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_53,plain,(
    ! [A_20,B_21] : m1_subset_1(k4_xboole_0(A_20,B_21),k1_zfmisc_1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34])).

tff(c_200,plain,(
    ! [A_53,B_54] : m1_subset_1(k3_xboole_0(A_53,B_54),k1_zfmisc_1(A_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_53])).

tff(c_212,plain,(
    ! [B_2,A_1] : m1_subset_1(k3_xboole_0(B_2,A_1),k1_zfmisc_1(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_200])).

tff(c_288,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(resolution,[status(thm)],[c_212,c_258])).

tff(c_617,plain,(
    ! [A_75,B_76,C_77] : r1_tarski(k3_xboole_0(A_75,k3_xboole_0(B_76,C_77)),C_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_547,c_288])).

tff(c_666,plain,(
    ! [A_78] : r1_tarski(k3_xboole_0(A_78,'#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_617])).

tff(c_679,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_666])).

tff(c_694,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_679,c_8])).

tff(c_730,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_694,c_212])).

tff(c_48,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1849,plain,(
    ! [C_120,A_121,B_122] :
      ( r1_tarski(C_120,k3_subset_1(A_121,B_122))
      | ~ r1_tarski(B_122,k3_subset_1(A_121,C_120))
      | ~ m1_subset_1(C_120,k1_zfmisc_1(A_121))
      | ~ m1_subset_1(B_122,k1_zfmisc_1(A_121)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1875,plain,
    ( r1_tarski('#skF_5',k3_subset_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_1849])).

tff(c_1891,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_730,c_52,c_1875])).

tff(c_1900,plain,(
    k3_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_4')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1891,c_8])).

tff(c_598,plain,(
    ! [C_74] : k3_xboole_0('#skF_4',k3_xboole_0('#skF_5',C_74)) = k3_xboole_0('#skF_4',C_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_547])).

tff(c_1915,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1900,c_598])).

tff(c_1947,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_1915])).

tff(c_1986,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1947,c_288])).

tff(c_32,plain,(
    ! [A_19] : k1_subset_1(A_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_44,plain,(
    ! [A_29,B_30] :
      ( k1_subset_1(A_29) = B_30
      | ~ r1_tarski(B_30,k3_subset_1(A_29,B_30))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_55,plain,(
    ! [B_30,A_29] :
      ( k1_xboole_0 = B_30
      | ~ r1_tarski(B_30,k3_subset_1(A_29,B_30))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_44])).

tff(c_2021,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1986,c_55])).

tff(c_2030,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_730,c_2021])).

tff(c_2032,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_2030])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:34:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.48/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.81/1.63  
% 3.81/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.81/1.63  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.81/1.63  
% 3.81/1.63  %Foreground sorts:
% 3.81/1.63  
% 3.81/1.63  
% 3.81/1.63  %Background operators:
% 3.81/1.63  
% 3.81/1.63  
% 3.81/1.63  %Foreground operators:
% 3.81/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.81/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.81/1.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.81/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.81/1.63  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.81/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.81/1.63  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.81/1.63  tff('#skF_5', type, '#skF_5': $i).
% 3.81/1.63  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.81/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.81/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.81/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.81/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.81/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.81/1.63  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.81/1.63  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.81/1.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.81/1.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.81/1.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.81/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.81/1.63  
% 3.81/1.65  tff(f_90, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_subset_1)).
% 3.81/1.65  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.81/1.65  tff(f_64, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.81/1.65  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.81/1.65  tff(f_44, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.81/1.65  tff(f_31, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 3.81/1.65  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.81/1.65  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.81/1.65  tff(f_66, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.81/1.65  tff(f_61, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 3.81/1.65  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_subset_1)).
% 3.81/1.65  tff(f_59, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 3.81/1.65  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 3.81/1.65  tff(c_46, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.81/1.65  tff(c_50, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.81/1.65  tff(c_122, plain, (![A_45, B_46]: (k3_xboole_0(A_45, B_46)=A_45 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.81/1.65  tff(c_130, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_50, c_122])).
% 3.81/1.65  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.81/1.65  tff(c_36, plain, (![A_22]: (~v1_xboole_0(k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.81/1.65  tff(c_245, plain, (![B_57, A_58]: (r2_hidden(B_57, A_58) | ~m1_subset_1(B_57, A_58) | v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.81/1.65  tff(c_12, plain, (![C_16, A_12]: (r1_tarski(C_16, A_12) | ~r2_hidden(C_16, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.81/1.65  tff(c_249, plain, (![B_57, A_12]: (r1_tarski(B_57, A_12) | ~m1_subset_1(B_57, k1_zfmisc_1(A_12)) | v1_xboole_0(k1_zfmisc_1(A_12)))), inference(resolution, [status(thm)], [c_245, c_12])).
% 3.81/1.65  tff(c_258, plain, (![B_59, A_60]: (r1_tarski(B_59, A_60) | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)))), inference(negUnitSimplification, [status(thm)], [c_36, c_249])).
% 3.81/1.65  tff(c_293, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_258])).
% 3.81/1.65  tff(c_8, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.81/1.65  tff(c_297, plain, (k3_xboole_0('#skF_5', '#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_293, c_8])).
% 3.81/1.65  tff(c_547, plain, (![A_72, B_73, C_74]: (k3_xboole_0(k3_xboole_0(A_72, B_73), C_74)=k3_xboole_0(A_72, k3_xboole_0(B_73, C_74)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.81/1.65  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.81/1.65  tff(c_169, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k4_xboole_0(A_51, B_52))=k3_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.81/1.65  tff(c_38, plain, (![A_23, B_24]: (k6_subset_1(A_23, B_24)=k4_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.81/1.65  tff(c_34, plain, (![A_20, B_21]: (m1_subset_1(k6_subset_1(A_20, B_21), k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.81/1.65  tff(c_53, plain, (![A_20, B_21]: (m1_subset_1(k4_xboole_0(A_20, B_21), k1_zfmisc_1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34])).
% 3.81/1.65  tff(c_200, plain, (![A_53, B_54]: (m1_subset_1(k3_xboole_0(A_53, B_54), k1_zfmisc_1(A_53)))), inference(superposition, [status(thm), theory('equality')], [c_169, c_53])).
% 3.81/1.65  tff(c_212, plain, (![B_2, A_1]: (m1_subset_1(k3_xboole_0(B_2, A_1), k1_zfmisc_1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_200])).
% 3.81/1.65  tff(c_288, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(resolution, [status(thm)], [c_212, c_258])).
% 3.81/1.65  tff(c_617, plain, (![A_75, B_76, C_77]: (r1_tarski(k3_xboole_0(A_75, k3_xboole_0(B_76, C_77)), C_77))), inference(superposition, [status(thm), theory('equality')], [c_547, c_288])).
% 3.81/1.65  tff(c_666, plain, (![A_78]: (r1_tarski(k3_xboole_0(A_78, '#skF_5'), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_297, c_617])).
% 3.81/1.65  tff(c_679, plain, (r1_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_130, c_666])).
% 3.81/1.65  tff(c_694, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_679, c_8])).
% 3.81/1.65  tff(c_730, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_694, c_212])).
% 3.81/1.65  tff(c_48, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.81/1.65  tff(c_1849, plain, (![C_120, A_121, B_122]: (r1_tarski(C_120, k3_subset_1(A_121, B_122)) | ~r1_tarski(B_122, k3_subset_1(A_121, C_120)) | ~m1_subset_1(C_120, k1_zfmisc_1(A_121)) | ~m1_subset_1(B_122, k1_zfmisc_1(A_121)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.81/1.65  tff(c_1875, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_1849])).
% 3.81/1.65  tff(c_1891, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_730, c_52, c_1875])).
% 3.81/1.65  tff(c_1900, plain, (k3_xboole_0('#skF_5', k3_subset_1('#skF_3', '#skF_4'))='#skF_5'), inference(resolution, [status(thm)], [c_1891, c_8])).
% 3.81/1.65  tff(c_598, plain, (![C_74]: (k3_xboole_0('#skF_4', k3_xboole_0('#skF_5', C_74))=k3_xboole_0('#skF_4', C_74))), inference(superposition, [status(thm), theory('equality')], [c_130, c_547])).
% 3.81/1.65  tff(c_1915, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1900, c_598])).
% 3.81/1.65  tff(c_1947, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_130, c_1915])).
% 3.81/1.65  tff(c_1986, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1947, c_288])).
% 3.81/1.65  tff(c_32, plain, (![A_19]: (k1_subset_1(A_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.81/1.65  tff(c_44, plain, (![A_29, B_30]: (k1_subset_1(A_29)=B_30 | ~r1_tarski(B_30, k3_subset_1(A_29, B_30)) | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.81/1.65  tff(c_55, plain, (![B_30, A_29]: (k1_xboole_0=B_30 | ~r1_tarski(B_30, k3_subset_1(A_29, B_30)) | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_44])).
% 3.81/1.65  tff(c_2021, plain, (k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_1986, c_55])).
% 3.81/1.65  tff(c_2030, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_730, c_2021])).
% 3.81/1.65  tff(c_2032, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_2030])).
% 3.81/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.81/1.65  
% 3.81/1.65  Inference rules
% 3.81/1.65  ----------------------
% 3.81/1.65  #Ref     : 0
% 3.81/1.65  #Sup     : 508
% 3.81/1.65  #Fact    : 0
% 3.81/1.65  #Define  : 0
% 3.81/1.65  #Split   : 0
% 3.81/1.65  #Chain   : 0
% 3.81/1.65  #Close   : 0
% 3.81/1.65  
% 3.81/1.65  Ordering : KBO
% 3.81/1.65  
% 3.81/1.65  Simplification rules
% 3.81/1.65  ----------------------
% 3.81/1.65  #Subsume      : 12
% 3.81/1.65  #Demod        : 364
% 3.81/1.65  #Tautology    : 323
% 3.81/1.65  #SimpNegUnit  : 3
% 3.81/1.65  #BackRed      : 2
% 3.81/1.65  
% 3.81/1.65  #Partial instantiations: 0
% 3.81/1.65  #Strategies tried      : 1
% 3.81/1.65  
% 3.81/1.65  Timing (in seconds)
% 3.81/1.65  ----------------------
% 3.81/1.65  Preprocessing        : 0.32
% 3.81/1.65  Parsing              : 0.16
% 3.81/1.65  CNF conversion       : 0.02
% 3.81/1.65  Main loop            : 0.57
% 3.81/1.65  Inferencing          : 0.18
% 3.81/1.65  Reduction            : 0.24
% 3.81/1.65  Demodulation         : 0.20
% 3.81/1.65  BG Simplification    : 0.02
% 3.81/1.65  Subsumption          : 0.09
% 3.81/1.65  Abstraction          : 0.02
% 3.81/1.65  MUC search           : 0.00
% 3.81/1.65  Cooper               : 0.00
% 3.81/1.65  Total                : 0.92
% 3.81/1.65  Index Insertion      : 0.00
% 3.81/1.65  Index Deletion       : 0.00
% 3.81/1.65  Index Matching       : 0.00
% 3.81/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
