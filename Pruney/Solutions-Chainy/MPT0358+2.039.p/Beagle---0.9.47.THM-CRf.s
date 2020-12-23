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
% DateTime   : Thu Dec  3 09:56:05 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 110 expanded)
%              Number of leaves         :   28 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :   97 ( 179 expanded)
%              Number of equality atoms :   32 (  58 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_74,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_63,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ! [A_21] : ~ v1_xboole_0(k1_zfmisc_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_18,plain,(
    ! [C_13,A_9] :
      ( r2_hidden(C_13,k1_zfmisc_1(A_9))
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_147,plain,(
    ! [B_43,A_44] :
      ( m1_subset_1(B_43,A_44)
      | ~ r2_hidden(B_43,A_44)
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_150,plain,(
    ! [C_13,A_9] :
      ( m1_subset_1(C_13,k1_zfmisc_1(A_9))
      | v1_xboole_0(k1_zfmisc_1(A_9))
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(resolution,[status(thm)],[c_18,c_147])).

tff(c_153,plain,(
    ! [C_13,A_9] :
      ( m1_subset_1(C_13,k1_zfmisc_1(A_9))
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_150])).

tff(c_36,plain,(
    ! [A_16] : k1_subset_1(A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_46,plain,
    ( k1_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_54,plain,
    ( k1_xboole_0 != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_46])).

tff(c_71,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_52,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_53,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_52])).

tff(c_77,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_53])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_93,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = '#skF_4'
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_10])).

tff(c_97,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6,c_93])).

tff(c_241,plain,(
    ! [A_59,B_60] :
      ( k4_xboole_0(A_59,B_60) = k3_subset_1(A_59,B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_269,plain,(
    ! [A_61,C_62] :
      ( k4_xboole_0(A_61,C_62) = k3_subset_1(A_61,C_62)
      | ~ r1_tarski(C_62,A_61) ) ),
    inference(resolution,[status(thm)],[c_153,c_241])).

tff(c_278,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k3_subset_1(B_2,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_269])).

tff(c_283,plain,(
    ! [B_2] : k3_subset_1(B_2,B_2) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_278])).

tff(c_291,plain,(
    ! [A_64,B_65] :
      ( m1_subset_1(k3_subset_1(A_64,B_65),k1_zfmisc_1(A_64))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_307,plain,(
    ! [B_66] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(B_66))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(B_66)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_291])).

tff(c_310,plain,(
    ! [A_9] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(A_9))
      | ~ r1_tarski(A_9,A_9) ) ),
    inference(resolution,[status(thm)],[c_153,c_307])).

tff(c_320,plain,(
    ! [A_67] : m1_subset_1('#skF_4',k1_zfmisc_1(A_67)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_310])).

tff(c_169,plain,(
    ! [B_49,A_50] :
      ( r2_hidden(B_49,A_50)
      | ~ m1_subset_1(B_49,A_50)
      | v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    ! [C_13,A_9] :
      ( r1_tarski(C_13,A_9)
      | ~ r2_hidden(C_13,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_176,plain,(
    ! [B_49,A_9] :
      ( r1_tarski(B_49,A_9)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_9))
      | v1_xboole_0(k1_zfmisc_1(A_9)) ) ),
    inference(resolution,[status(thm)],[c_169,c_16])).

tff(c_180,plain,(
    ! [B_49,A_9] :
      ( r1_tarski(B_49,A_9)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_9)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_176])).

tff(c_331,plain,(
    ! [A_67] : r1_tarski('#skF_4',A_67) ),
    inference(resolution,[status(thm)],[c_320,c_180])).

tff(c_336,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_71])).

tff(c_337,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_338,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_356,plain,(
    ! [A_74,B_75] :
      ( k4_xboole_0(A_74,B_75) = k1_xboole_0
      | ~ r1_tarski(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_367,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_338,c_356])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_582,plain,(
    ! [A_103,B_104] :
      ( k4_xboole_0(A_103,B_104) = k3_subset_1(A_103,B_104)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_599,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_582])).

tff(c_350,plain,(
    ! [A_72,B_73] :
      ( r1_tarski(A_72,B_73)
      | k4_xboole_0(A_72,B_73) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k4_xboole_0(B_8,A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_355,plain,(
    ! [A_72,B_8] :
      ( k1_xboole_0 = A_72
      | k4_xboole_0(A_72,k4_xboole_0(B_8,A_72)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_350,c_14])).

tff(c_615,plain,
    ( k1_xboole_0 = '#skF_4'
    | k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_599,c_355])).

tff(c_622,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_615])).

tff(c_624,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_337,c_622])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:09:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.50  
% 2.90/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.50  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.90/1.50  
% 2.90/1.50  %Foreground sorts:
% 2.90/1.50  
% 2.90/1.50  
% 2.90/1.50  %Background operators:
% 2.90/1.50  
% 2.90/1.50  
% 2.90/1.50  %Foreground operators:
% 2.90/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.90/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.90/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.90/1.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.90/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.90/1.50  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.90/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.90/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.90/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.50  tff('#skF_4', type, '#skF_4': $i).
% 2.90/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.90/1.50  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.90/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.90/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.90/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.90/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.90/1.50  
% 2.90/1.52  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.90/1.52  tff(f_74, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.90/1.52  tff(f_48, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.90/1.52  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.90/1.52  tff(f_63, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.90/1.52  tff(f_81, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 2.90/1.52  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.90/1.52  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.90/1.52  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.90/1.52  tff(f_41, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 2.90/1.52  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.90/1.52  tff(c_42, plain, (![A_21]: (~v1_xboole_0(k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.90/1.52  tff(c_18, plain, (![C_13, A_9]: (r2_hidden(C_13, k1_zfmisc_1(A_9)) | ~r1_tarski(C_13, A_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.90/1.52  tff(c_147, plain, (![B_43, A_44]: (m1_subset_1(B_43, A_44) | ~r2_hidden(B_43, A_44) | v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.90/1.52  tff(c_150, plain, (![C_13, A_9]: (m1_subset_1(C_13, k1_zfmisc_1(A_9)) | v1_xboole_0(k1_zfmisc_1(A_9)) | ~r1_tarski(C_13, A_9))), inference(resolution, [status(thm)], [c_18, c_147])).
% 2.90/1.52  tff(c_153, plain, (![C_13, A_9]: (m1_subset_1(C_13, k1_zfmisc_1(A_9)) | ~r1_tarski(C_13, A_9))), inference(negUnitSimplification, [status(thm)], [c_42, c_150])).
% 2.90/1.52  tff(c_36, plain, (![A_16]: (k1_subset_1(A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.90/1.52  tff(c_46, plain, (k1_subset_1('#skF_3')!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.90/1.52  tff(c_54, plain, (k1_xboole_0!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_46])).
% 2.90/1.52  tff(c_71, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_54])).
% 2.90/1.52  tff(c_52, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.90/1.52  tff(c_53, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_52])).
% 2.90/1.52  tff(c_77, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_71, c_53])).
% 2.90/1.52  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.90/1.52  tff(c_93, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)='#skF_4' | ~r1_tarski(A_34, B_35))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_10])).
% 2.90/1.52  tff(c_97, plain, (![B_2]: (k4_xboole_0(B_2, B_2)='#skF_4')), inference(resolution, [status(thm)], [c_6, c_93])).
% 2.90/1.52  tff(c_241, plain, (![A_59, B_60]: (k4_xboole_0(A_59, B_60)=k3_subset_1(A_59, B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.90/1.52  tff(c_269, plain, (![A_61, C_62]: (k4_xboole_0(A_61, C_62)=k3_subset_1(A_61, C_62) | ~r1_tarski(C_62, A_61))), inference(resolution, [status(thm)], [c_153, c_241])).
% 2.90/1.52  tff(c_278, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k3_subset_1(B_2, B_2))), inference(resolution, [status(thm)], [c_6, c_269])).
% 2.90/1.52  tff(c_283, plain, (![B_2]: (k3_subset_1(B_2, B_2)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_278])).
% 2.90/1.52  tff(c_291, plain, (![A_64, B_65]: (m1_subset_1(k3_subset_1(A_64, B_65), k1_zfmisc_1(A_64)) | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.90/1.52  tff(c_307, plain, (![B_66]: (m1_subset_1('#skF_4', k1_zfmisc_1(B_66)) | ~m1_subset_1(B_66, k1_zfmisc_1(B_66)))), inference(superposition, [status(thm), theory('equality')], [c_283, c_291])).
% 2.90/1.52  tff(c_310, plain, (![A_9]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_9)) | ~r1_tarski(A_9, A_9))), inference(resolution, [status(thm)], [c_153, c_307])).
% 2.90/1.52  tff(c_320, plain, (![A_67]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_67)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_310])).
% 2.90/1.52  tff(c_169, plain, (![B_49, A_50]: (r2_hidden(B_49, A_50) | ~m1_subset_1(B_49, A_50) | v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.90/1.52  tff(c_16, plain, (![C_13, A_9]: (r1_tarski(C_13, A_9) | ~r2_hidden(C_13, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.90/1.52  tff(c_176, plain, (![B_49, A_9]: (r1_tarski(B_49, A_9) | ~m1_subset_1(B_49, k1_zfmisc_1(A_9)) | v1_xboole_0(k1_zfmisc_1(A_9)))), inference(resolution, [status(thm)], [c_169, c_16])).
% 2.90/1.52  tff(c_180, plain, (![B_49, A_9]: (r1_tarski(B_49, A_9) | ~m1_subset_1(B_49, k1_zfmisc_1(A_9)))), inference(negUnitSimplification, [status(thm)], [c_42, c_176])).
% 2.90/1.52  tff(c_331, plain, (![A_67]: (r1_tarski('#skF_4', A_67))), inference(resolution, [status(thm)], [c_320, c_180])).
% 2.90/1.52  tff(c_336, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_331, c_71])).
% 2.90/1.52  tff(c_337, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_54])).
% 2.90/1.52  tff(c_338, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_54])).
% 2.90/1.52  tff(c_356, plain, (![A_74, B_75]: (k4_xboole_0(A_74, B_75)=k1_xboole_0 | ~r1_tarski(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.90/1.52  tff(c_367, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_338, c_356])).
% 2.90/1.52  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.90/1.52  tff(c_582, plain, (![A_103, B_104]: (k4_xboole_0(A_103, B_104)=k3_subset_1(A_103, B_104) | ~m1_subset_1(B_104, k1_zfmisc_1(A_103)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.90/1.52  tff(c_599, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_582])).
% 2.90/1.52  tff(c_350, plain, (![A_72, B_73]: (r1_tarski(A_72, B_73) | k4_xboole_0(A_72, B_73)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.90/1.52  tff(c_14, plain, (![A_7, B_8]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k4_xboole_0(B_8, A_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.90/1.52  tff(c_355, plain, (![A_72, B_8]: (k1_xboole_0=A_72 | k4_xboole_0(A_72, k4_xboole_0(B_8, A_72))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_350, c_14])).
% 2.90/1.52  tff(c_615, plain, (k1_xboole_0='#skF_4' | k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_599, c_355])).
% 2.90/1.52  tff(c_622, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_367, c_615])).
% 2.90/1.52  tff(c_624, plain, $false, inference(negUnitSimplification, [status(thm)], [c_337, c_622])).
% 2.90/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.52  
% 2.90/1.52  Inference rules
% 2.90/1.52  ----------------------
% 2.90/1.52  #Ref     : 0
% 2.90/1.52  #Sup     : 127
% 2.90/1.52  #Fact    : 0
% 2.90/1.52  #Define  : 0
% 2.90/1.52  #Split   : 5
% 2.90/1.52  #Chain   : 0
% 2.90/1.52  #Close   : 0
% 2.90/1.52  
% 2.90/1.52  Ordering : KBO
% 2.90/1.52  
% 2.90/1.52  Simplification rules
% 2.90/1.52  ----------------------
% 2.90/1.52  #Subsume      : 27
% 2.90/1.52  #Demod        : 22
% 2.90/1.52  #Tautology    : 55
% 2.90/1.52  #SimpNegUnit  : 7
% 2.90/1.52  #BackRed      : 3
% 2.90/1.52  
% 2.90/1.52  #Partial instantiations: 0
% 2.90/1.52  #Strategies tried      : 1
% 2.90/1.52  
% 2.90/1.52  Timing (in seconds)
% 2.90/1.52  ----------------------
% 2.90/1.52  Preprocessing        : 0.33
% 2.90/1.52  Parsing              : 0.16
% 2.90/1.52  CNF conversion       : 0.02
% 2.90/1.52  Main loop            : 0.39
% 2.90/1.52  Inferencing          : 0.15
% 2.90/1.52  Reduction            : 0.11
% 2.90/1.52  Demodulation         : 0.08
% 2.90/1.52  BG Simplification    : 0.02
% 2.90/1.52  Subsumption          : 0.08
% 2.90/1.52  Abstraction          : 0.02
% 2.90/1.52  MUC search           : 0.00
% 2.90/1.52  Cooper               : 0.00
% 2.90/1.52  Total                : 0.77
% 2.90/1.52  Index Insertion      : 0.00
% 2.90/1.52  Index Deletion       : 0.00
% 2.90/1.52  Index Matching       : 0.00
% 2.90/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
