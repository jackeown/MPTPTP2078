%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:17 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 133 expanded)
%              Number of leaves         :   34 (  56 expanded)
%              Depth                    :    8
%              Number of atoms          :   93 ( 185 expanded)
%              Number of equality atoms :   40 (  89 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_62,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_64,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_68,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_74,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_66,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_84,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(c_150,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_1'(A_46,B_47),A_46)
      | r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    ! [A_6] : k3_xboole_0(A_6,A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_121,plain,(
    ! [A_37,B_38,C_39] :
      ( ~ r1_xboole_0(A_37,B_38)
      | ~ r2_hidden(C_39,k3_xboole_0(A_37,B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_145,plain,(
    ! [A_43,C_44] :
      ( ~ r1_xboole_0(A_43,A_43)
      | ~ r2_hidden(C_44,A_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_121])).

tff(c_148,plain,(
    ! [C_44] : ~ r2_hidden(C_44,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_145])).

tff(c_159,plain,(
    ! [B_47] : r1_tarski(k1_xboole_0,B_47) ),
    inference(resolution,[status(thm)],[c_150,c_148])).

tff(c_20,plain,(
    ! [A_16] : k5_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_125,plain,(
    ! [A_40,B_41] : k5_xboole_0(A_40,k3_xboole_0(A_40,B_41)) = k4_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_134,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k4_xboole_0(A_6,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_125])).

tff(c_137,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_134])).

tff(c_24,plain,(
    ! [A_18] : k2_subset_1(A_18) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_28,plain,(
    ! [A_21] : m1_subset_1(k2_subset_1(A_21),k1_zfmisc_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_50,plain,(
    ! [A_21] : m1_subset_1(A_21,k1_zfmisc_1(A_21)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28])).

tff(c_184,plain,(
    ! [A_60,B_61] :
      ( k4_xboole_0(A_60,B_61) = k3_subset_1(A_60,B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_187,plain,(
    ! [A_21] : k4_xboole_0(A_21,A_21) = k3_subset_1(A_21,A_21) ),
    inference(resolution,[status(thm)],[c_50,c_184])).

tff(c_189,plain,(
    ! [A_21] : k3_subset_1(A_21,A_21) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_187])).

tff(c_48,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | k2_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_51,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_48])).

tff(c_106,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_51])).

tff(c_42,plain,
    ( k2_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_53,plain,
    ( '#skF_3' != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_42])).

tff(c_120,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_106,c_53])).

tff(c_190,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_120])).

tff(c_193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_190])).

tff(c_195,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_51])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_30,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(k3_subset_1(A_22,B_23),k1_zfmisc_1(A_22))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_194,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_51])).

tff(c_296,plain,(
    ! [A_91,B_92] :
      ( k3_subset_1(A_91,k3_subset_1(A_91,B_92)) = B_92
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_305,plain,(
    k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_296])).

tff(c_22,plain,(
    ! [A_17] : k1_subset_1(A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_38,plain,(
    ! [A_27,B_28] :
      ( k1_subset_1(A_27) = B_28
      | ~ r1_tarski(B_28,k3_subset_1(A_27,B_28))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_399,plain,(
    ! [B_99,A_100] :
      ( k1_xboole_0 = B_99
      | ~ r1_tarski(B_99,k3_subset_1(A_100,B_99))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_100)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_38])).

tff(c_405,plain,
    ( k3_subset_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1(k3_subset_1('#skF_3','#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_399])).

tff(c_420,plain,
    ( k3_subset_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ m1_subset_1(k3_subset_1('#skF_3','#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_405])).

tff(c_457,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_3','#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_420])).

tff(c_460,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_457])).

tff(c_464,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_460])).

tff(c_465,plain,(
    k3_subset_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_420])).

tff(c_468,plain,(
    k3_subset_1('#skF_3',k1_xboole_0) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_305])).

tff(c_34,plain,(
    ! [A_26] : k3_subset_1(A_26,k1_subset_1(A_26)) = k2_subset_1(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_52,plain,(
    ! [A_26] : k3_subset_1(A_26,k1_subset_1(A_26)) = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_34])).

tff(c_55,plain,(
    ! [A_26] : k3_subset_1(A_26,k1_xboole_0) = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_52])).

tff(c_498,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_468,c_55])).

tff(c_510,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_498])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:18:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.36  
% 2.54/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.36  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.54/1.36  
% 2.54/1.36  %Foreground sorts:
% 2.54/1.36  
% 2.54/1.36  
% 2.54/1.36  %Background operators:
% 2.54/1.36  
% 2.54/1.36  
% 2.54/1.36  %Foreground operators:
% 2.54/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.54/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.54/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.54/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.54/1.36  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.54/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.54/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.54/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.54/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.54/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.54/1.36  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.54/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.54/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.54/1.36  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.54/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.54/1.36  
% 2.54/1.38  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.54/1.38  tff(f_62, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.54/1.38  tff(f_34, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.54/1.38  tff(f_48, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.54/1.38  tff(f_64, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.54/1.38  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.54/1.38  tff(f_68, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.54/1.38  tff(f_74, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.54/1.38  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.54/1.38  tff(f_97, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 2.54/1.38  tff(f_78, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.54/1.38  tff(f_82, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.54/1.38  tff(f_66, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.54/1.38  tff(f_90, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 2.54/1.38  tff(f_84, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 2.54/1.38  tff(c_150, plain, (![A_46, B_47]: (r2_hidden('#skF_1'(A_46, B_47), A_46) | r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.54/1.38  tff(c_16, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.54/1.38  tff(c_8, plain, (![A_6]: (k3_xboole_0(A_6, A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.54/1.38  tff(c_121, plain, (![A_37, B_38, C_39]: (~r1_xboole_0(A_37, B_38) | ~r2_hidden(C_39, k3_xboole_0(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.54/1.38  tff(c_145, plain, (![A_43, C_44]: (~r1_xboole_0(A_43, A_43) | ~r2_hidden(C_44, A_43))), inference(superposition, [status(thm), theory('equality')], [c_8, c_121])).
% 2.54/1.38  tff(c_148, plain, (![C_44]: (~r2_hidden(C_44, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_145])).
% 2.54/1.38  tff(c_159, plain, (![B_47]: (r1_tarski(k1_xboole_0, B_47))), inference(resolution, [status(thm)], [c_150, c_148])).
% 2.54/1.38  tff(c_20, plain, (![A_16]: (k5_xboole_0(A_16, A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.54/1.38  tff(c_125, plain, (![A_40, B_41]: (k5_xboole_0(A_40, k3_xboole_0(A_40, B_41))=k4_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.54/1.38  tff(c_134, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k4_xboole_0(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_8, c_125])).
% 2.54/1.38  tff(c_137, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_134])).
% 2.54/1.38  tff(c_24, plain, (![A_18]: (k2_subset_1(A_18)=A_18)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.54/1.38  tff(c_28, plain, (![A_21]: (m1_subset_1(k2_subset_1(A_21), k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.54/1.38  tff(c_50, plain, (![A_21]: (m1_subset_1(A_21, k1_zfmisc_1(A_21)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28])).
% 2.54/1.38  tff(c_184, plain, (![A_60, B_61]: (k4_xboole_0(A_60, B_61)=k3_subset_1(A_60, B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.54/1.38  tff(c_187, plain, (![A_21]: (k4_xboole_0(A_21, A_21)=k3_subset_1(A_21, A_21))), inference(resolution, [status(thm)], [c_50, c_184])).
% 2.54/1.38  tff(c_189, plain, (![A_21]: (k3_subset_1(A_21, A_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_137, c_187])).
% 2.54/1.38  tff(c_48, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | k2_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.54/1.38  tff(c_51, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_48])).
% 2.54/1.38  tff(c_106, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_51])).
% 2.54/1.38  tff(c_42, plain, (k2_subset_1('#skF_3')!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.54/1.38  tff(c_53, plain, ('#skF_3'!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_42])).
% 2.54/1.38  tff(c_120, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_106, c_53])).
% 2.54/1.38  tff(c_190, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_189, c_120])).
% 2.54/1.38  tff(c_193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_159, c_190])).
% 2.54/1.38  tff(c_195, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_51])).
% 2.54/1.38  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.54/1.38  tff(c_30, plain, (![A_22, B_23]: (m1_subset_1(k3_subset_1(A_22, B_23), k1_zfmisc_1(A_22)) | ~m1_subset_1(B_23, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.54/1.38  tff(c_194, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_51])).
% 2.54/1.38  tff(c_296, plain, (![A_91, B_92]: (k3_subset_1(A_91, k3_subset_1(A_91, B_92))=B_92 | ~m1_subset_1(B_92, k1_zfmisc_1(A_91)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.54/1.38  tff(c_305, plain, (k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_40, c_296])).
% 2.54/1.38  tff(c_22, plain, (![A_17]: (k1_subset_1(A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.54/1.38  tff(c_38, plain, (![A_27, B_28]: (k1_subset_1(A_27)=B_28 | ~r1_tarski(B_28, k3_subset_1(A_27, B_28)) | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.54/1.38  tff(c_399, plain, (![B_99, A_100]: (k1_xboole_0=B_99 | ~r1_tarski(B_99, k3_subset_1(A_100, B_99)) | ~m1_subset_1(B_99, k1_zfmisc_1(A_100)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_38])).
% 2.54/1.38  tff(c_405, plain, (k3_subset_1('#skF_3', '#skF_4')=k1_xboole_0 | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1(k3_subset_1('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_305, c_399])).
% 2.54/1.38  tff(c_420, plain, (k3_subset_1('#skF_3', '#skF_4')=k1_xboole_0 | ~m1_subset_1(k3_subset_1('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_405])).
% 2.54/1.38  tff(c_457, plain, (~m1_subset_1(k3_subset_1('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_420])).
% 2.54/1.38  tff(c_460, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_457])).
% 2.54/1.38  tff(c_464, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_460])).
% 2.54/1.38  tff(c_465, plain, (k3_subset_1('#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_420])).
% 2.54/1.38  tff(c_468, plain, (k3_subset_1('#skF_3', k1_xboole_0)='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_465, c_305])).
% 2.54/1.38  tff(c_34, plain, (![A_26]: (k3_subset_1(A_26, k1_subset_1(A_26))=k2_subset_1(A_26))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.54/1.38  tff(c_52, plain, (![A_26]: (k3_subset_1(A_26, k1_subset_1(A_26))=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_34])).
% 2.54/1.38  tff(c_55, plain, (![A_26]: (k3_subset_1(A_26, k1_xboole_0)=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_52])).
% 2.54/1.38  tff(c_498, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_468, c_55])).
% 2.54/1.38  tff(c_510, plain, $false, inference(negUnitSimplification, [status(thm)], [c_195, c_498])).
% 2.54/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.38  
% 2.54/1.38  Inference rules
% 2.54/1.38  ----------------------
% 2.54/1.38  #Ref     : 0
% 2.54/1.38  #Sup     : 97
% 2.54/1.38  #Fact    : 0
% 2.54/1.38  #Define  : 0
% 2.54/1.38  #Split   : 2
% 2.54/1.38  #Chain   : 0
% 2.54/1.38  #Close   : 0
% 2.54/1.38  
% 2.54/1.38  Ordering : KBO
% 2.54/1.38  
% 2.54/1.38  Simplification rules
% 2.54/1.38  ----------------------
% 2.54/1.38  #Subsume      : 2
% 2.54/1.38  #Demod        : 55
% 2.54/1.38  #Tautology    : 66
% 2.54/1.38  #SimpNegUnit  : 1
% 2.54/1.38  #BackRed      : 6
% 2.54/1.38  
% 2.54/1.38  #Partial instantiations: 0
% 2.54/1.38  #Strategies tried      : 1
% 2.54/1.38  
% 2.54/1.38  Timing (in seconds)
% 2.54/1.38  ----------------------
% 2.54/1.38  Preprocessing        : 0.32
% 2.54/1.38  Parsing              : 0.17
% 2.54/1.38  CNF conversion       : 0.02
% 2.54/1.38  Main loop            : 0.24
% 2.54/1.38  Inferencing          : 0.09
% 2.54/1.38  Reduction            : 0.08
% 2.54/1.38  Demodulation         : 0.06
% 2.54/1.38  BG Simplification    : 0.01
% 2.54/1.38  Subsumption          : 0.04
% 2.54/1.38  Abstraction          : 0.01
% 2.54/1.38  MUC search           : 0.00
% 2.54/1.38  Cooper               : 0.00
% 2.54/1.38  Total                : 0.60
% 2.54/1.38  Index Insertion      : 0.00
% 2.54/1.38  Index Deletion       : 0.00
% 2.54/1.38  Index Matching       : 0.00
% 2.54/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
