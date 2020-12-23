%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:22 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 112 expanded)
%              Number of leaves         :   31 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :  105 ( 220 expanded)
%              Number of equality atoms :   15 (  30 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_67,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_48,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_83,plain,(
    ! [B_41,A_42] :
      ( v1_xboole_0(B_41)
      | ~ m1_subset_1(B_41,A_42)
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_91,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_50,c_83])).

tff(c_92,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_46,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_167,plain,(
    ! [A_63,B_64] :
      ( k4_xboole_0(A_63,B_64) = k3_subset_1(A_63,B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_181,plain,(
    k4_xboole_0('#skF_4','#skF_6') = k3_subset_1('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_167])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9] :
      ( r1_tarski(A_7,B_8)
      | ~ r1_tarski(A_7,k4_xboole_0(B_8,C_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_196,plain,(
    ! [A_65] :
      ( r1_tarski(A_65,'#skF_4')
      | ~ r1_tarski(A_65,k3_subset_1('#skF_4','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_10])).

tff(c_209,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_196])).

tff(c_16,plain,(
    ! [C_17,A_13] :
      ( r2_hidden(C_17,k1_zfmisc_1(A_13))
      | ~ r1_tarski(C_17,A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_113,plain,(
    ! [B_50,A_51] :
      ( m1_subset_1(B_50,A_51)
      | ~ r2_hidden(B_50,A_51)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_124,plain,(
    ! [C_17,A_13] :
      ( m1_subset_1(C_17,k1_zfmisc_1(A_13))
      | v1_xboole_0(k1_zfmisc_1(A_13))
      | ~ r1_tarski(C_17,A_13) ) ),
    inference(resolution,[status(thm)],[c_16,c_113])).

tff(c_832,plain,(
    ! [C_119,A_120,B_121] :
      ( r1_tarski(C_119,k3_subset_1(A_120,B_121))
      | ~ r1_tarski(B_121,k3_subset_1(A_120,C_119))
      | ~ m1_subset_1(C_119,k1_zfmisc_1(A_120))
      | ~ m1_subset_1(B_121,k1_zfmisc_1(A_120)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_850,plain,
    ( r1_tarski('#skF_6',k3_subset_1('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_832])).

tff(c_859,plain,
    ( r1_tarski('#skF_6',k3_subset_1('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_850])).

tff(c_907,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_859])).

tff(c_910,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_124,c_907])).

tff(c_916,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_910])).

tff(c_918,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_916])).

tff(c_920,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_859])).

tff(c_919,plain,(
    r1_tarski('#skF_6',k3_subset_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_859])).

tff(c_12,plain,(
    ! [A_10,C_12,B_11] :
      ( r1_tarski(A_10,C_12)
      | ~ r1_tarski(B_11,C_12)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_961,plain,(
    ! [A_122] :
      ( r1_tarski(A_122,k3_subset_1('#skF_4','#skF_5'))
      | ~ r1_tarski(A_122,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_919,c_12])).

tff(c_34,plain,(
    ! [A_20] : k1_subset_1(A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_42,plain,(
    ! [A_27,B_28] :
      ( k1_subset_1(A_27) = B_28
      | ~ r1_tarski(B_28,k3_subset_1(A_27,B_28))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_51,plain,(
    ! [B_28,A_27] :
      ( k1_xboole_0 = B_28
      | ~ r1_tarski(B_28,k3_subset_1(A_27,B_28))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_42])).

tff(c_971,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_961,c_51])).

tff(c_980,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_920,c_971])).

tff(c_982,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_980])).

tff(c_984,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_66,plain,(
    ! [C_33,A_34] :
      ( r2_hidden(C_33,k1_zfmisc_1(A_34))
      | ~ r1_tarski(C_33,A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    ! [A_34,C_33] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_34))
      | ~ r1_tarski(C_33,A_34) ) ),
    inference(resolution,[status(thm)],[c_66,c_2])).

tff(c_996,plain,(
    ! [C_33] : ~ r1_tarski(C_33,'#skF_4') ),
    inference(resolution,[status(thm)],[c_984,c_70])).

tff(c_1080,plain,(
    ! [A_145,B_146] :
      ( k4_xboole_0(A_145,B_146) = k3_subset_1(A_145,B_146)
      | ~ m1_subset_1(B_146,k1_zfmisc_1(A_145)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1094,plain,(
    k4_xboole_0('#skF_4','#skF_6') = k3_subset_1('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_1080])).

tff(c_1098,plain,(
    ! [A_7] :
      ( r1_tarski(A_7,'#skF_4')
      | ~ r1_tarski(A_7,k3_subset_1('#skF_4','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1094,c_10])).

tff(c_1104,plain,(
    ! [A_7] : ~ r1_tarski(A_7,k3_subset_1('#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_996,c_1098])).

tff(c_1107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1104,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:36:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.24/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.48  
% 3.24/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.48  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 3.24/1.48  
% 3.24/1.48  %Foreground sorts:
% 3.24/1.48  
% 3.24/1.48  
% 3.24/1.48  %Background operators:
% 3.24/1.48  
% 3.24/1.48  
% 3.24/1.48  %Foreground operators:
% 3.24/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.24/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.24/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.24/1.48  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.24/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.24/1.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.24/1.48  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.24/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.24/1.48  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.24/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.24/1.48  tff('#skF_6', type, '#skF_6': $i).
% 3.24/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.24/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.24/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.24/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.24/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.24/1.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.24/1.48  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.24/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.24/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.24/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.24/1.48  
% 3.24/1.50  tff(f_95, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_subset_1)).
% 3.24/1.50  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.24/1.50  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.24/1.50  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.24/1.50  tff(f_52, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.24/1.50  tff(f_80, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_subset_1)).
% 3.24/1.50  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.24/1.50  tff(f_67, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 3.24/1.50  tff(f_86, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 3.24/1.50  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.24/1.50  tff(c_44, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.24/1.50  tff(c_48, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.24/1.50  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.24/1.50  tff(c_83, plain, (![B_41, A_42]: (v1_xboole_0(B_41) | ~m1_subset_1(B_41, A_42) | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.24/1.50  tff(c_91, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_83])).
% 3.24/1.50  tff(c_92, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_91])).
% 3.24/1.50  tff(c_46, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.24/1.50  tff(c_167, plain, (![A_63, B_64]: (k4_xboole_0(A_63, B_64)=k3_subset_1(A_63, B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.24/1.50  tff(c_181, plain, (k4_xboole_0('#skF_4', '#skF_6')=k3_subset_1('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_50, c_167])).
% 3.24/1.50  tff(c_10, plain, (![A_7, B_8, C_9]: (r1_tarski(A_7, B_8) | ~r1_tarski(A_7, k4_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.24/1.50  tff(c_196, plain, (![A_65]: (r1_tarski(A_65, '#skF_4') | ~r1_tarski(A_65, k3_subset_1('#skF_4', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_181, c_10])).
% 3.24/1.50  tff(c_209, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_196])).
% 3.24/1.50  tff(c_16, plain, (![C_17, A_13]: (r2_hidden(C_17, k1_zfmisc_1(A_13)) | ~r1_tarski(C_17, A_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.24/1.50  tff(c_113, plain, (![B_50, A_51]: (m1_subset_1(B_50, A_51) | ~r2_hidden(B_50, A_51) | v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.24/1.50  tff(c_124, plain, (![C_17, A_13]: (m1_subset_1(C_17, k1_zfmisc_1(A_13)) | v1_xboole_0(k1_zfmisc_1(A_13)) | ~r1_tarski(C_17, A_13))), inference(resolution, [status(thm)], [c_16, c_113])).
% 3.24/1.50  tff(c_832, plain, (![C_119, A_120, B_121]: (r1_tarski(C_119, k3_subset_1(A_120, B_121)) | ~r1_tarski(B_121, k3_subset_1(A_120, C_119)) | ~m1_subset_1(C_119, k1_zfmisc_1(A_120)) | ~m1_subset_1(B_121, k1_zfmisc_1(A_120)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.24/1.50  tff(c_850, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_46, c_832])).
% 3.24/1.50  tff(c_859, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_850])).
% 3.24/1.50  tff(c_907, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_859])).
% 3.24/1.50  tff(c_910, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4')) | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_124, c_907])).
% 3.24/1.50  tff(c_916, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_209, c_910])).
% 3.24/1.50  tff(c_918, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_916])).
% 3.24/1.50  tff(c_920, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_859])).
% 3.24/1.50  tff(c_919, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_859])).
% 3.24/1.50  tff(c_12, plain, (![A_10, C_12, B_11]: (r1_tarski(A_10, C_12) | ~r1_tarski(B_11, C_12) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.24/1.50  tff(c_961, plain, (![A_122]: (r1_tarski(A_122, k3_subset_1('#skF_4', '#skF_5')) | ~r1_tarski(A_122, '#skF_6'))), inference(resolution, [status(thm)], [c_919, c_12])).
% 3.24/1.50  tff(c_34, plain, (![A_20]: (k1_subset_1(A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.24/1.50  tff(c_42, plain, (![A_27, B_28]: (k1_subset_1(A_27)=B_28 | ~r1_tarski(B_28, k3_subset_1(A_27, B_28)) | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.24/1.50  tff(c_51, plain, (![B_28, A_27]: (k1_xboole_0=B_28 | ~r1_tarski(B_28, k3_subset_1(A_27, B_28)) | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_42])).
% 3.24/1.50  tff(c_971, plain, (k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4')) | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_961, c_51])).
% 3.24/1.50  tff(c_980, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_920, c_971])).
% 3.24/1.50  tff(c_982, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_980])).
% 3.24/1.50  tff(c_984, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_91])).
% 3.24/1.50  tff(c_66, plain, (![C_33, A_34]: (r2_hidden(C_33, k1_zfmisc_1(A_34)) | ~r1_tarski(C_33, A_34))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.24/1.50  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.24/1.50  tff(c_70, plain, (![A_34, C_33]: (~v1_xboole_0(k1_zfmisc_1(A_34)) | ~r1_tarski(C_33, A_34))), inference(resolution, [status(thm)], [c_66, c_2])).
% 3.24/1.50  tff(c_996, plain, (![C_33]: (~r1_tarski(C_33, '#skF_4'))), inference(resolution, [status(thm)], [c_984, c_70])).
% 3.24/1.50  tff(c_1080, plain, (![A_145, B_146]: (k4_xboole_0(A_145, B_146)=k3_subset_1(A_145, B_146) | ~m1_subset_1(B_146, k1_zfmisc_1(A_145)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.24/1.50  tff(c_1094, plain, (k4_xboole_0('#skF_4', '#skF_6')=k3_subset_1('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_50, c_1080])).
% 3.24/1.50  tff(c_1098, plain, (![A_7]: (r1_tarski(A_7, '#skF_4') | ~r1_tarski(A_7, k3_subset_1('#skF_4', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_1094, c_10])).
% 3.24/1.50  tff(c_1104, plain, (![A_7]: (~r1_tarski(A_7, k3_subset_1('#skF_4', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_996, c_1098])).
% 3.24/1.50  tff(c_1107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1104, c_46])).
% 3.24/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.50  
% 3.24/1.50  Inference rules
% 3.24/1.50  ----------------------
% 3.24/1.50  #Ref     : 0
% 3.24/1.50  #Sup     : 231
% 3.24/1.50  #Fact    : 0
% 3.24/1.50  #Define  : 0
% 3.24/1.50  #Split   : 6
% 3.24/1.50  #Chain   : 0
% 3.24/1.50  #Close   : 0
% 3.24/1.50  
% 3.24/1.50  Ordering : KBO
% 3.24/1.50  
% 3.24/1.50  Simplification rules
% 3.24/1.50  ----------------------
% 3.24/1.50  #Subsume      : 30
% 3.24/1.50  #Demod        : 66
% 3.24/1.50  #Tautology    : 61
% 3.24/1.50  #SimpNegUnit  : 23
% 3.24/1.50  #BackRed      : 5
% 3.24/1.50  
% 3.24/1.50  #Partial instantiations: 0
% 3.24/1.50  #Strategies tried      : 1
% 3.24/1.50  
% 3.24/1.50  Timing (in seconds)
% 3.24/1.50  ----------------------
% 3.24/1.50  Preprocessing        : 0.32
% 3.24/1.50  Parsing              : 0.16
% 3.24/1.50  CNF conversion       : 0.02
% 3.24/1.50  Main loop            : 0.42
% 3.24/1.50  Inferencing          : 0.16
% 3.24/1.50  Reduction            : 0.12
% 3.24/1.50  Demodulation         : 0.08
% 3.24/1.50  BG Simplification    : 0.02
% 3.24/1.50  Subsumption          : 0.08
% 3.24/1.50  Abstraction          : 0.02
% 3.24/1.50  MUC search           : 0.00
% 3.24/1.50  Cooper               : 0.00
% 3.24/1.50  Total                : 0.77
% 3.24/1.50  Index Insertion      : 0.00
% 3.24/1.50  Index Deletion       : 0.00
% 3.24/1.50  Index Matching       : 0.00
% 3.24/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
