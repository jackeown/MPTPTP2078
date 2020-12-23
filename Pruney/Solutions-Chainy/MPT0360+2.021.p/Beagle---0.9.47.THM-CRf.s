%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:21 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 132 expanded)
%              Number of leaves         :   28 (  57 expanded)
%              Depth                    :   13
%              Number of atoms          :   89 ( 209 expanded)
%              Number of equality atoms :   31 (  78 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_43,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_42,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_301,plain,(
    ! [A_60,B_61] :
      ( k4_xboole_0(A_60,B_61) = k3_subset_1(A_60,B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_305,plain,(
    k4_xboole_0('#skF_4','#skF_6') = k3_subset_1('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_301])).

tff(c_30,plain,(
    ! [A_13,C_15,B_14] :
      ( r1_xboole_0(A_13,C_15)
      | ~ r1_tarski(A_13,k4_xboole_0(B_14,C_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_354,plain,(
    ! [A_64] :
      ( r1_xboole_0(A_64,'#skF_6')
      | ~ r1_tarski(A_64,k3_subset_1('#skF_4','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_30])).

tff(c_373,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_354])).

tff(c_26,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_36,plain,(
    ! [A_18,B_19,C_20] :
      ( r1_tarski(A_18,k4_xboole_0(B_19,C_20))
      | ~ r1_xboole_0(A_18,C_20)
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_87,plain,(
    ! [A_33,B_34,C_35] :
      ( r1_tarski(A_33,B_34)
      | ~ r1_tarski(A_33,k4_xboole_0(B_34,C_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_92,plain,(
    ! [B_34,C_35] : r1_tarski(k4_xboole_0(B_34,C_35),B_34) ),
    inference(resolution,[status(thm)],[c_26,c_87])).

tff(c_123,plain,(
    ! [B_41,A_42] :
      ( B_41 = A_42
      | ~ r1_tarski(B_41,A_42)
      | ~ r1_tarski(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_802,plain,(
    ! [B_89,C_90] :
      ( k4_xboole_0(B_89,C_90) = B_89
      | ~ r1_tarski(B_89,k4_xboole_0(B_89,C_90)) ) ),
    inference(resolution,[status(thm)],[c_92,c_123])).

tff(c_815,plain,(
    ! [B_19,C_20] :
      ( k4_xboole_0(B_19,C_20) = B_19
      | ~ r1_xboole_0(B_19,C_20)
      | ~ r1_tarski(B_19,B_19) ) ),
    inference(resolution,[status(thm)],[c_36,c_802])).

tff(c_827,plain,(
    ! [B_93,C_94] :
      ( k4_xboole_0(B_93,C_94) = B_93
      | ~ r1_xboole_0(B_93,C_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_815])).

tff(c_867,plain,(
    k4_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_373,c_827])).

tff(c_32,plain,(
    ! [A_13,B_14,C_15] :
      ( r1_tarski(A_13,B_14)
      | ~ r1_tarski(A_13,k4_xboole_0(B_14,C_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_382,plain,(
    ! [A_66] :
      ( r1_tarski(A_66,'#skF_4')
      | ~ r1_tarski(A_66,k3_subset_1('#skF_4','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_32])).

tff(c_401,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_382])).

tff(c_34,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_440,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_401,c_34])).

tff(c_28,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_444,plain,(
    k5_xboole_0('#skF_5','#skF_5') = k4_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_28])).

tff(c_44,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_50,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = A_25
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_62,plain,(
    k3_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_44,c_50])).

tff(c_151,plain,(
    ! [A_49,B_50] : k5_xboole_0(A_49,k3_xboole_0(A_49,B_50)) = k4_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_163,plain,(
    k5_xboole_0('#skF_5','#skF_5') = k4_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_151])).

tff(c_455,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k4_xboole_0('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_163])).

tff(c_872,plain,(
    k4_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_867,c_455])).

tff(c_61,plain,(
    ! [B_10] : k3_xboole_0(B_10,B_10) = B_10 ),
    inference(resolution,[status(thm)],[c_26,c_50])).

tff(c_173,plain,(
    ! [B_51] : k5_xboole_0(B_51,B_51) = k4_xboole_0(B_51,B_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_151])).

tff(c_179,plain,(
    k4_xboole_0('#skF_5','#skF_5') = k4_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_163])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_200,plain,(
    ! [D_6] :
      ( ~ r2_hidden(D_6,'#skF_5')
      | ~ r2_hidden(D_6,k4_xboole_0('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_4])).

tff(c_467,plain,(
    ! [D_6] :
      ( ~ r2_hidden(D_6,'#skF_5')
      | ~ r2_hidden(D_6,k4_xboole_0('#skF_5','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_200])).

tff(c_1132,plain,(
    ! [D_106] :
      ( ~ r2_hidden(D_106,'#skF_5')
      | ~ r2_hidden(D_106,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_872,c_467])).

tff(c_1139,plain,
    ( ~ r2_hidden('#skF_3'('#skF_5'),'#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_20,c_1132])).

tff(c_1143,plain,(
    ~ r2_hidden('#skF_3'('#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1139])).

tff(c_1146,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_20,c_1143])).

tff(c_1150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1146])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:48:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.45  
% 2.87/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.45  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.87/1.45  
% 2.87/1.45  %Foreground sorts:
% 2.87/1.45  
% 2.87/1.45  
% 2.87/1.45  %Background operators:
% 2.87/1.45  
% 2.87/1.45  
% 2.87/1.45  %Foreground operators:
% 2.87/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.87/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.87/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.87/1.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.87/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.87/1.45  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.87/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.87/1.45  tff('#skF_6', type, '#skF_6': $i).
% 2.87/1.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.87/1.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.87/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.87/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.87/1.45  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.87/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.87/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.87/1.45  
% 3.21/1.47  tff(f_80, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 3.21/1.47  tff(f_43, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.21/1.47  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.21/1.47  tff(f_57, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.21/1.47  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.21/1.47  tff(f_67, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 3.21/1.47  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.21/1.47  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.21/1.47  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.21/1.47  tff(c_40, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.21/1.47  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.21/1.47  tff(c_42, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.21/1.47  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.21/1.47  tff(c_301, plain, (![A_60, B_61]: (k4_xboole_0(A_60, B_61)=k3_subset_1(A_60, B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.21/1.47  tff(c_305, plain, (k4_xboole_0('#skF_4', '#skF_6')=k3_subset_1('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_46, c_301])).
% 3.21/1.47  tff(c_30, plain, (![A_13, C_15, B_14]: (r1_xboole_0(A_13, C_15) | ~r1_tarski(A_13, k4_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.21/1.47  tff(c_354, plain, (![A_64]: (r1_xboole_0(A_64, '#skF_6') | ~r1_tarski(A_64, k3_subset_1('#skF_4', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_305, c_30])).
% 3.21/1.47  tff(c_373, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_42, c_354])).
% 3.21/1.47  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.21/1.47  tff(c_36, plain, (![A_18, B_19, C_20]: (r1_tarski(A_18, k4_xboole_0(B_19, C_20)) | ~r1_xboole_0(A_18, C_20) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.21/1.47  tff(c_87, plain, (![A_33, B_34, C_35]: (r1_tarski(A_33, B_34) | ~r1_tarski(A_33, k4_xboole_0(B_34, C_35)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.21/1.47  tff(c_92, plain, (![B_34, C_35]: (r1_tarski(k4_xboole_0(B_34, C_35), B_34))), inference(resolution, [status(thm)], [c_26, c_87])).
% 3.21/1.47  tff(c_123, plain, (![B_41, A_42]: (B_41=A_42 | ~r1_tarski(B_41, A_42) | ~r1_tarski(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.21/1.47  tff(c_802, plain, (![B_89, C_90]: (k4_xboole_0(B_89, C_90)=B_89 | ~r1_tarski(B_89, k4_xboole_0(B_89, C_90)))), inference(resolution, [status(thm)], [c_92, c_123])).
% 3.21/1.47  tff(c_815, plain, (![B_19, C_20]: (k4_xboole_0(B_19, C_20)=B_19 | ~r1_xboole_0(B_19, C_20) | ~r1_tarski(B_19, B_19))), inference(resolution, [status(thm)], [c_36, c_802])).
% 3.21/1.47  tff(c_827, plain, (![B_93, C_94]: (k4_xboole_0(B_93, C_94)=B_93 | ~r1_xboole_0(B_93, C_94))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_815])).
% 3.21/1.47  tff(c_867, plain, (k4_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_373, c_827])).
% 3.21/1.47  tff(c_32, plain, (![A_13, B_14, C_15]: (r1_tarski(A_13, B_14) | ~r1_tarski(A_13, k4_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.21/1.47  tff(c_382, plain, (![A_66]: (r1_tarski(A_66, '#skF_4') | ~r1_tarski(A_66, k3_subset_1('#skF_4', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_305, c_32])).
% 3.21/1.47  tff(c_401, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_382])).
% 3.21/1.47  tff(c_34, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.21/1.47  tff(c_440, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_401, c_34])).
% 3.21/1.47  tff(c_28, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.21/1.47  tff(c_444, plain, (k5_xboole_0('#skF_5', '#skF_5')=k4_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_440, c_28])).
% 3.21/1.47  tff(c_44, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.21/1.47  tff(c_50, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=A_25 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.21/1.47  tff(c_62, plain, (k3_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_44, c_50])).
% 3.21/1.47  tff(c_151, plain, (![A_49, B_50]: (k5_xboole_0(A_49, k3_xboole_0(A_49, B_50))=k4_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.21/1.47  tff(c_163, plain, (k5_xboole_0('#skF_5', '#skF_5')=k4_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_62, c_151])).
% 3.21/1.47  tff(c_455, plain, (k4_xboole_0('#skF_5', '#skF_6')=k4_xboole_0('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_444, c_163])).
% 3.21/1.47  tff(c_872, plain, (k4_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_867, c_455])).
% 3.21/1.47  tff(c_61, plain, (![B_10]: (k3_xboole_0(B_10, B_10)=B_10)), inference(resolution, [status(thm)], [c_26, c_50])).
% 3.21/1.47  tff(c_173, plain, (![B_51]: (k5_xboole_0(B_51, B_51)=k4_xboole_0(B_51, B_51))), inference(superposition, [status(thm), theory('equality')], [c_61, c_151])).
% 3.21/1.47  tff(c_179, plain, (k4_xboole_0('#skF_5', '#skF_5')=k4_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_173, c_163])).
% 3.21/1.47  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.21/1.47  tff(c_200, plain, (![D_6]: (~r2_hidden(D_6, '#skF_5') | ~r2_hidden(D_6, k4_xboole_0('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_179, c_4])).
% 3.21/1.47  tff(c_467, plain, (![D_6]: (~r2_hidden(D_6, '#skF_5') | ~r2_hidden(D_6, k4_xboole_0('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_455, c_200])).
% 3.21/1.47  tff(c_1132, plain, (![D_106]: (~r2_hidden(D_106, '#skF_5') | ~r2_hidden(D_106, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_872, c_467])).
% 3.21/1.47  tff(c_1139, plain, (~r2_hidden('#skF_3'('#skF_5'), '#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_20, c_1132])).
% 3.21/1.47  tff(c_1143, plain, (~r2_hidden('#skF_3'('#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_40, c_1139])).
% 3.21/1.47  tff(c_1146, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_20, c_1143])).
% 3.21/1.47  tff(c_1150, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_1146])).
% 3.21/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.47  
% 3.21/1.47  Inference rules
% 3.21/1.47  ----------------------
% 3.21/1.47  #Ref     : 0
% 3.21/1.47  #Sup     : 275
% 3.21/1.47  #Fact    : 0
% 3.21/1.47  #Define  : 0
% 3.21/1.47  #Split   : 3
% 3.21/1.47  #Chain   : 0
% 3.21/1.47  #Close   : 0
% 3.21/1.47  
% 3.21/1.47  Ordering : KBO
% 3.21/1.47  
% 3.21/1.47  Simplification rules
% 3.21/1.47  ----------------------
% 3.21/1.47  #Subsume      : 17
% 3.21/1.47  #Demod        : 103
% 3.21/1.47  #Tautology    : 125
% 3.21/1.47  #SimpNegUnit  : 3
% 3.21/1.47  #BackRed      : 21
% 3.21/1.47  
% 3.21/1.47  #Partial instantiations: 0
% 3.21/1.47  #Strategies tried      : 1
% 3.21/1.47  
% 3.21/1.47  Timing (in seconds)
% 3.21/1.47  ----------------------
% 3.21/1.47  Preprocessing        : 0.30
% 3.21/1.47  Parsing              : 0.16
% 3.21/1.47  CNF conversion       : 0.02
% 3.21/1.47  Main loop            : 0.41
% 3.21/1.47  Inferencing          : 0.15
% 3.21/1.47  Reduction            : 0.13
% 3.21/1.47  Demodulation         : 0.09
% 3.21/1.47  BG Simplification    : 0.02
% 3.21/1.47  Subsumption          : 0.08
% 3.21/1.47  Abstraction          : 0.02
% 3.21/1.47  MUC search           : 0.00
% 3.21/1.47  Cooper               : 0.00
% 3.21/1.47  Total                : 0.75
% 3.21/1.47  Index Insertion      : 0.00
% 3.21/1.47  Index Deletion       : 0.00
% 3.21/1.48  Index Matching       : 0.00
% 3.21/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
