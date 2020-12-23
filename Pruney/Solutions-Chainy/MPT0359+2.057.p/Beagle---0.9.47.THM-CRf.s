%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:16 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 186 expanded)
%              Number of leaves         :   28 (  71 expanded)
%              Depth                    :   10
%              Number of atoms          :  105 ( 296 expanded)
%              Number of equality atoms :   32 ( 121 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_57,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_67,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    ! [A_13] : k1_subset_1(A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_30,plain,(
    ! [A_14] : k2_subset_1(A_14) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_36,plain,(
    ! [A_19] : k3_subset_1(A_19,k1_subset_1(A_19)) = k2_subset_1(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_52,plain,(
    ! [A_19] : k3_subset_1(A_19,k1_subset_1(A_19)) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_36])).

tff(c_56,plain,(
    ! [A_19] : k3_subset_1(A_19,k1_xboole_0) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_52])).

tff(c_10,plain,(
    ! [C_10,A_6] :
      ( r2_hidden(C_10,k1_zfmisc_1(A_6))
      | ~ r1_tarski(C_10,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_137,plain,(
    ! [B_41,A_42] :
      ( m1_subset_1(B_41,A_42)
      | ~ r2_hidden(B_41,A_42)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_228,plain,(
    ! [C_54,A_55] :
      ( m1_subset_1(C_54,k1_zfmisc_1(A_55))
      | v1_xboole_0(k1_zfmisc_1(A_55))
      | ~ r1_tarski(C_54,A_55) ) ),
    inference(resolution,[status(thm)],[c_10,c_137])).

tff(c_34,plain,(
    ! [A_17,B_18] :
      ( k3_subset_1(A_17,k3_subset_1(A_17,B_18)) = B_18
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_485,plain,(
    ! [A_84,C_85] :
      ( k3_subset_1(A_84,k3_subset_1(A_84,C_85)) = C_85
      | v1_xboole_0(k1_zfmisc_1(A_84))
      | ~ r1_tarski(C_85,A_84) ) ),
    inference(resolution,[status(thm)],[c_228,c_34])).

tff(c_526,plain,(
    ! [A_19] :
      ( k3_subset_1(A_19,A_19) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_19))
      | ~ r1_tarski(k1_xboole_0,A_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_485])).

tff(c_543,plain,(
    ! [A_86] :
      ( k3_subset_1(A_86,A_86) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_86)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_526])).

tff(c_44,plain,
    ( k2_subset_1('#skF_4') != '#skF_5'
    | ~ r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_54,plain,
    ( '#skF_5' != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_44])).

tff(c_92,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_50,plain,
    ( r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_5')
    | k2_subset_1('#skF_4') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_53,plain,
    ( r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_50])).

tff(c_93,plain,(
    '#skF_5' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_53])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_95,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_42])).

tff(c_116,plain,(
    ! [B_35,A_36] :
      ( v1_xboole_0(B_35)
      | ~ m1_subset_1(B_35,A_36)
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_124,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_95,c_116])).

tff(c_125,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_589,plain,(
    k3_subset_1('#skF_4','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_543,c_125])).

tff(c_94,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_93,c_92])).

tff(c_662,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_589,c_94])).

tff(c_665,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_662])).

tff(c_667,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_107,plain,(
    ! [C_33,A_34] :
      ( r2_hidden(C_33,k1_zfmisc_1(A_34))
      | ~ r1_tarski(C_33,A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_678,plain,(
    ! [A_91,C_92] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_91))
      | ~ r1_tarski(C_92,A_91) ) ),
    inference(resolution,[status(thm)],[c_107,c_2])).

tff(c_682,plain,(
    ! [C_93] : ~ r1_tarski(C_93,'#skF_4') ),
    inference(resolution,[status(thm)],[c_667,c_678])).

tff(c_687,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_682])).

tff(c_688,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_32,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k3_subset_1(A_15,B_16),k1_zfmisc_1(A_15))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_689,plain,(
    r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_762,plain,(
    ! [A_113,B_114] :
      ( k3_subset_1(A_113,k3_subset_1(A_113,B_114)) = B_114
      | ~ m1_subset_1(B_114,k1_zfmisc_1(A_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_776,plain,(
    k3_subset_1('#skF_4',k3_subset_1('#skF_4','#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_42,c_762])).

tff(c_40,plain,(
    ! [A_20,B_21] :
      ( k1_subset_1(A_20) = B_21
      | ~ r1_tarski(B_21,k3_subset_1(A_20,B_21))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_824,plain,(
    ! [B_119,A_120] :
      ( k1_xboole_0 = B_119
      | ~ r1_tarski(B_119,k3_subset_1(A_120,B_119))
      | ~ m1_subset_1(B_119,k1_zfmisc_1(A_120)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_40])).

tff(c_827,plain,
    ( k3_subset_1('#skF_4','#skF_5') = k1_xboole_0
    | ~ r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_5')
    | ~ m1_subset_1(k3_subset_1('#skF_4','#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_776,c_824])).

tff(c_836,plain,
    ( k3_subset_1('#skF_4','#skF_5') = k1_xboole_0
    | ~ m1_subset_1(k3_subset_1('#skF_4','#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_689,c_827])).

tff(c_866,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_4','#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_836])).

tff(c_872,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_32,c_866])).

tff(c_882,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_872])).

tff(c_883,plain,(
    k3_subset_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_836])).

tff(c_885,plain,(
    k3_subset_1('#skF_4',k1_xboole_0) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_883,c_776])).

tff(c_887,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_885])).

tff(c_889,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_688,c_887])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:49:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.46  
% 2.71/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.46  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 2.94/1.46  
% 2.94/1.46  %Foreground sorts:
% 2.94/1.46  
% 2.94/1.46  
% 2.94/1.46  %Background operators:
% 2.94/1.46  
% 2.94/1.46  
% 2.94/1.46  %Foreground operators:
% 2.94/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.94/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.94/1.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.94/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.94/1.46  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.94/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.94/1.46  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.94/1.46  tff('#skF_5', type, '#skF_5': $i).
% 2.94/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.94/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.94/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.94/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.94/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.94/1.46  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.94/1.46  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.94/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.94/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.94/1.46  
% 2.95/1.48  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.95/1.48  tff(f_55, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.95/1.48  tff(f_57, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.95/1.48  tff(f_67, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.95/1.48  tff(f_40, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.95/1.48  tff(f_53, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.95/1.48  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.95/1.48  tff(f_80, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 2.95/1.48  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.95/1.48  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.95/1.48  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 2.95/1.48  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.95/1.48  tff(c_28, plain, (![A_13]: (k1_subset_1(A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.95/1.48  tff(c_30, plain, (![A_14]: (k2_subset_1(A_14)=A_14)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.95/1.48  tff(c_36, plain, (![A_19]: (k3_subset_1(A_19, k1_subset_1(A_19))=k2_subset_1(A_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.95/1.48  tff(c_52, plain, (![A_19]: (k3_subset_1(A_19, k1_subset_1(A_19))=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_36])).
% 2.95/1.48  tff(c_56, plain, (![A_19]: (k3_subset_1(A_19, k1_xboole_0)=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_52])).
% 2.95/1.48  tff(c_10, plain, (![C_10, A_6]: (r2_hidden(C_10, k1_zfmisc_1(A_6)) | ~r1_tarski(C_10, A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.95/1.48  tff(c_137, plain, (![B_41, A_42]: (m1_subset_1(B_41, A_42) | ~r2_hidden(B_41, A_42) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.95/1.48  tff(c_228, plain, (![C_54, A_55]: (m1_subset_1(C_54, k1_zfmisc_1(A_55)) | v1_xboole_0(k1_zfmisc_1(A_55)) | ~r1_tarski(C_54, A_55))), inference(resolution, [status(thm)], [c_10, c_137])).
% 2.95/1.48  tff(c_34, plain, (![A_17, B_18]: (k3_subset_1(A_17, k3_subset_1(A_17, B_18))=B_18 | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.95/1.48  tff(c_485, plain, (![A_84, C_85]: (k3_subset_1(A_84, k3_subset_1(A_84, C_85))=C_85 | v1_xboole_0(k1_zfmisc_1(A_84)) | ~r1_tarski(C_85, A_84))), inference(resolution, [status(thm)], [c_228, c_34])).
% 2.95/1.48  tff(c_526, plain, (![A_19]: (k3_subset_1(A_19, A_19)=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_19)) | ~r1_tarski(k1_xboole_0, A_19))), inference(superposition, [status(thm), theory('equality')], [c_56, c_485])).
% 2.95/1.48  tff(c_543, plain, (![A_86]: (k3_subset_1(A_86, A_86)=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_86)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_526])).
% 2.95/1.48  tff(c_44, plain, (k2_subset_1('#skF_4')!='#skF_5' | ~r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.95/1.48  tff(c_54, plain, ('#skF_5'!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_44])).
% 2.95/1.48  tff(c_92, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_54])).
% 2.95/1.48  tff(c_50, plain, (r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_5') | k2_subset_1('#skF_4')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.95/1.48  tff(c_53, plain, (r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_5') | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_50])).
% 2.95/1.48  tff(c_93, plain, ('#skF_5'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_92, c_53])).
% 2.95/1.48  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.95/1.48  tff(c_95, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_42])).
% 2.95/1.48  tff(c_116, plain, (![B_35, A_36]: (v1_xboole_0(B_35) | ~m1_subset_1(B_35, A_36) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.95/1.48  tff(c_124, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_95, c_116])).
% 2.95/1.48  tff(c_125, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_124])).
% 2.95/1.48  tff(c_589, plain, (k3_subset_1('#skF_4', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_543, c_125])).
% 2.95/1.48  tff(c_94, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_93, c_92])).
% 2.95/1.48  tff(c_662, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_589, c_94])).
% 2.95/1.48  tff(c_665, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_662])).
% 2.95/1.48  tff(c_667, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_124])).
% 2.95/1.48  tff(c_107, plain, (![C_33, A_34]: (r2_hidden(C_33, k1_zfmisc_1(A_34)) | ~r1_tarski(C_33, A_34))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.95/1.48  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.95/1.48  tff(c_678, plain, (![A_91, C_92]: (~v1_xboole_0(k1_zfmisc_1(A_91)) | ~r1_tarski(C_92, A_91))), inference(resolution, [status(thm)], [c_107, c_2])).
% 2.95/1.48  tff(c_682, plain, (![C_93]: (~r1_tarski(C_93, '#skF_4'))), inference(resolution, [status(thm)], [c_667, c_678])).
% 2.95/1.48  tff(c_687, plain, $false, inference(resolution, [status(thm)], [c_6, c_682])).
% 2.95/1.48  tff(c_688, plain, ('#skF_5'!='#skF_4'), inference(splitRight, [status(thm)], [c_54])).
% 2.95/1.48  tff(c_32, plain, (![A_15, B_16]: (m1_subset_1(k3_subset_1(A_15, B_16), k1_zfmisc_1(A_15)) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.95/1.48  tff(c_689, plain, (r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_54])).
% 2.95/1.48  tff(c_762, plain, (![A_113, B_114]: (k3_subset_1(A_113, k3_subset_1(A_113, B_114))=B_114 | ~m1_subset_1(B_114, k1_zfmisc_1(A_113)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.95/1.48  tff(c_776, plain, (k3_subset_1('#skF_4', k3_subset_1('#skF_4', '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_42, c_762])).
% 2.95/1.48  tff(c_40, plain, (![A_20, B_21]: (k1_subset_1(A_20)=B_21 | ~r1_tarski(B_21, k3_subset_1(A_20, B_21)) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.95/1.48  tff(c_824, plain, (![B_119, A_120]: (k1_xboole_0=B_119 | ~r1_tarski(B_119, k3_subset_1(A_120, B_119)) | ~m1_subset_1(B_119, k1_zfmisc_1(A_120)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_40])).
% 2.95/1.48  tff(c_827, plain, (k3_subset_1('#skF_4', '#skF_5')=k1_xboole_0 | ~r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_5') | ~m1_subset_1(k3_subset_1('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_776, c_824])).
% 2.95/1.48  tff(c_836, plain, (k3_subset_1('#skF_4', '#skF_5')=k1_xboole_0 | ~m1_subset_1(k3_subset_1('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_689, c_827])).
% 2.95/1.48  tff(c_866, plain, (~m1_subset_1(k3_subset_1('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_836])).
% 2.95/1.48  tff(c_872, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_32, c_866])).
% 2.95/1.48  tff(c_882, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_872])).
% 2.95/1.48  tff(c_883, plain, (k3_subset_1('#skF_4', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_836])).
% 2.95/1.48  tff(c_885, plain, (k3_subset_1('#skF_4', k1_xboole_0)='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_883, c_776])).
% 2.95/1.48  tff(c_887, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_885])).
% 2.95/1.48  tff(c_889, plain, $false, inference(negUnitSimplification, [status(thm)], [c_688, c_887])).
% 2.95/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.48  
% 2.95/1.48  Inference rules
% 2.95/1.48  ----------------------
% 2.95/1.48  #Ref     : 0
% 2.95/1.48  #Sup     : 183
% 2.95/1.48  #Fact    : 0
% 2.95/1.48  #Define  : 0
% 2.95/1.48  #Split   : 6
% 2.95/1.48  #Chain   : 0
% 2.95/1.48  #Close   : 0
% 2.95/1.48  
% 2.95/1.48  Ordering : KBO
% 2.95/1.48  
% 2.95/1.48  Simplification rules
% 2.95/1.48  ----------------------
% 2.95/1.48  #Subsume      : 27
% 2.95/1.48  #Demod        : 53
% 2.95/1.48  #Tautology    : 90
% 2.95/1.48  #SimpNegUnit  : 8
% 2.95/1.48  #BackRed      : 5
% 2.95/1.48  
% 2.95/1.48  #Partial instantiations: 0
% 2.95/1.48  #Strategies tried      : 1
% 2.95/1.48  
% 2.95/1.48  Timing (in seconds)
% 2.95/1.48  ----------------------
% 2.95/1.48  Preprocessing        : 0.29
% 2.95/1.48  Parsing              : 0.16
% 2.95/1.48  CNF conversion       : 0.02
% 2.95/1.48  Main loop            : 0.42
% 2.95/1.48  Inferencing          : 0.16
% 2.95/1.49  Reduction            : 0.12
% 2.95/1.49  Demodulation         : 0.08
% 2.95/1.49  BG Simplification    : 0.02
% 2.95/1.49  Subsumption          : 0.08
% 2.95/1.49  Abstraction          : 0.02
% 2.95/1.49  MUC search           : 0.00
% 2.95/1.49  Cooper               : 0.00
% 2.95/1.49  Total                : 0.75
% 2.95/1.49  Index Insertion      : 0.00
% 2.95/1.49  Index Deletion       : 0.00
% 2.95/1.49  Index Matching       : 0.00
% 2.95/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
