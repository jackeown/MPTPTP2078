%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:35 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :   63 (  81 expanded)
%              Number of leaves         :   30 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   80 ( 121 expanded)
%              Number of equality atoms :   26 (  32 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_59,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_70,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_32,plain,(
    ! [A_18] : k2_subset_1(A_18) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_42,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_45,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_42])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_38,plain,(
    ! [A_23] : ~ v1_xboole_0(k1_zfmisc_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_127,plain,(
    ! [B_47,A_48] :
      ( r2_hidden(B_47,A_48)
      | ~ m1_subset_1(B_47,A_48)
      | v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    ! [C_15,A_11] :
      ( r1_tarski(C_15,A_11)
      | ~ r2_hidden(C_15,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_134,plain,(
    ! [B_47,A_11] :
      ( r1_tarski(B_47,A_11)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_11))
      | v1_xboole_0(k1_zfmisc_1(A_11)) ) ),
    inference(resolution,[status(thm)],[c_127,c_12])).

tff(c_139,plain,(
    ! [B_49,A_50] :
      ( r1_tarski(B_49,A_50)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_134])).

tff(c_152,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_139])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_171,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_152,c_6])).

tff(c_290,plain,(
    ! [A_63,B_64] :
      ( k4_xboole_0(A_63,B_64) = k3_subset_1(A_63,B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_307,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_290])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_153,plain,(
    ! [A_51,B_52] : k2_xboole_0(k3_xboole_0(A_51,B_52),k4_xboole_0(A_51,B_52)) = A_51 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_162,plain,(
    ! [B_2,A_1] : k2_xboole_0(k3_xboole_0(B_2,A_1),k4_xboole_0(A_1,B_2)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_153])).

tff(c_313,plain,(
    k2_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_162])).

tff(c_322,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_313])).

tff(c_270,plain,(
    ! [A_59,B_60] :
      ( m1_subset_1(k3_subset_1(A_59,B_60),k1_zfmisc_1(A_59))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_138,plain,(
    ! [B_47,A_11] :
      ( r1_tarski(B_47,A_11)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_11)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_134])).

tff(c_277,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(k3_subset_1(A_59,B_60),A_59)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(resolution,[status(thm)],[c_270,c_138])).

tff(c_14,plain,(
    ! [C_15,A_11] :
      ( r2_hidden(C_15,k1_zfmisc_1(A_11))
      | ~ r1_tarski(C_15,A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_106,plain,(
    ! [B_41,A_42] :
      ( m1_subset_1(B_41,A_42)
      | ~ r2_hidden(B_41,A_42)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_109,plain,(
    ! [C_15,A_11] :
      ( m1_subset_1(C_15,k1_zfmisc_1(A_11))
      | v1_xboole_0(k1_zfmisc_1(A_11))
      | ~ r1_tarski(C_15,A_11) ) ),
    inference(resolution,[status(thm)],[c_14,c_106])).

tff(c_112,plain,(
    ! [C_15,A_11] :
      ( m1_subset_1(C_15,k1_zfmisc_1(A_11))
      | ~ r1_tarski(C_15,A_11) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_109])).

tff(c_488,plain,(
    ! [A_81,B_82,C_83] :
      ( k4_subset_1(A_81,B_82,C_83) = k2_xboole_0(B_82,C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(A_81))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_656,plain,(
    ! [A_94,B_95,C_96] :
      ( k4_subset_1(A_94,B_95,C_96) = k2_xboole_0(B_95,C_96)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_94))
      | ~ r1_tarski(C_96,A_94) ) ),
    inference(resolution,[status(thm)],[c_112,c_488])).

tff(c_734,plain,(
    ! [C_99] :
      ( k4_subset_1('#skF_3','#skF_4',C_99) = k2_xboole_0('#skF_4',C_99)
      | ~ r1_tarski(C_99,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_656])).

tff(c_905,plain,(
    ! [B_113] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_113)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_113))
      | ~ m1_subset_1(B_113,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_277,c_734])).

tff(c_928,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_905])).

tff(c_939,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_928])).

tff(c_941,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_939])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:44:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.44  
% 2.71/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.44  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.71/1.44  
% 2.71/1.44  %Foreground sorts:
% 2.71/1.44  
% 2.71/1.44  
% 2.71/1.44  %Background operators:
% 2.71/1.44  
% 2.71/1.44  
% 2.71/1.44  %Foreground operators:
% 2.71/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.71/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.71/1.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.71/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.44  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.71/1.44  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.71/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.71/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.71/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.71/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.71/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.71/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.71/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.71/1.44  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.71/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.71/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.71/1.44  
% 2.95/1.45  tff(f_59, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.95/1.45  tff(f_81, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 2.95/1.45  tff(f_70, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.95/1.45  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.95/1.45  tff(f_44, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.95/1.45  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.95/1.45  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.95/1.45  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.95/1.45  tff(f_35, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.95/1.45  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.95/1.45  tff(f_76, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.95/1.45  tff(c_32, plain, (![A_18]: (k2_subset_1(A_18)=A_18)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.95/1.45  tff(c_42, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.95/1.45  tff(c_45, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_42])).
% 2.95/1.45  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.95/1.45  tff(c_38, plain, (![A_23]: (~v1_xboole_0(k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.95/1.45  tff(c_127, plain, (![B_47, A_48]: (r2_hidden(B_47, A_48) | ~m1_subset_1(B_47, A_48) | v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.95/1.45  tff(c_12, plain, (![C_15, A_11]: (r1_tarski(C_15, A_11) | ~r2_hidden(C_15, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.95/1.45  tff(c_134, plain, (![B_47, A_11]: (r1_tarski(B_47, A_11) | ~m1_subset_1(B_47, k1_zfmisc_1(A_11)) | v1_xboole_0(k1_zfmisc_1(A_11)))), inference(resolution, [status(thm)], [c_127, c_12])).
% 2.95/1.45  tff(c_139, plain, (![B_49, A_50]: (r1_tarski(B_49, A_50) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)))), inference(negUnitSimplification, [status(thm)], [c_38, c_134])).
% 2.95/1.45  tff(c_152, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_139])).
% 2.95/1.45  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.95/1.45  tff(c_171, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_152, c_6])).
% 2.95/1.45  tff(c_290, plain, (![A_63, B_64]: (k4_xboole_0(A_63, B_64)=k3_subset_1(A_63, B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.95/1.45  tff(c_307, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_290])).
% 2.95/1.45  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.95/1.45  tff(c_153, plain, (![A_51, B_52]: (k2_xboole_0(k3_xboole_0(A_51, B_52), k4_xboole_0(A_51, B_52))=A_51)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.95/1.45  tff(c_162, plain, (![B_2, A_1]: (k2_xboole_0(k3_xboole_0(B_2, A_1), k4_xboole_0(A_1, B_2))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_153])).
% 2.95/1.45  tff(c_313, plain, (k2_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_307, c_162])).
% 2.95/1.45  tff(c_322, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_171, c_313])).
% 2.95/1.45  tff(c_270, plain, (![A_59, B_60]: (m1_subset_1(k3_subset_1(A_59, B_60), k1_zfmisc_1(A_59)) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.95/1.45  tff(c_138, plain, (![B_47, A_11]: (r1_tarski(B_47, A_11) | ~m1_subset_1(B_47, k1_zfmisc_1(A_11)))), inference(negUnitSimplification, [status(thm)], [c_38, c_134])).
% 2.95/1.45  tff(c_277, plain, (![A_59, B_60]: (r1_tarski(k3_subset_1(A_59, B_60), A_59) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(resolution, [status(thm)], [c_270, c_138])).
% 2.95/1.45  tff(c_14, plain, (![C_15, A_11]: (r2_hidden(C_15, k1_zfmisc_1(A_11)) | ~r1_tarski(C_15, A_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.95/1.45  tff(c_106, plain, (![B_41, A_42]: (m1_subset_1(B_41, A_42) | ~r2_hidden(B_41, A_42) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.95/1.45  tff(c_109, plain, (![C_15, A_11]: (m1_subset_1(C_15, k1_zfmisc_1(A_11)) | v1_xboole_0(k1_zfmisc_1(A_11)) | ~r1_tarski(C_15, A_11))), inference(resolution, [status(thm)], [c_14, c_106])).
% 2.95/1.45  tff(c_112, plain, (![C_15, A_11]: (m1_subset_1(C_15, k1_zfmisc_1(A_11)) | ~r1_tarski(C_15, A_11))), inference(negUnitSimplification, [status(thm)], [c_38, c_109])).
% 2.95/1.45  tff(c_488, plain, (![A_81, B_82, C_83]: (k4_subset_1(A_81, B_82, C_83)=k2_xboole_0(B_82, C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(A_81)) | ~m1_subset_1(B_82, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.95/1.45  tff(c_656, plain, (![A_94, B_95, C_96]: (k4_subset_1(A_94, B_95, C_96)=k2_xboole_0(B_95, C_96) | ~m1_subset_1(B_95, k1_zfmisc_1(A_94)) | ~r1_tarski(C_96, A_94))), inference(resolution, [status(thm)], [c_112, c_488])).
% 2.95/1.45  tff(c_734, plain, (![C_99]: (k4_subset_1('#skF_3', '#skF_4', C_99)=k2_xboole_0('#skF_4', C_99) | ~r1_tarski(C_99, '#skF_3'))), inference(resolution, [status(thm)], [c_44, c_656])).
% 2.95/1.45  tff(c_905, plain, (![B_113]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_113))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_113)) | ~m1_subset_1(B_113, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_277, c_734])).
% 2.95/1.45  tff(c_928, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_905])).
% 2.95/1.45  tff(c_939, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_322, c_928])).
% 2.95/1.45  tff(c_941, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_939])).
% 2.95/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.45  
% 2.95/1.45  Inference rules
% 2.95/1.45  ----------------------
% 2.95/1.45  #Ref     : 0
% 2.95/1.45  #Sup     : 211
% 2.95/1.45  #Fact    : 0
% 2.95/1.45  #Define  : 0
% 2.95/1.45  #Split   : 0
% 2.95/1.45  #Chain   : 0
% 2.95/1.45  #Close   : 0
% 2.95/1.45  
% 2.95/1.45  Ordering : KBO
% 2.95/1.45  
% 2.95/1.45  Simplification rules
% 2.95/1.45  ----------------------
% 2.95/1.45  #Subsume      : 16
% 2.95/1.45  #Demod        : 47
% 2.95/1.45  #Tautology    : 109
% 2.95/1.45  #SimpNegUnit  : 22
% 2.95/1.45  #BackRed      : 4
% 2.95/1.45  
% 2.95/1.45  #Partial instantiations: 0
% 2.95/1.45  #Strategies tried      : 1
% 2.95/1.45  
% 2.95/1.45  Timing (in seconds)
% 2.95/1.45  ----------------------
% 2.95/1.45  Preprocessing        : 0.30
% 2.95/1.45  Parsing              : 0.16
% 2.95/1.45  CNF conversion       : 0.02
% 2.95/1.45  Main loop            : 0.37
% 2.95/1.45  Inferencing          : 0.14
% 2.95/1.45  Reduction            : 0.11
% 2.95/1.45  Demodulation         : 0.08
% 2.95/1.45  BG Simplification    : 0.02
% 2.95/1.45  Subsumption          : 0.06
% 2.95/1.45  Abstraction          : 0.03
% 2.95/1.46  MUC search           : 0.00
% 2.95/1.46  Cooper               : 0.00
% 2.95/1.46  Total                : 0.70
% 2.95/1.46  Index Insertion      : 0.00
% 2.95/1.46  Index Deletion       : 0.00
% 2.95/1.46  Index Matching       : 0.00
% 2.95/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
