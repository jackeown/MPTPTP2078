%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:28 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 126 expanded)
%              Number of leaves         :   30 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :   63 ( 139 expanded)
%              Number of equality atoms :   40 (  93 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_45,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_18,plain,(
    ! [A_18] : k2_subset_1(A_18) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_31,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_28])).

tff(c_10,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_75,plain,(
    ! [A_33,B_34] : k3_tarski(k2_tarski(A_33,B_34)) = k2_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_122,plain,(
    ! [B_43,A_44] : k3_tarski(k2_tarski(B_43,A_44)) = k2_xboole_0(A_44,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_75])).

tff(c_16,plain,(
    ! [A_16,B_17] : k3_tarski(k2_tarski(A_16,B_17)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_128,plain,(
    ! [B_43,A_44] : k2_xboole_0(B_43,A_44) = k2_xboole_0(A_44,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_16])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_257,plain,(
    ! [A_59,B_60] :
      ( k4_xboole_0(A_59,B_60) = k3_subset_1(A_59,B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_265,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_257])).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_269,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_8])).

tff(c_281,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_269])).

tff(c_145,plain,(
    ! [B_45,A_46] : k2_xboole_0(B_45,A_46) = k2_xboole_0(A_46,B_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_16])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_99,plain,(
    ! [A_37,B_38] :
      ( k2_xboole_0(A_37,B_38) = B_38
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_103,plain,(
    ! [A_5,B_6] : k2_xboole_0(k4_xboole_0(A_5,B_6),A_5) = A_5 ),
    inference(resolution,[status(thm)],[c_6,c_99])).

tff(c_161,plain,(
    ! [B_45,B_6] : k2_xboole_0(B_45,k4_xboole_0(B_45,B_6)) = B_45 ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_103])).

tff(c_272,plain,(
    k2_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_161])).

tff(c_242,plain,(
    ! [A_57,B_58] :
      ( k3_subset_1(A_57,k3_subset_1(A_57,B_58)) = B_58
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_248,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_242])).

tff(c_22,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(k3_subset_1(A_21,B_22),k1_zfmisc_1(A_21))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_392,plain,(
    ! [A_68,B_69] :
      ( k4_xboole_0(A_68,k3_subset_1(A_68,B_69)) = k3_subset_1(A_68,k3_subset_1(A_68,B_69))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(resolution,[status(thm)],[c_22,c_257])).

tff(c_396,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_392])).

tff(c_399,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_396])).

tff(c_403,plain,(
    k2_xboole_0(k3_subset_1('#skF_1','#skF_2'),'#skF_2') = k2_xboole_0(k3_subset_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_8])).

tff(c_415,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_272,c_128,c_128,c_403])).

tff(c_445,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_281])).

tff(c_312,plain,(
    ! [A_61,B_62,C_63] :
      ( k4_subset_1(A_61,B_62,C_63) = k2_xboole_0(B_62,C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(A_61))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_421,plain,(
    ! [A_70,B_71,B_72] :
      ( k4_subset_1(A_70,B_71,k3_subset_1(A_70,B_72)) = k2_xboole_0(B_71,k3_subset_1(A_70,B_72))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_70))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_70)) ) ),
    inference(resolution,[status(thm)],[c_22,c_312])).

tff(c_451,plain,(
    ! [B_73] :
      ( k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1',B_73)) = k2_xboole_0('#skF_2',k3_subset_1('#skF_1',B_73))
      | ~ m1_subset_1(B_73,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_30,c_421])).

tff(c_460,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_451])).

tff(c_512,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_460])).

tff(c_513,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31,c_512])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:36:06 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.30  
% 2.25/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.31  %$ r1_tarski > m1_subset_1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.25/1.31  
% 2.25/1.31  %Foreground sorts:
% 2.25/1.31  
% 2.25/1.31  
% 2.25/1.31  %Background operators:
% 2.25/1.31  
% 2.25/1.31  
% 2.25/1.31  %Foreground operators:
% 2.25/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.25/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.25/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.25/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.25/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.25/1.31  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.25/1.31  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.25/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.25/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.25/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.25/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.25/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.25/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.25/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.25/1.31  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.25/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.25/1.31  
% 2.54/1.32  tff(f_45, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.54/1.32  tff(f_68, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 2.54/1.32  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.54/1.32  tff(f_43, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.54/1.32  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.54/1.32  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.54/1.32  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.54/1.32  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.54/1.32  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.54/1.32  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.54/1.32  tff(f_63, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.54/1.32  tff(c_18, plain, (![A_18]: (k2_subset_1(A_18)=A_18)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.54/1.32  tff(c_28, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.54/1.32  tff(c_31, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_28])).
% 2.54/1.32  tff(c_10, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.54/1.32  tff(c_75, plain, (![A_33, B_34]: (k3_tarski(k2_tarski(A_33, B_34))=k2_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.54/1.32  tff(c_122, plain, (![B_43, A_44]: (k3_tarski(k2_tarski(B_43, A_44))=k2_xboole_0(A_44, B_43))), inference(superposition, [status(thm), theory('equality')], [c_10, c_75])).
% 2.54/1.32  tff(c_16, plain, (![A_16, B_17]: (k3_tarski(k2_tarski(A_16, B_17))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.54/1.32  tff(c_128, plain, (![B_43, A_44]: (k2_xboole_0(B_43, A_44)=k2_xboole_0(A_44, B_43))), inference(superposition, [status(thm), theory('equality')], [c_122, c_16])).
% 2.54/1.32  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.54/1.32  tff(c_257, plain, (![A_59, B_60]: (k4_xboole_0(A_59, B_60)=k3_subset_1(A_59, B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.54/1.32  tff(c_265, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_257])).
% 2.54/1.32  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.54/1.32  tff(c_269, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_265, c_8])).
% 2.54/1.32  tff(c_281, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_269])).
% 2.54/1.32  tff(c_145, plain, (![B_45, A_46]: (k2_xboole_0(B_45, A_46)=k2_xboole_0(A_46, B_45))), inference(superposition, [status(thm), theory('equality')], [c_122, c_16])).
% 2.54/1.32  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.54/1.32  tff(c_99, plain, (![A_37, B_38]: (k2_xboole_0(A_37, B_38)=B_38 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.54/1.32  tff(c_103, plain, (![A_5, B_6]: (k2_xboole_0(k4_xboole_0(A_5, B_6), A_5)=A_5)), inference(resolution, [status(thm)], [c_6, c_99])).
% 2.54/1.32  tff(c_161, plain, (![B_45, B_6]: (k2_xboole_0(B_45, k4_xboole_0(B_45, B_6))=B_45)), inference(superposition, [status(thm), theory('equality')], [c_145, c_103])).
% 2.54/1.32  tff(c_272, plain, (k2_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_265, c_161])).
% 2.54/1.32  tff(c_242, plain, (![A_57, B_58]: (k3_subset_1(A_57, k3_subset_1(A_57, B_58))=B_58 | ~m1_subset_1(B_58, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.54/1.32  tff(c_248, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_30, c_242])).
% 2.54/1.32  tff(c_22, plain, (![A_21, B_22]: (m1_subset_1(k3_subset_1(A_21, B_22), k1_zfmisc_1(A_21)) | ~m1_subset_1(B_22, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.54/1.32  tff(c_392, plain, (![A_68, B_69]: (k4_xboole_0(A_68, k3_subset_1(A_68, B_69))=k3_subset_1(A_68, k3_subset_1(A_68, B_69)) | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(resolution, [status(thm)], [c_22, c_257])).
% 2.54/1.32  tff(c_396, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_392])).
% 2.54/1.32  tff(c_399, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_248, c_396])).
% 2.54/1.32  tff(c_403, plain, (k2_xboole_0(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')=k2_xboole_0(k3_subset_1('#skF_1', '#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_399, c_8])).
% 2.54/1.32  tff(c_415, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_281, c_272, c_128, c_128, c_403])).
% 2.54/1.32  tff(c_445, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_415, c_281])).
% 2.54/1.32  tff(c_312, plain, (![A_61, B_62, C_63]: (k4_subset_1(A_61, B_62, C_63)=k2_xboole_0(B_62, C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(A_61)) | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.54/1.32  tff(c_421, plain, (![A_70, B_71, B_72]: (k4_subset_1(A_70, B_71, k3_subset_1(A_70, B_72))=k2_xboole_0(B_71, k3_subset_1(A_70, B_72)) | ~m1_subset_1(B_71, k1_zfmisc_1(A_70)) | ~m1_subset_1(B_72, k1_zfmisc_1(A_70)))), inference(resolution, [status(thm)], [c_22, c_312])).
% 2.54/1.32  tff(c_451, plain, (![B_73]: (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', B_73))=k2_xboole_0('#skF_2', k3_subset_1('#skF_1', B_73)) | ~m1_subset_1(B_73, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_30, c_421])).
% 2.54/1.32  tff(c_460, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_451])).
% 2.54/1.32  tff(c_512, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_445, c_460])).
% 2.54/1.32  tff(c_513, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31, c_512])).
% 2.54/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.32  
% 2.54/1.32  Inference rules
% 2.54/1.32  ----------------------
% 2.54/1.32  #Ref     : 0
% 2.54/1.32  #Sup     : 127
% 2.54/1.32  #Fact    : 0
% 2.54/1.32  #Define  : 0
% 2.54/1.32  #Split   : 0
% 2.54/1.32  #Chain   : 0
% 2.54/1.32  #Close   : 0
% 2.54/1.32  
% 2.54/1.32  Ordering : KBO
% 2.54/1.32  
% 2.54/1.32  Simplification rules
% 2.54/1.32  ----------------------
% 2.54/1.32  #Subsume      : 2
% 2.54/1.32  #Demod        : 43
% 2.54/1.32  #Tautology    : 91
% 2.54/1.32  #SimpNegUnit  : 1
% 2.54/1.32  #BackRed      : 2
% 2.54/1.32  
% 2.54/1.32  #Partial instantiations: 0
% 2.54/1.32  #Strategies tried      : 1
% 2.54/1.32  
% 2.54/1.32  Timing (in seconds)
% 2.54/1.32  ----------------------
% 2.54/1.32  Preprocessing        : 0.31
% 2.54/1.32  Parsing              : 0.16
% 2.54/1.32  CNF conversion       : 0.02
% 2.54/1.32  Main loop            : 0.27
% 2.54/1.32  Inferencing          : 0.10
% 2.54/1.32  Reduction            : 0.09
% 2.54/1.32  Demodulation         : 0.07
% 2.54/1.32  BG Simplification    : 0.02
% 2.54/1.32  Subsumption          : 0.05
% 2.54/1.32  Abstraction          : 0.02
% 2.54/1.32  MUC search           : 0.00
% 2.54/1.32  Cooper               : 0.00
% 2.54/1.32  Total                : 0.61
% 2.54/1.32  Index Insertion      : 0.00
% 2.54/1.32  Index Deletion       : 0.00
% 2.54/1.32  Index Matching       : 0.00
% 2.54/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
