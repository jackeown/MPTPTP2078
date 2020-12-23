%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:40 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   62 (  70 expanded)
%              Number of leaves         :   34 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   61 (  71 expanded)
%              Number of equality atoms :   27 (  34 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff(f_65,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_50,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_70,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_67,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_40,plain,(
    ! [A_26] : k2_subset_1(A_26) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_48,plain,(
    k4_subset_1('#skF_3','#skF_4',k2_subset_1('#skF_3')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_51,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_48])).

tff(c_10,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_121,plain,(
    ! [A_44,B_45] : k3_tarski(k2_tarski(A_44,B_45)) = k2_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_164,plain,(
    ! [A_56,B_57] : k3_tarski(k2_tarski(A_56,B_57)) = k2_xboole_0(B_57,A_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_121])).

tff(c_30,plain,(
    ! [A_22,B_23] : k3_tarski(k2_tarski(A_22,B_23)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_170,plain,(
    ! [B_57,A_56] : k2_xboole_0(B_57,A_56) = k2_xboole_0(A_56,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_30])).

tff(c_6,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_44,plain,(
    ! [A_28] : ~ v1_xboole_0(k1_zfmisc_1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_156,plain,(
    ! [B_54,A_55] :
      ( r2_hidden(B_54,A_55)
      | ~ m1_subset_1(B_54,A_55)
      | v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_18,plain,(
    ! [C_21,A_17] :
      ( r1_tarski(C_21,A_17)
      | ~ r2_hidden(C_21,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_160,plain,(
    ! [B_54,A_17] :
      ( r1_tarski(B_54,A_17)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_17))
      | v1_xboole_0(k1_zfmisc_1(A_17)) ) ),
    inference(resolution,[status(thm)],[c_156,c_18])).

tff(c_323,plain,(
    ! [B_68,A_69] :
      ( r1_tarski(B_68,A_69)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_69)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_160])).

tff(c_340,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_323])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_344,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_340,c_4])).

tff(c_8,plain,(
    ! [A_4,B_5] : k2_xboole_0(A_4,k4_xboole_0(B_5,A_4)) = k2_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_353,plain,(
    k2_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_8])).

tff(c_356,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_6,c_353])).

tff(c_42,plain,(
    ! [A_27] : m1_subset_1(k2_subset_1(A_27),k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_52,plain,(
    ! [A_27] : m1_subset_1(A_27,k1_zfmisc_1(A_27)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42])).

tff(c_523,plain,(
    ! [A_94,B_95,C_96] :
      ( k4_subset_1(A_94,B_95,C_96) = k2_xboole_0(B_95,C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(A_94))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_537,plain,(
    ! [A_97,B_98] :
      ( k4_subset_1(A_97,B_98,A_97) = k2_xboole_0(B_98,A_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(A_97)) ) ),
    inference(resolution,[status(thm)],[c_52,c_523])).

tff(c_546,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_537])).

tff(c_552,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_546])).

tff(c_554,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_552])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:18:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.33  
% 2.14/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.33  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.14/1.33  
% 2.14/1.33  %Foreground sorts:
% 2.14/1.33  
% 2.14/1.33  
% 2.14/1.33  %Background operators:
% 2.14/1.33  
% 2.14/1.33  
% 2.14/1.33  %Foreground operators:
% 2.14/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.14/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.14/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.14/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.14/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.14/1.33  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.14/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.14/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.14/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.14/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.14/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.14/1.33  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.14/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.14/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.33  
% 2.54/1.34  tff(f_65, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.54/1.34  tff(f_81, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 2.54/1.34  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.54/1.34  tff(f_50, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.54/1.34  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.54/1.34  tff(f_70, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.54/1.34  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.54/1.34  tff(f_48, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.54/1.34  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.54/1.34  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.54/1.34  tff(f_67, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.54/1.34  tff(f_76, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.54/1.34  tff(c_40, plain, (![A_26]: (k2_subset_1(A_26)=A_26)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.54/1.34  tff(c_48, plain, (k4_subset_1('#skF_3', '#skF_4', k2_subset_1('#skF_3'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.54/1.34  tff(c_51, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_48])).
% 2.54/1.34  tff(c_10, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.54/1.34  tff(c_121, plain, (![A_44, B_45]: (k3_tarski(k2_tarski(A_44, B_45))=k2_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.54/1.34  tff(c_164, plain, (![A_56, B_57]: (k3_tarski(k2_tarski(A_56, B_57))=k2_xboole_0(B_57, A_56))), inference(superposition, [status(thm), theory('equality')], [c_10, c_121])).
% 2.54/1.34  tff(c_30, plain, (![A_22, B_23]: (k3_tarski(k2_tarski(A_22, B_23))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.54/1.34  tff(c_170, plain, (![B_57, A_56]: (k2_xboole_0(B_57, A_56)=k2_xboole_0(A_56, B_57))), inference(superposition, [status(thm), theory('equality')], [c_164, c_30])).
% 2.54/1.34  tff(c_6, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.54/1.34  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.54/1.34  tff(c_44, plain, (![A_28]: (~v1_xboole_0(k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.54/1.34  tff(c_156, plain, (![B_54, A_55]: (r2_hidden(B_54, A_55) | ~m1_subset_1(B_54, A_55) | v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.54/1.34  tff(c_18, plain, (![C_21, A_17]: (r1_tarski(C_21, A_17) | ~r2_hidden(C_21, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.54/1.34  tff(c_160, plain, (![B_54, A_17]: (r1_tarski(B_54, A_17) | ~m1_subset_1(B_54, k1_zfmisc_1(A_17)) | v1_xboole_0(k1_zfmisc_1(A_17)))), inference(resolution, [status(thm)], [c_156, c_18])).
% 2.54/1.34  tff(c_323, plain, (![B_68, A_69]: (r1_tarski(B_68, A_69) | ~m1_subset_1(B_68, k1_zfmisc_1(A_69)))), inference(negUnitSimplification, [status(thm)], [c_44, c_160])).
% 2.54/1.34  tff(c_340, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_323])).
% 2.54/1.34  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.54/1.34  tff(c_344, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_340, c_4])).
% 2.54/1.34  tff(c_8, plain, (![A_4, B_5]: (k2_xboole_0(A_4, k4_xboole_0(B_5, A_4))=k2_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.54/1.34  tff(c_353, plain, (k2_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_344, c_8])).
% 2.54/1.34  tff(c_356, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_170, c_6, c_353])).
% 2.54/1.34  tff(c_42, plain, (![A_27]: (m1_subset_1(k2_subset_1(A_27), k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.54/1.34  tff(c_52, plain, (![A_27]: (m1_subset_1(A_27, k1_zfmisc_1(A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42])).
% 2.54/1.34  tff(c_523, plain, (![A_94, B_95, C_96]: (k4_subset_1(A_94, B_95, C_96)=k2_xboole_0(B_95, C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(A_94)) | ~m1_subset_1(B_95, k1_zfmisc_1(A_94)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.54/1.34  tff(c_537, plain, (![A_97, B_98]: (k4_subset_1(A_97, B_98, A_97)=k2_xboole_0(B_98, A_97) | ~m1_subset_1(B_98, k1_zfmisc_1(A_97)))), inference(resolution, [status(thm)], [c_52, c_523])).
% 2.54/1.34  tff(c_546, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')=k2_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_537])).
% 2.54/1.34  tff(c_552, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_356, c_546])).
% 2.54/1.34  tff(c_554, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_552])).
% 2.54/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.34  
% 2.54/1.34  Inference rules
% 2.54/1.34  ----------------------
% 2.54/1.34  #Ref     : 0
% 2.54/1.34  #Sup     : 112
% 2.54/1.34  #Fact    : 0
% 2.54/1.34  #Define  : 0
% 2.54/1.34  #Split   : 0
% 2.54/1.34  #Chain   : 0
% 2.54/1.34  #Close   : 0
% 2.54/1.34  
% 2.54/1.34  Ordering : KBO
% 2.54/1.34  
% 2.54/1.34  Simplification rules
% 2.54/1.34  ----------------------
% 2.54/1.34  #Subsume      : 7
% 2.54/1.34  #Demod        : 24
% 2.54/1.34  #Tautology    : 73
% 2.54/1.34  #SimpNegUnit  : 3
% 2.54/1.34  #BackRed      : 0
% 2.54/1.34  
% 2.54/1.34  #Partial instantiations: 0
% 2.54/1.34  #Strategies tried      : 1
% 2.54/1.34  
% 2.54/1.34  Timing (in seconds)
% 2.54/1.34  ----------------------
% 2.54/1.35  Preprocessing        : 0.33
% 2.54/1.35  Parsing              : 0.17
% 2.54/1.35  CNF conversion       : 0.02
% 2.54/1.35  Main loop            : 0.26
% 2.54/1.35  Inferencing          : 0.10
% 2.54/1.35  Reduction            : 0.08
% 2.54/1.35  Demodulation         : 0.06
% 2.54/1.35  BG Simplification    : 0.02
% 2.54/1.35  Subsumption          : 0.04
% 2.54/1.35  Abstraction          : 0.02
% 2.54/1.35  MUC search           : 0.00
% 2.54/1.35  Cooper               : 0.00
% 2.54/1.35  Total                : 0.62
% 2.54/1.35  Index Insertion      : 0.00
% 2.54/1.35  Index Deletion       : 0.00
% 2.54/1.35  Index Matching       : 0.00
% 2.54/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
