%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:38 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   65 (  73 expanded)
%              Number of leaves         :   35 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   64 (  74 expanded)
%              Number of equality atoms :   28 (  35 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_75,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_55,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_53,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_72,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_36,plain,(
    ! [A_43] : k2_subset_1(A_43) = A_43 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_44,plain,(
    k4_subset_1('#skF_1','#skF_2',k2_subset_1('#skF_1')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_47,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_36,c_44])).

tff(c_46,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_40,plain,(
    ! [A_45] : ~ v1_xboole_0(k1_zfmisc_1(A_45)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_30,plain,(
    ! [B_42,A_41] :
      ( r2_hidden(B_42,A_41)
      | ~ m1_subset_1(B_42,A_41)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26,plain,(
    ! [A_40] : k3_tarski(k1_zfmisc_1(A_40)) = A_40 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_204,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(A_69,k3_tarski(B_70))
      | ~ r2_hidden(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_289,plain,(
    ! [A_79,A_80] :
      ( r1_tarski(A_79,A_80)
      | ~ r2_hidden(A_79,k1_zfmisc_1(A_80)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_204])).

tff(c_293,plain,(
    ! [B_42,A_80] :
      ( r1_tarski(B_42,A_80)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_80))
      | v1_xboole_0(k1_zfmisc_1(A_80)) ) ),
    inference(resolution,[status(thm)],[c_30,c_289])).

tff(c_297,plain,(
    ! [B_81,A_82] :
      ( r1_tarski(B_81,A_82)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_82)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_293])).

tff(c_310,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_297])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_324,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_310,c_6])).

tff(c_111,plain,(
    ! [B_57,A_58] : k3_xboole_0(B_57,A_58) = k3_xboole_0(A_58,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_126,plain,(
    ! [A_58,B_57] : k2_xboole_0(A_58,k3_xboole_0(B_57,A_58)) = A_58 ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_4])).

tff(c_343,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_126])).

tff(c_8,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_189,plain,(
    ! [A_67,B_68] : k3_tarski(k2_tarski(A_67,B_68)) = k2_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_228,plain,(
    ! [A_73,B_74] : k3_tarski(k2_tarski(A_73,B_74)) = k2_xboole_0(B_74,A_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_189])).

tff(c_24,plain,(
    ! [A_38,B_39] : k3_tarski(k2_tarski(A_38,B_39)) = k2_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_237,plain,(
    ! [B_74,A_73] : k2_xboole_0(B_74,A_73) = k2_xboole_0(A_73,B_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_24])).

tff(c_38,plain,(
    ! [A_44] : m1_subset_1(k2_subset_1(A_44),k1_zfmisc_1(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_48,plain,(
    ! [A_44] : m1_subset_1(A_44,k1_zfmisc_1(A_44)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38])).

tff(c_791,plain,(
    ! [A_136,B_137,C_138] :
      ( k4_subset_1(A_136,B_137,C_138) = k2_xboole_0(B_137,C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(A_136))
      | ~ m1_subset_1(B_137,k1_zfmisc_1(A_136)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_802,plain,(
    ! [A_139,B_140] :
      ( k4_subset_1(A_139,B_140,A_139) = k2_xboole_0(B_140,A_139)
      | ~ m1_subset_1(B_140,k1_zfmisc_1(A_139)) ) ),
    inference(resolution,[status(thm)],[c_48,c_791])).

tff(c_809,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = k2_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_802])).

tff(c_814,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_237,c_809])).

tff(c_816,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_814])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:23:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.48  
% 2.90/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.48  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.90/1.48  
% 2.90/1.48  %Foreground sorts:
% 2.90/1.48  
% 2.90/1.48  
% 2.90/1.48  %Background operators:
% 2.90/1.48  
% 2.90/1.48  
% 2.90/1.48  %Foreground operators:
% 2.90/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.90/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.90/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.90/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.90/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.90/1.48  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.90/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.90/1.48  tff('#skF_2', type, '#skF_2': $i).
% 2.90/1.48  tff('#skF_1', type, '#skF_1': $i).
% 2.90/1.48  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.90/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.90/1.48  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.90/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.48  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.90/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.90/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.90/1.48  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.90/1.48  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.90/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.90/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.90/1.48  
% 3.00/1.50  tff(f_70, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.00/1.50  tff(f_86, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 3.00/1.50  tff(f_75, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.00/1.50  tff(f_68, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.00/1.50  tff(f_55, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 3.00/1.50  tff(f_51, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 3.00/1.50  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.00/1.50  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.00/1.50  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 3.00/1.50  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.00/1.50  tff(f_53, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.00/1.50  tff(f_72, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.00/1.50  tff(f_81, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.00/1.50  tff(c_36, plain, (![A_43]: (k2_subset_1(A_43)=A_43)), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.00/1.50  tff(c_44, plain, (k4_subset_1('#skF_1', '#skF_2', k2_subset_1('#skF_1'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.00/1.50  tff(c_47, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_36, c_44])).
% 3.00/1.50  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.00/1.50  tff(c_40, plain, (![A_45]: (~v1_xboole_0(k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.00/1.50  tff(c_30, plain, (![B_42, A_41]: (r2_hidden(B_42, A_41) | ~m1_subset_1(B_42, A_41) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.00/1.50  tff(c_26, plain, (![A_40]: (k3_tarski(k1_zfmisc_1(A_40))=A_40)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.00/1.50  tff(c_204, plain, (![A_69, B_70]: (r1_tarski(A_69, k3_tarski(B_70)) | ~r2_hidden(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.00/1.50  tff(c_289, plain, (![A_79, A_80]: (r1_tarski(A_79, A_80) | ~r2_hidden(A_79, k1_zfmisc_1(A_80)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_204])).
% 3.00/1.50  tff(c_293, plain, (![B_42, A_80]: (r1_tarski(B_42, A_80) | ~m1_subset_1(B_42, k1_zfmisc_1(A_80)) | v1_xboole_0(k1_zfmisc_1(A_80)))), inference(resolution, [status(thm)], [c_30, c_289])).
% 3.00/1.50  tff(c_297, plain, (![B_81, A_82]: (r1_tarski(B_81, A_82) | ~m1_subset_1(B_81, k1_zfmisc_1(A_82)))), inference(negUnitSimplification, [status(thm)], [c_40, c_293])).
% 3.00/1.50  tff(c_310, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_297])).
% 3.00/1.50  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.00/1.50  tff(c_324, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_310, c_6])).
% 3.00/1.50  tff(c_111, plain, (![B_57, A_58]: (k3_xboole_0(B_57, A_58)=k3_xboole_0(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.00/1.50  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k3_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.00/1.50  tff(c_126, plain, (![A_58, B_57]: (k2_xboole_0(A_58, k3_xboole_0(B_57, A_58))=A_58)), inference(superposition, [status(thm), theory('equality')], [c_111, c_4])).
% 3.00/1.50  tff(c_343, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_324, c_126])).
% 3.00/1.50  tff(c_8, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.00/1.50  tff(c_189, plain, (![A_67, B_68]: (k3_tarski(k2_tarski(A_67, B_68))=k2_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.00/1.50  tff(c_228, plain, (![A_73, B_74]: (k3_tarski(k2_tarski(A_73, B_74))=k2_xboole_0(B_74, A_73))), inference(superposition, [status(thm), theory('equality')], [c_8, c_189])).
% 3.00/1.50  tff(c_24, plain, (![A_38, B_39]: (k3_tarski(k2_tarski(A_38, B_39))=k2_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.00/1.50  tff(c_237, plain, (![B_74, A_73]: (k2_xboole_0(B_74, A_73)=k2_xboole_0(A_73, B_74))), inference(superposition, [status(thm), theory('equality')], [c_228, c_24])).
% 3.00/1.50  tff(c_38, plain, (![A_44]: (m1_subset_1(k2_subset_1(A_44), k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.00/1.50  tff(c_48, plain, (![A_44]: (m1_subset_1(A_44, k1_zfmisc_1(A_44)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38])).
% 3.00/1.50  tff(c_791, plain, (![A_136, B_137, C_138]: (k4_subset_1(A_136, B_137, C_138)=k2_xboole_0(B_137, C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(A_136)) | ~m1_subset_1(B_137, k1_zfmisc_1(A_136)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.00/1.50  tff(c_802, plain, (![A_139, B_140]: (k4_subset_1(A_139, B_140, A_139)=k2_xboole_0(B_140, A_139) | ~m1_subset_1(B_140, k1_zfmisc_1(A_139)))), inference(resolution, [status(thm)], [c_48, c_791])).
% 3.00/1.50  tff(c_809, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')=k2_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_802])).
% 3.00/1.50  tff(c_814, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_343, c_237, c_809])).
% 3.00/1.50  tff(c_816, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_814])).
% 3.00/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.50  
% 3.00/1.50  Inference rules
% 3.00/1.50  ----------------------
% 3.00/1.50  #Ref     : 0
% 3.00/1.50  #Sup     : 182
% 3.00/1.50  #Fact    : 0
% 3.00/1.50  #Define  : 0
% 3.00/1.50  #Split   : 0
% 3.00/1.50  #Chain   : 0
% 3.00/1.50  #Close   : 0
% 3.00/1.50  
% 3.00/1.50  Ordering : KBO
% 3.00/1.50  
% 3.00/1.50  Simplification rules
% 3.00/1.50  ----------------------
% 3.00/1.50  #Subsume      : 29
% 3.00/1.50  #Demod        : 38
% 3.00/1.50  #Tautology    : 108
% 3.00/1.50  #SimpNegUnit  : 6
% 3.00/1.50  #BackRed      : 0
% 3.00/1.50  
% 3.00/1.50  #Partial instantiations: 0
% 3.00/1.50  #Strategies tried      : 1
% 3.00/1.50  
% 3.00/1.50  Timing (in seconds)
% 3.00/1.50  ----------------------
% 3.00/1.50  Preprocessing        : 0.32
% 3.00/1.50  Parsing              : 0.17
% 3.00/1.50  CNF conversion       : 0.02
% 3.00/1.50  Main loop            : 0.39
% 3.00/1.50  Inferencing          : 0.16
% 3.00/1.50  Reduction            : 0.13
% 3.00/1.50  Demodulation         : 0.10
% 3.00/1.50  BG Simplification    : 0.02
% 3.00/1.50  Subsumption          : 0.06
% 3.00/1.50  Abstraction          : 0.02
% 3.00/1.50  MUC search           : 0.00
% 3.00/1.50  Cooper               : 0.00
% 3.00/1.50  Total                : 0.75
% 3.00/1.50  Index Insertion      : 0.00
% 3.00/1.50  Index Deletion       : 0.00
% 3.00/1.50  Index Matching       : 0.00
% 3.00/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
