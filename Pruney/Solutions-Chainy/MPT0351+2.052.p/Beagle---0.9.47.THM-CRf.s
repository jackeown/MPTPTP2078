%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:43 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 100 expanded)
%              Number of leaves         :   34 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :   71 ( 119 expanded)
%              Number of equality atoms :   29 (  50 expanded)
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

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_74,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_76,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_79,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_53,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k4_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_36,plain,(
    ! [A_44] : k2_subset_1(A_44) = A_44 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_38,plain,(
    ! [A_45] : m1_subset_1(k2_subset_1(A_45),k1_zfmisc_1(A_45)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_48,plain,(
    ! [A_45] : m1_subset_1(A_45,k1_zfmisc_1(A_45)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38])).

tff(c_461,plain,(
    ! [A_111,B_112,C_113] :
      ( k4_subset_1(A_111,B_112,C_113) = k2_xboole_0(B_112,C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(A_111))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(A_111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_601,plain,(
    ! [A_129,B_130] :
      ( k4_subset_1(A_129,B_130,A_129) = k2_xboole_0(B_130,A_129)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(A_129)) ) ),
    inference(resolution,[status(thm)],[c_48,c_461])).

tff(c_612,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = k2_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_601])).

tff(c_44,plain,(
    k4_subset_1('#skF_1','#skF_2',k2_subset_1('#skF_1')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_47,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_36,c_44])).

tff(c_622,plain,(
    k2_xboole_0('#skF_2','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_47])).

tff(c_40,plain,(
    ! [A_46] : ~ v1_xboole_0(k1_zfmisc_1(A_46)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_191,plain,(
    ! [B_76,A_77] :
      ( r2_hidden(B_76,A_77)
      | ~ m1_subset_1(B_76,A_77)
      | v1_xboole_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24,plain,(
    ! [A_38] : k3_tarski(k1_zfmisc_1(A_38)) = A_38 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_159,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(A_64,k3_tarski(B_65))
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_162,plain,(
    ! [A_64,A_38] :
      ( r1_tarski(A_64,A_38)
      | ~ r2_hidden(A_64,k1_zfmisc_1(A_38)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_159])).

tff(c_198,plain,(
    ! [B_76,A_38] :
      ( r1_tarski(B_76,A_38)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_38))
      | v1_xboole_0(k1_zfmisc_1(A_38)) ) ),
    inference(resolution,[status(thm)],[c_191,c_162])).

tff(c_212,plain,(
    ! [B_81,A_82] :
      ( r1_tarski(B_81,A_82)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_82)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_198])).

tff(c_225,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_212])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_234,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_225,c_6])).

tff(c_78,plain,(
    ! [B_56,A_57] : k3_xboole_0(B_56,A_57) = k3_xboole_0(A_57,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_93,plain,(
    ! [A_57,B_56] : k2_xboole_0(A_57,k3_xboole_0(B_56,A_57)) = A_57 ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_4])).

tff(c_253,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_93])).

tff(c_543,plain,(
    ! [B_120] :
      ( k4_subset_1('#skF_1',B_120,'#skF_2') = k2_xboole_0(B_120,'#skF_2')
      | ~ m1_subset_1(B_120,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_46,c_461])).

tff(c_551,plain,(
    k4_subset_1('#skF_1','#skF_1','#skF_2') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_543])).

tff(c_557,plain,(
    k4_subset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_551])).

tff(c_590,plain,(
    ! [A_126,C_127,B_128] :
      ( k4_subset_1(A_126,C_127,B_128) = k4_subset_1(A_126,B_128,C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(A_126))
      | ~ m1_subset_1(B_128,k1_zfmisc_1(A_126)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_627,plain,(
    ! [B_132] :
      ( k4_subset_1('#skF_1',B_132,'#skF_2') = k4_subset_1('#skF_1','#skF_2',B_132)
      | ~ m1_subset_1(B_132,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_46,c_590])).

tff(c_635,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = k4_subset_1('#skF_1','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_627])).

tff(c_641,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_557,c_635])).

tff(c_644,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_622,c_641])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:37:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.36  
% 2.76/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.36  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.76/1.36  
% 2.76/1.36  %Foreground sorts:
% 2.76/1.36  
% 2.76/1.36  
% 2.76/1.36  %Background operators:
% 2.76/1.36  
% 2.76/1.36  
% 2.76/1.36  %Foreground operators:
% 2.76/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.76/1.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.76/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.76/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.76/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.76/1.36  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.76/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.76/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.76/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.76/1.36  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.76/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.76/1.36  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.76/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.76/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.76/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.76/1.36  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.76/1.36  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.76/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.76/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.76/1.36  
% 2.76/1.38  tff(f_90, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 2.76/1.38  tff(f_74, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.76/1.38  tff(f_76, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.76/1.38  tff(f_85, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.76/1.38  tff(f_79, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.76/1.38  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.76/1.38  tff(f_53, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.76/1.38  tff(f_49, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.76/1.38  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.76/1.38  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.76/1.38  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.76/1.38  tff(f_59, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k4_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k4_subset_1)).
% 2.76/1.38  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.76/1.38  tff(c_36, plain, (![A_44]: (k2_subset_1(A_44)=A_44)), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.76/1.38  tff(c_38, plain, (![A_45]: (m1_subset_1(k2_subset_1(A_45), k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.76/1.38  tff(c_48, plain, (![A_45]: (m1_subset_1(A_45, k1_zfmisc_1(A_45)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38])).
% 2.76/1.38  tff(c_461, plain, (![A_111, B_112, C_113]: (k4_subset_1(A_111, B_112, C_113)=k2_xboole_0(B_112, C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(A_111)) | ~m1_subset_1(B_112, k1_zfmisc_1(A_111)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.76/1.38  tff(c_601, plain, (![A_129, B_130]: (k4_subset_1(A_129, B_130, A_129)=k2_xboole_0(B_130, A_129) | ~m1_subset_1(B_130, k1_zfmisc_1(A_129)))), inference(resolution, [status(thm)], [c_48, c_461])).
% 2.76/1.38  tff(c_612, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')=k2_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_601])).
% 2.76/1.38  tff(c_44, plain, (k4_subset_1('#skF_1', '#skF_2', k2_subset_1('#skF_1'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.76/1.38  tff(c_47, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_36, c_44])).
% 2.76/1.38  tff(c_622, plain, (k2_xboole_0('#skF_2', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_612, c_47])).
% 2.76/1.38  tff(c_40, plain, (![A_46]: (~v1_xboole_0(k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.76/1.38  tff(c_191, plain, (![B_76, A_77]: (r2_hidden(B_76, A_77) | ~m1_subset_1(B_76, A_77) | v1_xboole_0(A_77))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.76/1.38  tff(c_24, plain, (![A_38]: (k3_tarski(k1_zfmisc_1(A_38))=A_38)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.76/1.38  tff(c_159, plain, (![A_64, B_65]: (r1_tarski(A_64, k3_tarski(B_65)) | ~r2_hidden(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.76/1.38  tff(c_162, plain, (![A_64, A_38]: (r1_tarski(A_64, A_38) | ~r2_hidden(A_64, k1_zfmisc_1(A_38)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_159])).
% 2.76/1.38  tff(c_198, plain, (![B_76, A_38]: (r1_tarski(B_76, A_38) | ~m1_subset_1(B_76, k1_zfmisc_1(A_38)) | v1_xboole_0(k1_zfmisc_1(A_38)))), inference(resolution, [status(thm)], [c_191, c_162])).
% 2.76/1.38  tff(c_212, plain, (![B_81, A_82]: (r1_tarski(B_81, A_82) | ~m1_subset_1(B_81, k1_zfmisc_1(A_82)))), inference(negUnitSimplification, [status(thm)], [c_40, c_198])).
% 2.76/1.38  tff(c_225, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_212])).
% 2.76/1.38  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.76/1.38  tff(c_234, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_225, c_6])).
% 2.76/1.38  tff(c_78, plain, (![B_56, A_57]: (k3_xboole_0(B_56, A_57)=k3_xboole_0(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.76/1.38  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k3_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.76/1.38  tff(c_93, plain, (![A_57, B_56]: (k2_xboole_0(A_57, k3_xboole_0(B_56, A_57))=A_57)), inference(superposition, [status(thm), theory('equality')], [c_78, c_4])).
% 2.76/1.38  tff(c_253, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_234, c_93])).
% 2.76/1.38  tff(c_543, plain, (![B_120]: (k4_subset_1('#skF_1', B_120, '#skF_2')=k2_xboole_0(B_120, '#skF_2') | ~m1_subset_1(B_120, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_46, c_461])).
% 2.76/1.38  tff(c_551, plain, (k4_subset_1('#skF_1', '#skF_1', '#skF_2')=k2_xboole_0('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_48, c_543])).
% 2.76/1.38  tff(c_557, plain, (k4_subset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_253, c_551])).
% 2.76/1.38  tff(c_590, plain, (![A_126, C_127, B_128]: (k4_subset_1(A_126, C_127, B_128)=k4_subset_1(A_126, B_128, C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(A_126)) | ~m1_subset_1(B_128, k1_zfmisc_1(A_126)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.76/1.38  tff(c_627, plain, (![B_132]: (k4_subset_1('#skF_1', B_132, '#skF_2')=k4_subset_1('#skF_1', '#skF_2', B_132) | ~m1_subset_1(B_132, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_46, c_590])).
% 2.76/1.38  tff(c_635, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')=k4_subset_1('#skF_1', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_48, c_627])).
% 2.76/1.38  tff(c_641, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_612, c_557, c_635])).
% 2.76/1.38  tff(c_644, plain, $false, inference(negUnitSimplification, [status(thm)], [c_622, c_641])).
% 2.76/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.38  
% 2.76/1.38  Inference rules
% 2.76/1.38  ----------------------
% 2.76/1.38  #Ref     : 0
% 2.76/1.38  #Sup     : 139
% 2.76/1.38  #Fact    : 0
% 2.76/1.38  #Define  : 0
% 2.76/1.38  #Split   : 0
% 2.76/1.38  #Chain   : 0
% 2.76/1.38  #Close   : 0
% 2.76/1.38  
% 2.76/1.38  Ordering : KBO
% 2.76/1.38  
% 2.76/1.38  Simplification rules
% 2.76/1.38  ----------------------
% 2.76/1.38  #Subsume      : 19
% 2.76/1.38  #Demod        : 31
% 2.76/1.38  #Tautology    : 85
% 2.76/1.38  #SimpNegUnit  : 5
% 2.76/1.38  #BackRed      : 1
% 2.76/1.38  
% 2.76/1.38  #Partial instantiations: 0
% 2.76/1.38  #Strategies tried      : 1
% 2.76/1.38  
% 2.76/1.38  Timing (in seconds)
% 2.76/1.38  ----------------------
% 2.76/1.38  Preprocessing        : 0.33
% 2.76/1.38  Parsing              : 0.17
% 2.76/1.38  CNF conversion       : 0.02
% 2.76/1.38  Main loop            : 0.28
% 2.76/1.38  Inferencing          : 0.11
% 2.76/1.38  Reduction            : 0.09
% 2.76/1.38  Demodulation         : 0.07
% 2.76/1.38  BG Simplification    : 0.02
% 2.76/1.38  Subsumption          : 0.04
% 2.76/1.38  Abstraction          : 0.02
% 2.76/1.38  MUC search           : 0.00
% 2.76/1.38  Cooper               : 0.00
% 2.76/1.38  Total                : 0.64
% 2.76/1.38  Index Insertion      : 0.00
% 2.76/1.38  Index Deletion       : 0.00
% 2.76/1.38  Index Matching       : 0.00
% 2.76/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
