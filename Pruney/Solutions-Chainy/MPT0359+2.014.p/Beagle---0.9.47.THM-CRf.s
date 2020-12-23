%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:10 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 132 expanded)
%              Number of leaves         :   24 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :   79 ( 176 expanded)
%              Number of equality atoms :   35 (  85 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_130,plain,(
    ! [A_41,B_42] :
      ( k2_xboole_0(A_41,B_42) = B_42
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,(
    ! [A_43] : k2_xboole_0(k1_xboole_0,A_43) = A_43 ),
    inference(resolution,[status(thm)],[c_6,c_130])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_92,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k2_xboole_0(A_37,B_38)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_99,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_92])).

tff(c_141,plain,(
    ! [A_43] : k4_xboole_0(A_43,A_43) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_99])).

tff(c_12,plain,(
    ! [A_10] : k2_subset_1(A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_13] : m1_subset_1(k2_subset_1(A_13),k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_43,plain,(
    ! [A_13] : m1_subset_1(A_13,k1_zfmisc_1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16])).

tff(c_378,plain,(
    ! [A_55,B_56] :
      ( k4_xboole_0(A_55,B_56) = k3_subset_1(A_55,B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_381,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_subset_1(A_13,A_13) ),
    inference(resolution,[status(thm)],[c_43,c_378])).

tff(c_386,plain,(
    ! [A_13] : k3_subset_1(A_13,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_381])).

tff(c_36,plain,
    ( k2_subset_1('#skF_1') != '#skF_2'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_44,plain,
    ( '#skF_2' != '#skF_1'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_36])).

tff(c_129,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_42,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | k2_subset_1('#skF_1') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_45,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_42])).

tff(c_215,plain,(
    '#skF_2' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_45])).

tff(c_216,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_215,c_129])).

tff(c_389,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_216])).

tff(c_392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_389])).

tff(c_393,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_394,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_395,plain,(
    ! [A_57,B_58] :
      ( k2_xboole_0(A_57,B_58) = B_58
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_402,plain,(
    k2_xboole_0(k3_subset_1('#skF_1','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_394,c_395])).

tff(c_499,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_2])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_872,plain,(
    ! [A_85,B_86] :
      ( k4_xboole_0(A_85,B_86) = k3_subset_1(A_85,B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_890,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_872])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_933,plain,
    ( k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_1'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_890,c_8])).

tff(c_936,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_933])).

tff(c_937,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_393,c_936])).

tff(c_404,plain,(
    ! [A_59] : k2_xboole_0(k1_xboole_0,A_59) = A_59 ),
    inference(resolution,[status(thm)],[c_6,c_395])).

tff(c_410,plain,(
    ! [A_59] : k4_xboole_0(A_59,A_59) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_99])).

tff(c_878,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_subset_1(A_13,A_13) ),
    inference(resolution,[status(thm)],[c_43,c_872])).

tff(c_887,plain,(
    ! [A_13] : k3_subset_1(A_13,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_878])).

tff(c_1442,plain,(
    ! [B_112,C_113,A_114] :
      ( r1_tarski(B_112,C_113)
      | ~ r1_tarski(k3_subset_1(A_114,C_113),k3_subset_1(A_114,B_112))
      | ~ m1_subset_1(C_113,k1_zfmisc_1(A_114))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(A_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1463,plain,(
    ! [B_112,A_13] :
      ( r1_tarski(B_112,A_13)
      | ~ r1_tarski(k1_xboole_0,k3_subset_1(A_13,B_112))
      | ~ m1_subset_1(A_13,k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_887,c_1442])).

tff(c_1511,plain,(
    ! [B_115,A_116] :
      ( r1_tarski(B_115,A_116)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(A_116)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_6,c_1463])).

tff(c_1532,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_1511])).

tff(c_1543,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_937,c_1532])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:57:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.33/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.58  
% 3.33/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.58  %$ r1_tarski > m1_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.33/1.58  
% 3.33/1.58  %Foreground sorts:
% 3.33/1.58  
% 3.33/1.58  
% 3.33/1.58  %Background operators:
% 3.33/1.58  
% 3.33/1.58  
% 3.33/1.58  %Foreground operators:
% 3.33/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.33/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.33/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.33/1.58  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.33/1.58  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.33/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.33/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.33/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.33/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.33/1.58  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.33/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.33/1.58  
% 3.33/1.60  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.33/1.60  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.33/1.60  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.33/1.60  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.33/1.60  tff(f_41, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.33/1.60  tff(f_47, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.33/1.60  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.33/1.60  tff(f_89, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 3.33/1.60  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 3.33/1.60  tff(f_80, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 3.33/1.60  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.33/1.60  tff(c_130, plain, (![A_41, B_42]: (k2_xboole_0(A_41, B_42)=B_42 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.33/1.60  tff(c_135, plain, (![A_43]: (k2_xboole_0(k1_xboole_0, A_43)=A_43)), inference(resolution, [status(thm)], [c_6, c_130])).
% 3.33/1.60  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.33/1.60  tff(c_92, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k2_xboole_0(A_37, B_38))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.33/1.60  tff(c_99, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_92])).
% 3.33/1.60  tff(c_141, plain, (![A_43]: (k4_xboole_0(A_43, A_43)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_135, c_99])).
% 3.33/1.60  tff(c_12, plain, (![A_10]: (k2_subset_1(A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.33/1.60  tff(c_16, plain, (![A_13]: (m1_subset_1(k2_subset_1(A_13), k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.33/1.60  tff(c_43, plain, (![A_13]: (m1_subset_1(A_13, k1_zfmisc_1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16])).
% 3.33/1.60  tff(c_378, plain, (![A_55, B_56]: (k4_xboole_0(A_55, B_56)=k3_subset_1(A_55, B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.33/1.60  tff(c_381, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_subset_1(A_13, A_13))), inference(resolution, [status(thm)], [c_43, c_378])).
% 3.33/1.60  tff(c_386, plain, (![A_13]: (k3_subset_1(A_13, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_141, c_381])).
% 3.33/1.60  tff(c_36, plain, (k2_subset_1('#skF_1')!='#skF_2' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.33/1.60  tff(c_44, plain, ('#skF_2'!='#skF_1' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_36])).
% 3.33/1.60  tff(c_129, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_44])).
% 3.33/1.60  tff(c_42, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | k2_subset_1('#skF_1')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.33/1.60  tff(c_45, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_42])).
% 3.33/1.60  tff(c_215, plain, ('#skF_2'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_129, c_45])).
% 3.33/1.60  tff(c_216, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_215, c_129])).
% 3.33/1.60  tff(c_389, plain, (~r1_tarski(k1_xboole_0, '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_386, c_216])).
% 3.33/1.60  tff(c_392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_389])).
% 3.33/1.60  tff(c_393, plain, ('#skF_2'!='#skF_1'), inference(splitRight, [status(thm)], [c_44])).
% 3.33/1.60  tff(c_394, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 3.33/1.60  tff(c_395, plain, (![A_57, B_58]: (k2_xboole_0(A_57, B_58)=B_58 | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.33/1.60  tff(c_402, plain, (k2_xboole_0(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_394, c_395])).
% 3.33/1.60  tff(c_499, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_402, c_2])).
% 3.33/1.60  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.33/1.60  tff(c_872, plain, (![A_85, B_86]: (k4_xboole_0(A_85, B_86)=k3_subset_1(A_85, B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(A_85)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.33/1.60  tff(c_890, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_872])).
% 3.33/1.60  tff(c_8, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.33/1.60  tff(c_933, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_1' | ~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_890, c_8])).
% 3.33/1.60  tff(c_936, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_499, c_933])).
% 3.33/1.60  tff(c_937, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_393, c_936])).
% 3.33/1.60  tff(c_404, plain, (![A_59]: (k2_xboole_0(k1_xboole_0, A_59)=A_59)), inference(resolution, [status(thm)], [c_6, c_395])).
% 3.33/1.60  tff(c_410, plain, (![A_59]: (k4_xboole_0(A_59, A_59)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_404, c_99])).
% 3.33/1.60  tff(c_878, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_subset_1(A_13, A_13))), inference(resolution, [status(thm)], [c_43, c_872])).
% 3.33/1.60  tff(c_887, plain, (![A_13]: (k3_subset_1(A_13, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_410, c_878])).
% 3.33/1.60  tff(c_1442, plain, (![B_112, C_113, A_114]: (r1_tarski(B_112, C_113) | ~r1_tarski(k3_subset_1(A_114, C_113), k3_subset_1(A_114, B_112)) | ~m1_subset_1(C_113, k1_zfmisc_1(A_114)) | ~m1_subset_1(B_112, k1_zfmisc_1(A_114)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.33/1.60  tff(c_1463, plain, (![B_112, A_13]: (r1_tarski(B_112, A_13) | ~r1_tarski(k1_xboole_0, k3_subset_1(A_13, B_112)) | ~m1_subset_1(A_13, k1_zfmisc_1(A_13)) | ~m1_subset_1(B_112, k1_zfmisc_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_887, c_1442])).
% 3.33/1.60  tff(c_1511, plain, (![B_115, A_116]: (r1_tarski(B_115, A_116) | ~m1_subset_1(B_115, k1_zfmisc_1(A_116)))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_6, c_1463])).
% 3.33/1.60  tff(c_1532, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_1511])).
% 3.33/1.60  tff(c_1543, plain, $false, inference(negUnitSimplification, [status(thm)], [c_937, c_1532])).
% 3.33/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.60  
% 3.33/1.60  Inference rules
% 3.33/1.60  ----------------------
% 3.33/1.60  #Ref     : 0
% 3.33/1.60  #Sup     : 360
% 3.33/1.60  #Fact    : 0
% 3.33/1.60  #Define  : 0
% 3.33/1.60  #Split   : 2
% 3.33/1.60  #Chain   : 0
% 3.33/1.60  #Close   : 0
% 3.33/1.60  
% 3.33/1.60  Ordering : KBO
% 3.33/1.60  
% 3.33/1.60  Simplification rules
% 3.33/1.60  ----------------------
% 3.33/1.60  #Subsume      : 40
% 3.33/1.60  #Demod        : 215
% 3.33/1.60  #Tautology    : 222
% 3.33/1.60  #SimpNegUnit  : 4
% 3.33/1.60  #BackRed      : 3
% 3.33/1.60  
% 3.33/1.60  #Partial instantiations: 0
% 3.33/1.60  #Strategies tried      : 1
% 3.33/1.60  
% 3.33/1.60  Timing (in seconds)
% 3.33/1.60  ----------------------
% 3.33/1.60  Preprocessing        : 0.32
% 3.33/1.60  Parsing              : 0.17
% 3.33/1.60  CNF conversion       : 0.02
% 3.33/1.60  Main loop            : 0.50
% 3.33/1.60  Inferencing          : 0.18
% 3.33/1.60  Reduction            : 0.19
% 3.33/1.60  Demodulation         : 0.14
% 3.33/1.60  BG Simplification    : 0.02
% 3.33/1.60  Subsumption          : 0.08
% 3.33/1.60  Abstraction          : 0.03
% 3.33/1.60  MUC search           : 0.00
% 3.33/1.60  Cooper               : 0.00
% 3.33/1.60  Total                : 0.86
% 3.33/1.60  Index Insertion      : 0.00
% 3.33/1.60  Index Deletion       : 0.00
% 3.33/1.60  Index Matching       : 0.00
% 3.33/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
