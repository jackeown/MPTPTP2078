%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:20 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   63 (  71 expanded)
%              Number of leaves         :   37 (  43 expanded)
%              Depth                    :    7
%              Number of atoms          :   76 ( 108 expanded)
%              Number of equality atoms :   34 (  42 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_65,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_52,plain,(
    k1_funct_1('#skF_7','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_44,plain,(
    ! [A_29] : m1_subset_1('#skF_3'(A_29),k1_zfmisc_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_156,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(A_64,B_65)
      | ~ m1_subset_1(A_64,k1_zfmisc_1(B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_168,plain,(
    ! [A_29] : r1_tarski('#skF_3'(A_29),A_29) ),
    inference(resolution,[status(thm)],[c_44,c_156])).

tff(c_170,plain,(
    ! [A_67,B_68] :
      ( k2_xboole_0(A_67,B_68) = B_68
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_188,plain,(
    ! [A_72] : k2_xboole_0('#skF_3'(A_72),A_72) = A_72 ),
    inference(resolution,[status(thm)],[c_168,c_170])).

tff(c_74,plain,(
    ! [B_45,A_46] : k2_xboole_0(B_45,A_46) = k2_xboole_0(A_46,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    ! [A_27,B_28] : k2_xboole_0(k1_tarski(A_27),B_28) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_90,plain,(
    ! [B_45,A_27] : k2_xboole_0(B_45,k1_tarski(A_27)) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_40])).

tff(c_195,plain,(
    ! [A_27] : k1_tarski(A_27) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_90])).

tff(c_60,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_58,plain,(
    v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_56,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_tarski('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_54,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_312,plain,(
    ! [D_109,C_110,B_111,A_112] :
      ( r2_hidden(k1_funct_1(D_109,C_110),B_111)
      | k1_xboole_0 = B_111
      | ~ r2_hidden(C_110,A_112)
      | ~ m1_subset_1(D_109,k1_zfmisc_1(k2_zfmisc_1(A_112,B_111)))
      | ~ v1_funct_2(D_109,A_112,B_111)
      | ~ v1_funct_1(D_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_337,plain,(
    ! [D_113,B_114] :
      ( r2_hidden(k1_funct_1(D_113,'#skF_6'),B_114)
      | k1_xboole_0 = B_114
      | ~ m1_subset_1(D_113,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_114)))
      | ~ v1_funct_2(D_113,'#skF_4',B_114)
      | ~ v1_funct_1(D_113) ) ),
    inference(resolution,[status(thm)],[c_54,c_312])).

tff(c_344,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_6'),k1_tarski('#skF_5'))
    | k1_tarski('#skF_5') = k1_xboole_0
    | ~ v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5'))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_337])).

tff(c_352,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_6'),k1_tarski('#skF_5'))
    | k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_344])).

tff(c_353,plain,(
    r2_hidden(k1_funct_1('#skF_7','#skF_6'),k1_tarski('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_352])).

tff(c_30,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_32,plain,(
    ! [A_13,B_14] : k1_enumset1(A_13,A_13,B_14) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_245,plain,(
    ! [E_79,C_80,B_81,A_82] :
      ( E_79 = C_80
      | E_79 = B_81
      | E_79 = A_82
      | ~ r2_hidden(E_79,k1_enumset1(A_82,B_81,C_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_273,plain,(
    ! [E_88,B_89,A_90] :
      ( E_88 = B_89
      | E_88 = A_90
      | E_88 = A_90
      | ~ r2_hidden(E_88,k2_tarski(A_90,B_89)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_245])).

tff(c_282,plain,(
    ! [E_88,A_12] :
      ( E_88 = A_12
      | E_88 = A_12
      | E_88 = A_12
      | ~ r2_hidden(E_88,k1_tarski(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_273])).

tff(c_359,plain,(
    k1_funct_1('#skF_7','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_353,c_282])).

tff(c_364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_52,c_52,c_359])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:56:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.32  
% 2.23/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.32  %$ v1_funct_2 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.23/1.32  
% 2.23/1.32  %Foreground sorts:
% 2.23/1.32  
% 2.23/1.32  
% 2.23/1.32  %Background operators:
% 2.23/1.32  
% 2.23/1.32  
% 2.23/1.32  %Foreground operators:
% 2.23/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.23/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.32  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.23/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.23/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.23/1.32  tff('#skF_7', type, '#skF_7': $i).
% 2.23/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.23/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.23/1.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.23/1.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.23/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.23/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.23/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.23/1.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.23/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.23/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.32  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.23/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.23/1.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.23/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.23/1.32  
% 2.55/1.34  tff(f_92, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.55/1.34  tff(f_65, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_subset_1)).
% 2.55/1.34  tff(f_69, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.55/1.34  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.55/1.34  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.55/1.34  tff(f_59, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.55/1.34  tff(f_81, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 2.55/1.34  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.55/1.34  tff(f_50, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.55/1.34  tff(f_46, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.55/1.34  tff(c_52, plain, (k1_funct_1('#skF_7', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.55/1.34  tff(c_44, plain, (![A_29]: (m1_subset_1('#skF_3'(A_29), k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.55/1.34  tff(c_156, plain, (![A_64, B_65]: (r1_tarski(A_64, B_65) | ~m1_subset_1(A_64, k1_zfmisc_1(B_65)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.55/1.34  tff(c_168, plain, (![A_29]: (r1_tarski('#skF_3'(A_29), A_29))), inference(resolution, [status(thm)], [c_44, c_156])).
% 2.55/1.34  tff(c_170, plain, (![A_67, B_68]: (k2_xboole_0(A_67, B_68)=B_68 | ~r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.55/1.34  tff(c_188, plain, (![A_72]: (k2_xboole_0('#skF_3'(A_72), A_72)=A_72)), inference(resolution, [status(thm)], [c_168, c_170])).
% 2.55/1.34  tff(c_74, plain, (![B_45, A_46]: (k2_xboole_0(B_45, A_46)=k2_xboole_0(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.55/1.34  tff(c_40, plain, (![A_27, B_28]: (k2_xboole_0(k1_tarski(A_27), B_28)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.55/1.34  tff(c_90, plain, (![B_45, A_27]: (k2_xboole_0(B_45, k1_tarski(A_27))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_74, c_40])).
% 2.55/1.34  tff(c_195, plain, (![A_27]: (k1_tarski(A_27)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_188, c_90])).
% 2.55/1.34  tff(c_60, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.55/1.34  tff(c_58, plain, (v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.55/1.34  tff(c_56, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_tarski('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.55/1.34  tff(c_54, plain, (r2_hidden('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.55/1.34  tff(c_312, plain, (![D_109, C_110, B_111, A_112]: (r2_hidden(k1_funct_1(D_109, C_110), B_111) | k1_xboole_0=B_111 | ~r2_hidden(C_110, A_112) | ~m1_subset_1(D_109, k1_zfmisc_1(k2_zfmisc_1(A_112, B_111))) | ~v1_funct_2(D_109, A_112, B_111) | ~v1_funct_1(D_109))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.55/1.34  tff(c_337, plain, (![D_113, B_114]: (r2_hidden(k1_funct_1(D_113, '#skF_6'), B_114) | k1_xboole_0=B_114 | ~m1_subset_1(D_113, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_114))) | ~v1_funct_2(D_113, '#skF_4', B_114) | ~v1_funct_1(D_113))), inference(resolution, [status(thm)], [c_54, c_312])).
% 2.55/1.34  tff(c_344, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_6'), k1_tarski('#skF_5')) | k1_tarski('#skF_5')=k1_xboole_0 | ~v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5')) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_56, c_337])).
% 2.55/1.34  tff(c_352, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_6'), k1_tarski('#skF_5')) | k1_tarski('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_344])).
% 2.55/1.34  tff(c_353, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_6'), k1_tarski('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_195, c_352])).
% 2.55/1.34  tff(c_30, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.55/1.34  tff(c_32, plain, (![A_13, B_14]: (k1_enumset1(A_13, A_13, B_14)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.55/1.34  tff(c_245, plain, (![E_79, C_80, B_81, A_82]: (E_79=C_80 | E_79=B_81 | E_79=A_82 | ~r2_hidden(E_79, k1_enumset1(A_82, B_81, C_80)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.55/1.34  tff(c_273, plain, (![E_88, B_89, A_90]: (E_88=B_89 | E_88=A_90 | E_88=A_90 | ~r2_hidden(E_88, k2_tarski(A_90, B_89)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_245])).
% 2.55/1.34  tff(c_282, plain, (![E_88, A_12]: (E_88=A_12 | E_88=A_12 | E_88=A_12 | ~r2_hidden(E_88, k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_273])).
% 2.55/1.34  tff(c_359, plain, (k1_funct_1('#skF_7', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_353, c_282])).
% 2.55/1.34  tff(c_364, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_52, c_52, c_359])).
% 2.55/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.34  
% 2.55/1.34  Inference rules
% 2.55/1.34  ----------------------
% 2.55/1.34  #Ref     : 0
% 2.55/1.34  #Sup     : 68
% 2.55/1.34  #Fact    : 0
% 2.55/1.34  #Define  : 0
% 2.55/1.34  #Split   : 0
% 2.55/1.34  #Chain   : 0
% 2.55/1.34  #Close   : 0
% 2.55/1.34  
% 2.55/1.34  Ordering : KBO
% 2.55/1.34  
% 2.55/1.34  Simplification rules
% 2.55/1.34  ----------------------
% 2.55/1.34  #Subsume      : 4
% 2.55/1.34  #Demod        : 7
% 2.55/1.34  #Tautology    : 36
% 2.55/1.34  #SimpNegUnit  : 2
% 2.55/1.34  #BackRed      : 0
% 2.55/1.34  
% 2.55/1.34  #Partial instantiations: 0
% 2.55/1.34  #Strategies tried      : 1
% 2.55/1.34  
% 2.55/1.34  Timing (in seconds)
% 2.55/1.34  ----------------------
% 2.55/1.34  Preprocessing        : 0.33
% 2.55/1.34  Parsing              : 0.17
% 2.55/1.34  CNF conversion       : 0.02
% 2.55/1.34  Main loop            : 0.24
% 2.55/1.34  Inferencing          : 0.08
% 2.55/1.34  Reduction            : 0.08
% 2.55/1.34  Demodulation         : 0.06
% 2.55/1.34  BG Simplification    : 0.02
% 2.55/1.34  Subsumption          : 0.05
% 2.55/1.34  Abstraction          : 0.02
% 2.55/1.34  MUC search           : 0.00
% 2.55/1.34  Cooper               : 0.00
% 2.55/1.34  Total                : 0.60
% 2.55/1.34  Index Insertion      : 0.00
% 2.55/1.34  Index Deletion       : 0.00
% 2.55/1.34  Index Matching       : 0.00
% 2.55/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
