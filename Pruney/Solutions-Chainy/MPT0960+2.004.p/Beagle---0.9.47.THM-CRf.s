%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:37 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   62 (  78 expanded)
%              Number of leaves         :   37 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :   61 (  86 expanded)
%              Number of equality atoms :   13 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_wellord2 > k1_relat_1 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_45,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_81,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_wellord2(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).

tff(c_48,plain,(
    ! [A_50] : v1_relat_1(k1_wellord2(A_50)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_42,plain,(
    ! [A_42] :
      ( k3_relat_1(k1_wellord2(A_42)) = A_42
      | ~ v1_relat_1(k1_wellord2(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_56,plain,(
    ! [A_42] : k3_relat_1(k1_wellord2(A_42)) = A_42 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42])).

tff(c_212,plain,(
    ! [A_73] :
      ( k2_xboole_0(k1_relat_1(A_73),k2_relat_1(A_73)) = k3_relat_1(A_73)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_228,plain,(
    ! [A_74] :
      ( r1_tarski(k1_relat_1(A_74),k3_relat_1(A_74))
      | ~ v1_relat_1(A_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_2])).

tff(c_231,plain,(
    ! [A_42] :
      ( r1_tarski(k1_relat_1(k1_wellord2(A_42)),A_42)
      | ~ v1_relat_1(k1_wellord2(A_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_228])).

tff(c_233,plain,(
    ! [A_42] : r1_tarski(k1_relat_1(k1_wellord2(A_42)),A_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_231])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_110,plain,(
    ! [A_59,B_60] : k3_tarski(k2_tarski(A_59,B_60)) = k2_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_140,plain,(
    ! [B_67,A_68] : k3_tarski(k2_tarski(B_67,A_68)) = k2_xboole_0(A_68,B_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_110])).

tff(c_20,plain,(
    ! [A_34,B_35] : k3_tarski(k2_tarski(A_34,B_35)) = k2_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_163,plain,(
    ! [B_69,A_70] : k2_xboole_0(B_69,A_70) = k2_xboole_0(A_70,B_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_20])).

tff(c_178,plain,(
    ! [A_70,B_69] : r1_tarski(A_70,k2_xboole_0(B_69,A_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_2])).

tff(c_244,plain,(
    ! [A_79] :
      ( r1_tarski(k2_relat_1(A_79),k3_relat_1(A_79))
      | ~ v1_relat_1(A_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_178])).

tff(c_247,plain,(
    ! [A_42] :
      ( r1_tarski(k2_relat_1(k1_wellord2(A_42)),A_42)
      | ~ v1_relat_1(k1_wellord2(A_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_244])).

tff(c_249,plain,(
    ! [A_42] : r1_tarski(k2_relat_1(k1_wellord2(A_42)),A_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_247])).

tff(c_306,plain,(
    ! [C_104,A_105,B_106] :
      ( m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106)))
      | ~ r1_tarski(k2_relat_1(C_104),B_106)
      | ~ r1_tarski(k1_relat_1(C_104),A_105)
      | ~ v1_relat_1(C_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | ~ m1_subset_1(A_36,k1_zfmisc_1(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_311,plain,(
    ! [C_107,A_108,B_109] :
      ( r1_tarski(C_107,k2_zfmisc_1(A_108,B_109))
      | ~ r1_tarski(k2_relat_1(C_107),B_109)
      | ~ r1_tarski(k1_relat_1(C_107),A_108)
      | ~ v1_relat_1(C_107) ) ),
    inference(resolution,[status(thm)],[c_306,c_22])).

tff(c_313,plain,(
    ! [A_42,A_108] :
      ( r1_tarski(k1_wellord2(A_42),k2_zfmisc_1(A_108,A_42))
      | ~ r1_tarski(k1_relat_1(k1_wellord2(A_42)),A_108)
      | ~ v1_relat_1(k1_wellord2(A_42)) ) ),
    inference(resolution,[status(thm)],[c_249,c_311])).

tff(c_328,plain,(
    ! [A_110,A_111] :
      ( r1_tarski(k1_wellord2(A_110),k2_zfmisc_1(A_111,A_110))
      | ~ r1_tarski(k1_relat_1(k1_wellord2(A_110)),A_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_313])).

tff(c_340,plain,(
    ! [A_42] : r1_tarski(k1_wellord2(A_42),k2_zfmisc_1(A_42,A_42)) ),
    inference(resolution,[status(thm)],[c_233,c_328])).

tff(c_50,plain,(
    ~ r1_tarski(k1_wellord2('#skF_3'),k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_348,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:47:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.33  
% 2.40/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.33  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_wellord2 > k1_relat_1 > #skF_3 > #skF_2 > #skF_1
% 2.40/1.33  
% 2.40/1.33  %Foreground sorts:
% 2.40/1.33  
% 2.40/1.33  
% 2.40/1.33  %Background operators:
% 2.40/1.33  
% 2.40/1.33  
% 2.40/1.33  %Foreground operators:
% 2.40/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.40/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.40/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.40/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.40/1.33  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.40/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.40/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.40/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.40/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.40/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.40/1.33  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 2.40/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.40/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.40/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.40/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.40/1.33  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.40/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.40/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.40/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.40/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.40/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.40/1.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.40/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.40/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.40/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.40/1.33  
% 2.40/1.35  tff(f_78, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 2.40/1.35  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 2.40/1.35  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 2.40/1.35  tff(f_27, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.40/1.35  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.40/1.35  tff(f_45, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.40/1.35  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 2.40/1.35  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.40/1.35  tff(f_81, negated_conjecture, ~(![A]: r1_tarski(k1_wellord2(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_wellord2)).
% 2.40/1.35  tff(c_48, plain, (![A_50]: (v1_relat_1(k1_wellord2(A_50)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.40/1.35  tff(c_42, plain, (![A_42]: (k3_relat_1(k1_wellord2(A_42))=A_42 | ~v1_relat_1(k1_wellord2(A_42)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.40/1.35  tff(c_56, plain, (![A_42]: (k3_relat_1(k1_wellord2(A_42))=A_42)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42])).
% 2.40/1.35  tff(c_212, plain, (![A_73]: (k2_xboole_0(k1_relat_1(A_73), k2_relat_1(A_73))=k3_relat_1(A_73) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.40/1.35  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.40/1.35  tff(c_228, plain, (![A_74]: (r1_tarski(k1_relat_1(A_74), k3_relat_1(A_74)) | ~v1_relat_1(A_74))), inference(superposition, [status(thm), theory('equality')], [c_212, c_2])).
% 2.40/1.35  tff(c_231, plain, (![A_42]: (r1_tarski(k1_relat_1(k1_wellord2(A_42)), A_42) | ~v1_relat_1(k1_wellord2(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_228])).
% 2.40/1.35  tff(c_233, plain, (![A_42]: (r1_tarski(k1_relat_1(k1_wellord2(A_42)), A_42))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_231])).
% 2.40/1.35  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.40/1.35  tff(c_110, plain, (![A_59, B_60]: (k3_tarski(k2_tarski(A_59, B_60))=k2_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.40/1.35  tff(c_140, plain, (![B_67, A_68]: (k3_tarski(k2_tarski(B_67, A_68))=k2_xboole_0(A_68, B_67))), inference(superposition, [status(thm), theory('equality')], [c_6, c_110])).
% 2.40/1.35  tff(c_20, plain, (![A_34, B_35]: (k3_tarski(k2_tarski(A_34, B_35))=k2_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.40/1.35  tff(c_163, plain, (![B_69, A_70]: (k2_xboole_0(B_69, A_70)=k2_xboole_0(A_70, B_69))), inference(superposition, [status(thm), theory('equality')], [c_140, c_20])).
% 2.40/1.35  tff(c_178, plain, (![A_70, B_69]: (r1_tarski(A_70, k2_xboole_0(B_69, A_70)))), inference(superposition, [status(thm), theory('equality')], [c_163, c_2])).
% 2.40/1.35  tff(c_244, plain, (![A_79]: (r1_tarski(k2_relat_1(A_79), k3_relat_1(A_79)) | ~v1_relat_1(A_79))), inference(superposition, [status(thm), theory('equality')], [c_212, c_178])).
% 2.40/1.35  tff(c_247, plain, (![A_42]: (r1_tarski(k2_relat_1(k1_wellord2(A_42)), A_42) | ~v1_relat_1(k1_wellord2(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_244])).
% 2.40/1.35  tff(c_249, plain, (![A_42]: (r1_tarski(k2_relat_1(k1_wellord2(A_42)), A_42))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_247])).
% 2.40/1.35  tff(c_306, plain, (![C_104, A_105, B_106]: (m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))) | ~r1_tarski(k2_relat_1(C_104), B_106) | ~r1_tarski(k1_relat_1(C_104), A_105) | ~v1_relat_1(C_104))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.40/1.35  tff(c_22, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | ~m1_subset_1(A_36, k1_zfmisc_1(B_37)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.40/1.35  tff(c_311, plain, (![C_107, A_108, B_109]: (r1_tarski(C_107, k2_zfmisc_1(A_108, B_109)) | ~r1_tarski(k2_relat_1(C_107), B_109) | ~r1_tarski(k1_relat_1(C_107), A_108) | ~v1_relat_1(C_107))), inference(resolution, [status(thm)], [c_306, c_22])).
% 2.40/1.35  tff(c_313, plain, (![A_42, A_108]: (r1_tarski(k1_wellord2(A_42), k2_zfmisc_1(A_108, A_42)) | ~r1_tarski(k1_relat_1(k1_wellord2(A_42)), A_108) | ~v1_relat_1(k1_wellord2(A_42)))), inference(resolution, [status(thm)], [c_249, c_311])).
% 2.40/1.35  tff(c_328, plain, (![A_110, A_111]: (r1_tarski(k1_wellord2(A_110), k2_zfmisc_1(A_111, A_110)) | ~r1_tarski(k1_relat_1(k1_wellord2(A_110)), A_111))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_313])).
% 2.40/1.35  tff(c_340, plain, (![A_42]: (r1_tarski(k1_wellord2(A_42), k2_zfmisc_1(A_42, A_42)))), inference(resolution, [status(thm)], [c_233, c_328])).
% 2.40/1.35  tff(c_50, plain, (~r1_tarski(k1_wellord2('#skF_3'), k2_zfmisc_1('#skF_3', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.40/1.35  tff(c_348, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_340, c_50])).
% 2.40/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.35  
% 2.40/1.35  Inference rules
% 2.40/1.35  ----------------------
% 2.40/1.35  #Ref     : 0
% 2.40/1.35  #Sup     : 65
% 2.40/1.35  #Fact    : 0
% 2.40/1.35  #Define  : 0
% 2.40/1.35  #Split   : 0
% 2.40/1.35  #Chain   : 0
% 2.40/1.35  #Close   : 0
% 2.40/1.35  
% 2.40/1.35  Ordering : KBO
% 2.40/1.35  
% 2.40/1.35  Simplification rules
% 2.40/1.35  ----------------------
% 2.40/1.35  #Subsume      : 1
% 2.40/1.35  #Demod        : 27
% 2.40/1.35  #Tautology    : 50
% 2.40/1.35  #SimpNegUnit  : 0
% 2.40/1.35  #BackRed      : 1
% 2.40/1.35  
% 2.40/1.35  #Partial instantiations: 0
% 2.40/1.35  #Strategies tried      : 1
% 2.40/1.35  
% 2.40/1.35  Timing (in seconds)
% 2.40/1.35  ----------------------
% 2.40/1.35  Preprocessing        : 0.33
% 2.40/1.35  Parsing              : 0.17
% 2.40/1.35  CNF conversion       : 0.02
% 2.40/1.35  Main loop            : 0.20
% 2.40/1.35  Inferencing          : 0.07
% 2.40/1.35  Reduction            : 0.07
% 2.40/1.35  Demodulation         : 0.05
% 2.40/1.35  BG Simplification    : 0.02
% 2.40/1.35  Subsumption          : 0.03
% 2.40/1.35  Abstraction          : 0.01
% 2.40/1.35  MUC search           : 0.00
% 2.40/1.35  Cooper               : 0.00
% 2.40/1.35  Total                : 0.55
% 2.40/1.35  Index Insertion      : 0.00
% 2.40/1.35  Index Deletion       : 0.00
% 2.40/1.35  Index Matching       : 0.00
% 2.40/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
