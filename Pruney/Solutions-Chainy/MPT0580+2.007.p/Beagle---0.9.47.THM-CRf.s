%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:57 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   74 (  99 expanded)
%              Number of leaves         :   31 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :   97 ( 167 expanded)
%              Number of equality atoms :   17 (  33 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v3_relat_1 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v3_relat_1,type,(
    v3_relat_1: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( v3_relat_1(A)
        <=> ! [B] :
              ( r2_hidden(B,k2_relat_1(A))
             => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t184_relat_1)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v3_relat_1(A)
      <=> r1_tarski(k2_relat_1(A),k1_tarski(k1_xboole_0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_53,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_50,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v3_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_68,plain,(
    ~ v3_relat_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_48,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_16,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_127,plain,(
    ! [B_56,C_57,A_58] :
      ( r2_hidden(B_56,C_57)
      | ~ r1_tarski(k2_tarski(A_58,B_56),C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_141,plain,(
    ! [B_59,A_60] : r2_hidden(B_59,k2_tarski(A_60,B_59)) ),
    inference(resolution,[status(thm)],[c_12,c_127])).

tff(c_147,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_141])).

tff(c_166,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_1'(A_65,B_66),A_65)
      | r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,(
    ! [B_36] :
      ( v3_relat_1('#skF_2')
      | k1_xboole_0 = B_36
      | ~ r2_hidden(B_36,k2_relat_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_118,plain,(
    ! [B_36] :
      ( k1_xboole_0 = B_36
      | ~ r2_hidden(B_36,k2_relat_1('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_60])).

tff(c_180,plain,(
    ! [B_66] :
      ( '#skF_1'(k2_relat_1('#skF_2'),B_66) = k1_xboole_0
      | r1_tarski(k2_relat_1('#skF_2'),B_66) ) ),
    inference(resolution,[status(thm)],[c_166,c_118])).

tff(c_597,plain,(
    ! [A_131] :
      ( v3_relat_1(A_131)
      | ~ r1_tarski(k2_relat_1(A_131),k1_tarski(k1_xboole_0))
      | ~ v1_relat_1(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_604,plain,
    ( v3_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | '#skF_1'(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_180,c_597])).

tff(c_608,plain,
    ( v3_relat_1('#skF_2')
    | '#skF_1'(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_604])).

tff(c_609,plain,(
    '#skF_1'(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_608])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_619,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | r1_tarski(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_609,c_4])).

tff(c_625,plain,(
    r1_tarski(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_619])).

tff(c_44,plain,(
    ! [A_33] :
      ( v3_relat_1(A_33)
      | ~ r1_tarski(k2_relat_1(A_33),k1_tarski(k1_xboole_0))
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_629,plain,
    ( v3_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_625,c_44])).

tff(c_634,plain,(
    v3_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_629])).

tff(c_636,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_634])).

tff(c_637,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_638,plain,(
    v3_relat_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1193,plain,(
    ! [A_217] :
      ( r1_tarski(k2_relat_1(A_217),k1_tarski(k1_xboole_0))
      | ~ v3_relat_1(A_217)
      | ~ v1_relat_1(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_52,plain,
    ( r2_hidden('#skF_3',k2_relat_1('#skF_2'))
    | ~ v3_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_668,plain,(
    r2_hidden('#skF_3',k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_638,c_52])).

tff(c_1001,plain,(
    ! [C_202,B_203,A_204] :
      ( r2_hidden(C_202,B_203)
      | ~ r2_hidden(C_202,A_204)
      | ~ r1_tarski(A_204,B_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1037,plain,(
    ! [B_203] :
      ( r2_hidden('#skF_3',B_203)
      | ~ r1_tarski(k2_relat_1('#skF_2'),B_203) ) ),
    inference(resolution,[status(thm)],[c_668,c_1001])).

tff(c_1197,plain,
    ( r2_hidden('#skF_3',k1_tarski(k1_xboole_0))
    | ~ v3_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1193,c_1037])).

tff(c_1205,plain,(
    r2_hidden('#skF_3',k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_638,c_1197])).

tff(c_38,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(A_29,B_30)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1214,plain,(
    m1_subset_1('#skF_3',k1_tarski(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_1205,c_38])).

tff(c_28,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_673,plain,(
    ! [A_138,B_139] :
      ( r1_tarski(A_138,B_139)
      | ~ m1_subset_1(A_138,k1_zfmisc_1(B_139)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_676,plain,(
    ! [A_138] :
      ( r1_tarski(A_138,k1_xboole_0)
      | ~ m1_subset_1(A_138,k1_tarski(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_673])).

tff(c_1218,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1214,c_676])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_853,plain,(
    ! [B_174,A_175] :
      ( B_174 = A_175
      | ~ r1_tarski(B_174,A_175)
      | ~ r1_tarski(A_175,B_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_871,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_853])).

tff(c_1221,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1218,c_871])).

tff(c_1227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_637,c_1221])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:46:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.48  
% 3.17/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.48  %$ r2_hidden > r1_tarski > m1_subset_1 > v3_relat_1 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.17/1.48  
% 3.17/1.48  %Foreground sorts:
% 3.17/1.48  
% 3.17/1.48  
% 3.17/1.48  %Background operators:
% 3.17/1.48  
% 3.17/1.48  
% 3.17/1.48  %Foreground operators:
% 3.17/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.17/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.17/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.17/1.48  tff(v3_relat_1, type, v3_relat_1: $i > $o).
% 3.17/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.17/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.17/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.17/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.17/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.17/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.17/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.17/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.17/1.48  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.17/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.17/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.48  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.17/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.17/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.17/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.17/1.48  
% 3.17/1.49  tff(f_85, negated_conjecture, ~(![A]: (v1_relat_1(A) => (v3_relat_1(A) <=> (![B]: (r2_hidden(B, k2_relat_1(A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t184_relat_1)).
% 3.17/1.49  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.17/1.49  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.17/1.49  tff(f_61, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.17/1.49  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.17/1.49  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (v3_relat_1(A) <=> r1_tarski(k2_relat_1(A), k1_tarski(k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d15_relat_1)).
% 3.17/1.49  tff(f_65, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.17/1.49  tff(f_53, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 3.17/1.49  tff(f_69, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.17/1.49  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.17/1.49  tff(c_50, plain, (k1_xboole_0!='#skF_3' | ~v3_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.17/1.49  tff(c_68, plain, (~v3_relat_1('#skF_2')), inference(splitLeft, [status(thm)], [c_50])).
% 3.17/1.49  tff(c_48, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.17/1.49  tff(c_16, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.17/1.49  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.17/1.49  tff(c_127, plain, (![B_56, C_57, A_58]: (r2_hidden(B_56, C_57) | ~r1_tarski(k2_tarski(A_58, B_56), C_57))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.17/1.49  tff(c_141, plain, (![B_59, A_60]: (r2_hidden(B_59, k2_tarski(A_60, B_59)))), inference(resolution, [status(thm)], [c_12, c_127])).
% 3.17/1.49  tff(c_147, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_141])).
% 3.17/1.49  tff(c_166, plain, (![A_65, B_66]: (r2_hidden('#skF_1'(A_65, B_66), A_65) | r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.17/1.49  tff(c_60, plain, (![B_36]: (v3_relat_1('#skF_2') | k1_xboole_0=B_36 | ~r2_hidden(B_36, k2_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.17/1.49  tff(c_118, plain, (![B_36]: (k1_xboole_0=B_36 | ~r2_hidden(B_36, k2_relat_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_68, c_60])).
% 3.17/1.49  tff(c_180, plain, (![B_66]: ('#skF_1'(k2_relat_1('#skF_2'), B_66)=k1_xboole_0 | r1_tarski(k2_relat_1('#skF_2'), B_66))), inference(resolution, [status(thm)], [c_166, c_118])).
% 3.17/1.49  tff(c_597, plain, (![A_131]: (v3_relat_1(A_131) | ~r1_tarski(k2_relat_1(A_131), k1_tarski(k1_xboole_0)) | ~v1_relat_1(A_131))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.17/1.49  tff(c_604, plain, (v3_relat_1('#skF_2') | ~v1_relat_1('#skF_2') | '#skF_1'(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_180, c_597])).
% 3.17/1.49  tff(c_608, plain, (v3_relat_1('#skF_2') | '#skF_1'(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_604])).
% 3.17/1.49  tff(c_609, plain, ('#skF_1'(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_608])).
% 3.17/1.49  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.17/1.49  tff(c_619, plain, (~r2_hidden(k1_xboole_0, k1_tarski(k1_xboole_0)) | r1_tarski(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_609, c_4])).
% 3.17/1.49  tff(c_625, plain, (r1_tarski(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_619])).
% 3.17/1.49  tff(c_44, plain, (![A_33]: (v3_relat_1(A_33) | ~r1_tarski(k2_relat_1(A_33), k1_tarski(k1_xboole_0)) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.17/1.49  tff(c_629, plain, (v3_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_625, c_44])).
% 3.17/1.49  tff(c_634, plain, (v3_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_629])).
% 3.17/1.49  tff(c_636, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_634])).
% 3.17/1.49  tff(c_637, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_50])).
% 3.17/1.49  tff(c_638, plain, (v3_relat_1('#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 3.17/1.49  tff(c_1193, plain, (![A_217]: (r1_tarski(k2_relat_1(A_217), k1_tarski(k1_xboole_0)) | ~v3_relat_1(A_217) | ~v1_relat_1(A_217))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.17/1.49  tff(c_52, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_2')) | ~v3_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.17/1.49  tff(c_668, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_638, c_52])).
% 3.17/1.49  tff(c_1001, plain, (![C_202, B_203, A_204]: (r2_hidden(C_202, B_203) | ~r2_hidden(C_202, A_204) | ~r1_tarski(A_204, B_203))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.17/1.49  tff(c_1037, plain, (![B_203]: (r2_hidden('#skF_3', B_203) | ~r1_tarski(k2_relat_1('#skF_2'), B_203))), inference(resolution, [status(thm)], [c_668, c_1001])).
% 3.17/1.49  tff(c_1197, plain, (r2_hidden('#skF_3', k1_tarski(k1_xboole_0)) | ~v3_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1193, c_1037])).
% 3.17/1.49  tff(c_1205, plain, (r2_hidden('#skF_3', k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_638, c_1197])).
% 3.17/1.49  tff(c_38, plain, (![A_29, B_30]: (m1_subset_1(A_29, B_30) | ~r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.17/1.49  tff(c_1214, plain, (m1_subset_1('#skF_3', k1_tarski(k1_xboole_0))), inference(resolution, [status(thm)], [c_1205, c_38])).
% 3.17/1.49  tff(c_28, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.17/1.49  tff(c_673, plain, (![A_138, B_139]: (r1_tarski(A_138, B_139) | ~m1_subset_1(A_138, k1_zfmisc_1(B_139)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.17/1.49  tff(c_676, plain, (![A_138]: (r1_tarski(A_138, k1_xboole_0) | ~m1_subset_1(A_138, k1_tarski(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_673])).
% 3.17/1.49  tff(c_1218, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_1214, c_676])).
% 3.17/1.49  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.17/1.49  tff(c_853, plain, (![B_174, A_175]: (B_174=A_175 | ~r1_tarski(B_174, A_175) | ~r1_tarski(A_175, B_174))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.17/1.49  tff(c_871, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_853])).
% 3.17/1.49  tff(c_1221, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1218, c_871])).
% 3.17/1.49  tff(c_1227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_637, c_1221])).
% 3.17/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.49  
% 3.17/1.49  Inference rules
% 3.17/1.49  ----------------------
% 3.17/1.49  #Ref     : 0
% 3.17/1.49  #Sup     : 248
% 3.17/1.49  #Fact    : 0
% 3.17/1.49  #Define  : 0
% 3.17/1.49  #Split   : 4
% 3.17/1.49  #Chain   : 0
% 3.17/1.49  #Close   : 0
% 3.17/1.49  
% 3.17/1.49  Ordering : KBO
% 3.17/1.49  
% 3.17/1.49  Simplification rules
% 3.17/1.49  ----------------------
% 3.17/1.49  #Subsume      : 11
% 3.17/1.49  #Demod        : 131
% 3.17/1.49  #Tautology    : 115
% 3.17/1.49  #SimpNegUnit  : 7
% 3.17/1.49  #BackRed      : 5
% 3.17/1.49  
% 3.17/1.49  #Partial instantiations: 0
% 3.17/1.49  #Strategies tried      : 1
% 3.17/1.49  
% 3.17/1.49  Timing (in seconds)
% 3.17/1.49  ----------------------
% 3.17/1.50  Preprocessing        : 0.31
% 3.17/1.50  Parsing              : 0.16
% 3.17/1.50  CNF conversion       : 0.02
% 3.17/1.50  Main loop            : 0.41
% 3.17/1.50  Inferencing          : 0.15
% 3.17/1.50  Reduction            : 0.13
% 3.17/1.50  Demodulation         : 0.10
% 3.17/1.50  BG Simplification    : 0.02
% 3.17/1.50  Subsumption          : 0.07
% 3.17/1.50  Abstraction          : 0.02
% 3.17/1.50  MUC search           : 0.00
% 3.17/1.50  Cooper               : 0.00
% 3.17/1.50  Total                : 0.75
% 3.17/1.50  Index Insertion      : 0.00
% 3.17/1.50  Index Deletion       : 0.00
% 3.17/1.50  Index Matching       : 0.00
% 3.17/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
