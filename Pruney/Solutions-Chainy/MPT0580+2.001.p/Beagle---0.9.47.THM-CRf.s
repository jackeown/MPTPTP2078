%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:56 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 133 expanded)
%              Number of leaves         :   34 (  57 expanded)
%              Depth                    :   12
%              Number of atoms          :  102 ( 230 expanded)
%              Number of equality atoms :   20 (  51 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v3_relat_1 > v1_xboole_0 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( v3_relat_1(A)
        <=> ! [B] :
              ( r2_hidden(B,k2_relat_1(A))
             => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t184_relat_1)).

tff(f_53,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_62,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_57,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_59,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v3_relat_1(A)
      <=> r1_tarski(k2_relat_1(A),k1_tarski(k1_xboole_0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_relat_1)).

tff(f_55,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_44,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v3_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_69,plain,(
    ~ v3_relat_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_42,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_26,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_34,plain,(
    ! [A_24] : ~ v1_xboole_0(k1_zfmisc_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_72,plain,(
    ~ v1_xboole_0(k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_34])).

tff(c_30,plain,(
    ! [A_22] : k2_subset_1(A_22) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,(
    ! [A_23] : m1_subset_1(k2_subset_1(A_23),k1_zfmisc_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_88,plain,(
    ! [A_36] : m1_subset_1(A_36,k1_zfmisc_1(A_36)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32])).

tff(c_91,plain,(
    m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_88])).

tff(c_36,plain,(
    ! [A_25,B_26] :
      ( r2_hidden(A_25,B_26)
      | v1_xboole_0(B_26)
      | ~ m1_subset_1(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_54,plain,(
    ! [B_30] :
      ( v3_relat_1('#skF_2')
      | k1_xboole_0 = B_30
      | ~ r2_hidden(B_30,k2_relat_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_195,plain,(
    ! [B_55] :
      ( k1_xboole_0 = B_55
      | ~ r2_hidden(B_55,k2_relat_1('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_54])).

tff(c_244,plain,(
    ! [B_66] :
      ( '#skF_1'(k2_relat_1('#skF_2'),B_66) = k1_xboole_0
      | r1_tarski(k2_relat_1('#skF_2'),B_66) ) ),
    inference(resolution,[status(thm)],[c_6,c_195])).

tff(c_38,plain,(
    ! [A_27] :
      ( v3_relat_1(A_27)
      | ~ r1_tarski(k2_relat_1(A_27),k1_tarski(k1_xboole_0))
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_248,plain,
    ( v3_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | '#skF_1'(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_244,c_38])).

tff(c_257,plain,
    ( v3_relat_1('#skF_2')
    | '#skF_1'(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_248])).

tff(c_258,plain,(
    '#skF_1'(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_257])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_264,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | r1_tarski(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_4])).

tff(c_539,plain,(
    ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_264])).

tff(c_542,plain,
    ( v1_xboole_0(k1_tarski(k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_36,c_539])).

tff(c_545,plain,(
    v1_xboole_0(k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_542])).

tff(c_547,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_545])).

tff(c_548,plain,(
    r1_tarski(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_569,plain,
    ( v3_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_548,c_38])).

tff(c_576,plain,(
    v3_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_569])).

tff(c_578,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_576])).

tff(c_579,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_580,plain,(
    v3_relat_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_757,plain,(
    ! [A_113] :
      ( r1_tarski(k2_relat_1(A_113),k1_tarski(k1_xboole_0))
      | ~ v3_relat_1(A_113)
      | ~ v1_relat_1(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_46,plain,
    ( r2_hidden('#skF_3',k2_relat_1('#skF_2'))
    | ~ v3_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_600,plain,(
    r2_hidden('#skF_3',k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_46])).

tff(c_729,plain,(
    ! [C_108,B_109,A_110] :
      ( r2_hidden(C_108,B_109)
      | ~ r2_hidden(C_108,A_110)
      | ~ r1_tarski(A_110,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_738,plain,(
    ! [B_109] :
      ( r2_hidden('#skF_3',B_109)
      | ~ r1_tarski(k2_relat_1('#skF_2'),B_109) ) ),
    inference(resolution,[status(thm)],[c_600,c_729])).

tff(c_761,plain,
    ( r2_hidden('#skF_3',k1_tarski(k1_xboole_0))
    | ~ v3_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_757,c_738])).

tff(c_766,plain,(
    r2_hidden('#skF_3',k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_580,c_761])).

tff(c_28,plain,(
    ! [A_21] : k3_tarski(k1_zfmisc_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_593,plain,(
    k3_tarski(k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_28])).

tff(c_618,plain,(
    ! [A_86,B_87] :
      ( r1_tarski(A_86,k3_tarski(B_87))
      | ~ r2_hidden(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_621,plain,(
    ! [A_86] :
      ( r1_tarski(A_86,k1_xboole_0)
      | ~ r2_hidden(A_86,k1_tarski(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_593,c_618])).

tff(c_779,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_766,c_621])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_693,plain,(
    ! [B_102,A_103] :
      ( B_102 = A_103
      | ~ r1_tarski(B_102,A_103)
      | ~ r1_tarski(A_103,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_705,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_693])).

tff(c_782,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_779,c_705])).

tff(c_788,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_579,c_782])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:37:53 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.40  
% 2.83/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.40  %$ r2_hidden > r1_tarski > m1_subset_1 > v3_relat_1 > v1_xboole_0 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.83/1.40  
% 2.83/1.40  %Foreground sorts:
% 2.83/1.40  
% 2.83/1.40  
% 2.83/1.40  %Background operators:
% 2.83/1.40  
% 2.83/1.40  
% 2.83/1.40  %Foreground operators:
% 2.83/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.83/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.83/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.83/1.40  tff(v3_relat_1, type, v3_relat_1: $i > $o).
% 2.83/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.83/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.83/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.83/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.83/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.83/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.83/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.83/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.83/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.40  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.83/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.83/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.83/1.40  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.83/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.83/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.40  
% 2.83/1.42  tff(f_84, negated_conjecture, ~(![A]: (v1_relat_1(A) => (v3_relat_1(A) <=> (![B]: (r2_hidden(B, k2_relat_1(A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t184_relat_1)).
% 2.83/1.42  tff(f_53, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 2.83/1.42  tff(f_62, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.83/1.42  tff(f_57, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.83/1.42  tff(f_59, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.83/1.42  tff(f_68, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.83/1.42  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.83/1.42  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (v3_relat_1(A) <=> r1_tarski(k2_relat_1(A), k1_tarski(k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d15_relat_1)).
% 2.83/1.42  tff(f_55, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.83/1.42  tff(f_52, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.83/1.42  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.83/1.42  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.83/1.42  tff(c_44, plain, (k1_xboole_0!='#skF_3' | ~v3_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.83/1.42  tff(c_69, plain, (~v3_relat_1('#skF_2')), inference(splitLeft, [status(thm)], [c_44])).
% 2.83/1.42  tff(c_42, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.83/1.42  tff(c_26, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.83/1.42  tff(c_34, plain, (![A_24]: (~v1_xboole_0(k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.83/1.42  tff(c_72, plain, (~v1_xboole_0(k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_34])).
% 2.83/1.42  tff(c_30, plain, (![A_22]: (k2_subset_1(A_22)=A_22)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.83/1.42  tff(c_32, plain, (![A_23]: (m1_subset_1(k2_subset_1(A_23), k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.83/1.42  tff(c_88, plain, (![A_36]: (m1_subset_1(A_36, k1_zfmisc_1(A_36)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32])).
% 2.83/1.42  tff(c_91, plain, (m1_subset_1(k1_xboole_0, k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_88])).
% 2.83/1.42  tff(c_36, plain, (![A_25, B_26]: (r2_hidden(A_25, B_26) | v1_xboole_0(B_26) | ~m1_subset_1(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.83/1.42  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.83/1.42  tff(c_54, plain, (![B_30]: (v3_relat_1('#skF_2') | k1_xboole_0=B_30 | ~r2_hidden(B_30, k2_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.83/1.42  tff(c_195, plain, (![B_55]: (k1_xboole_0=B_55 | ~r2_hidden(B_55, k2_relat_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_69, c_54])).
% 2.83/1.42  tff(c_244, plain, (![B_66]: ('#skF_1'(k2_relat_1('#skF_2'), B_66)=k1_xboole_0 | r1_tarski(k2_relat_1('#skF_2'), B_66))), inference(resolution, [status(thm)], [c_6, c_195])).
% 2.83/1.42  tff(c_38, plain, (![A_27]: (v3_relat_1(A_27) | ~r1_tarski(k2_relat_1(A_27), k1_tarski(k1_xboole_0)) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.83/1.42  tff(c_248, plain, (v3_relat_1('#skF_2') | ~v1_relat_1('#skF_2') | '#skF_1'(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_244, c_38])).
% 2.83/1.42  tff(c_257, plain, (v3_relat_1('#skF_2') | '#skF_1'(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_248])).
% 2.83/1.42  tff(c_258, plain, ('#skF_1'(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_69, c_257])).
% 2.83/1.42  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.83/1.42  tff(c_264, plain, (~r2_hidden(k1_xboole_0, k1_tarski(k1_xboole_0)) | r1_tarski(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_258, c_4])).
% 2.83/1.42  tff(c_539, plain, (~r2_hidden(k1_xboole_0, k1_tarski(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_264])).
% 2.83/1.42  tff(c_542, plain, (v1_xboole_0(k1_tarski(k1_xboole_0)) | ~m1_subset_1(k1_xboole_0, k1_tarski(k1_xboole_0))), inference(resolution, [status(thm)], [c_36, c_539])).
% 2.83/1.42  tff(c_545, plain, (v1_xboole_0(k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_542])).
% 2.83/1.42  tff(c_547, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_545])).
% 2.83/1.42  tff(c_548, plain, (r1_tarski(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))), inference(splitRight, [status(thm)], [c_264])).
% 2.83/1.42  tff(c_569, plain, (v3_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_548, c_38])).
% 2.83/1.42  tff(c_576, plain, (v3_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_569])).
% 2.83/1.42  tff(c_578, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_576])).
% 2.83/1.42  tff(c_579, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_44])).
% 2.83/1.42  tff(c_580, plain, (v3_relat_1('#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 2.83/1.42  tff(c_757, plain, (![A_113]: (r1_tarski(k2_relat_1(A_113), k1_tarski(k1_xboole_0)) | ~v3_relat_1(A_113) | ~v1_relat_1(A_113))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.83/1.42  tff(c_46, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_2')) | ~v3_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.83/1.42  tff(c_600, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_580, c_46])).
% 2.83/1.42  tff(c_729, plain, (![C_108, B_109, A_110]: (r2_hidden(C_108, B_109) | ~r2_hidden(C_108, A_110) | ~r1_tarski(A_110, B_109))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.83/1.42  tff(c_738, plain, (![B_109]: (r2_hidden('#skF_3', B_109) | ~r1_tarski(k2_relat_1('#skF_2'), B_109))), inference(resolution, [status(thm)], [c_600, c_729])).
% 2.83/1.42  tff(c_761, plain, (r2_hidden('#skF_3', k1_tarski(k1_xboole_0)) | ~v3_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_757, c_738])).
% 2.83/1.42  tff(c_766, plain, (r2_hidden('#skF_3', k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_580, c_761])).
% 2.83/1.42  tff(c_28, plain, (![A_21]: (k3_tarski(k1_zfmisc_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.83/1.42  tff(c_593, plain, (k3_tarski(k1_tarski(k1_xboole_0))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_26, c_28])).
% 2.83/1.42  tff(c_618, plain, (![A_86, B_87]: (r1_tarski(A_86, k3_tarski(B_87)) | ~r2_hidden(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.83/1.42  tff(c_621, plain, (![A_86]: (r1_tarski(A_86, k1_xboole_0) | ~r2_hidden(A_86, k1_tarski(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_593, c_618])).
% 2.83/1.42  tff(c_779, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_766, c_621])).
% 2.83/1.42  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.83/1.42  tff(c_693, plain, (![B_102, A_103]: (B_102=A_103 | ~r1_tarski(B_102, A_103) | ~r1_tarski(A_103, B_102))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.83/1.42  tff(c_705, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_693])).
% 2.83/1.42  tff(c_782, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_779, c_705])).
% 2.83/1.42  tff(c_788, plain, $false, inference(negUnitSimplification, [status(thm)], [c_579, c_782])).
% 2.83/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.42  
% 2.83/1.42  Inference rules
% 2.83/1.42  ----------------------
% 2.83/1.42  #Ref     : 0
% 2.83/1.42  #Sup     : 151
% 2.83/1.42  #Fact    : 0
% 2.83/1.42  #Define  : 0
% 2.83/1.42  #Split   : 11
% 2.83/1.42  #Chain   : 0
% 2.83/1.42  #Close   : 0
% 2.83/1.42  
% 2.83/1.42  Ordering : KBO
% 2.83/1.42  
% 2.83/1.42  Simplification rules
% 2.83/1.42  ----------------------
% 2.83/1.42  #Subsume      : 13
% 2.83/1.42  #Demod        : 64
% 2.83/1.42  #Tautology    : 78
% 2.83/1.42  #SimpNegUnit  : 17
% 2.83/1.42  #BackRed      : 20
% 2.83/1.42  
% 2.83/1.42  #Partial instantiations: 0
% 2.83/1.42  #Strategies tried      : 1
% 2.83/1.42  
% 2.83/1.42  Timing (in seconds)
% 2.83/1.42  ----------------------
% 2.83/1.42  Preprocessing        : 0.31
% 2.83/1.42  Parsing              : 0.16
% 2.83/1.42  CNF conversion       : 0.02
% 2.83/1.42  Main loop            : 0.32
% 2.83/1.42  Inferencing          : 0.11
% 2.83/1.42  Reduction            : 0.10
% 2.83/1.42  Demodulation         : 0.07
% 2.83/1.42  BG Simplification    : 0.02
% 2.83/1.42  Subsumption          : 0.06
% 2.83/1.42  Abstraction          : 0.01
% 2.83/1.42  MUC search           : 0.00
% 2.83/1.42  Cooper               : 0.00
% 2.83/1.42  Total                : 0.66
% 2.83/1.42  Index Insertion      : 0.00
% 2.83/1.42  Index Deletion       : 0.00
% 2.83/1.42  Index Matching       : 0.00
% 2.83/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
