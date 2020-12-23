%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:57 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 103 expanded)
%              Number of leaves         :   31 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :   99 ( 175 expanded)
%              Number of equality atoms :   17 (  34 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v3_relat_1 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t184_relat_1)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v3_relat_1(A)
      <=> r1_tarski(k2_relat_1(A),k1_tarski(k1_xboole_0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_55,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_50,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v3_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_73,plain,(
    ~ v3_relat_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_48,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_18,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_192,plain,(
    ! [B_57,C_58,A_59] :
      ( r2_hidden(B_57,C_58)
      | ~ r1_tarski(k2_tarski(A_59,B_57),C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_207,plain,(
    ! [B_60,A_61] : r2_hidden(B_60,k2_tarski(A_61,B_60)) ),
    inference(resolution,[status(thm)],[c_12,c_192])).

tff(c_213,plain,(
    ! [A_10] : r2_hidden(A_10,k1_tarski(A_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_207])).

tff(c_289,plain,(
    ! [A_76,B_77] :
      ( r2_hidden('#skF_1'(A_76,B_77),A_76)
      | r1_tarski(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,(
    ! [B_33] :
      ( v3_relat_1('#skF_2')
      | k1_xboole_0 = B_33
      | ~ r2_hidden(B_33,k2_relat_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_125,plain,(
    ! [B_33] :
      ( k1_xboole_0 = B_33
      | ~ r2_hidden(B_33,k2_relat_1('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_60])).

tff(c_303,plain,(
    ! [B_77] :
      ( '#skF_1'(k2_relat_1('#skF_2'),B_77) = k1_xboole_0
      | r1_tarski(k2_relat_1('#skF_2'),B_77) ) ),
    inference(resolution,[status(thm)],[c_289,c_125])).

tff(c_651,plain,(
    ! [A_117] :
      ( v3_relat_1(A_117)
      | ~ r1_tarski(k2_relat_1(A_117),k1_tarski(k1_xboole_0))
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_655,plain,
    ( v3_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | '#skF_1'(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_303,c_651])).

tff(c_658,plain,
    ( v3_relat_1('#skF_2')
    | '#skF_1'(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_655])).

tff(c_659,plain,(
    '#skF_1'(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_658])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_666,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | r1_tarski(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_659,c_4])).

tff(c_670,plain,(
    r1_tarski(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_666])).

tff(c_44,plain,(
    ! [A_30] :
      ( v3_relat_1(A_30)
      | ~ r1_tarski(k2_relat_1(A_30),k1_tarski(k1_xboole_0))
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_674,plain,
    ( v3_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_670,c_44])).

tff(c_679,plain,(
    v3_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_674])).

tff(c_681,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_679])).

tff(c_682,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_683,plain,(
    v3_relat_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1263,plain,(
    ! [A_198] :
      ( r1_tarski(k2_relat_1(A_198),k1_tarski(k1_xboole_0))
      | ~ v3_relat_1(A_198)
      | ~ v1_relat_1(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_52,plain,
    ( r2_hidden('#skF_3',k2_relat_1('#skF_2'))
    | ~ v3_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_684,plain,(
    ~ v3_relat_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_686,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_683,c_684])).

tff(c_687,plain,(
    r2_hidden('#skF_3',k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1136,plain,(
    ! [C_189,B_190,A_191] :
      ( r2_hidden(C_189,B_190)
      | ~ r2_hidden(C_189,A_191)
      | ~ r1_tarski(A_191,B_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1175,plain,(
    ! [B_190] :
      ( r2_hidden('#skF_3',B_190)
      | ~ r1_tarski(k2_relat_1('#skF_2'),B_190) ) ),
    inference(resolution,[status(thm)],[c_687,c_1136])).

tff(c_1267,plain,
    ( r2_hidden('#skF_3',k1_tarski(k1_xboole_0))
    | ~ v3_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1263,c_1175])).

tff(c_1272,plain,(
    r2_hidden('#skF_3',k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_683,c_1267])).

tff(c_38,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(A_26,B_27)
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1280,plain,(
    m1_subset_1('#skF_3',k1_tarski(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_1272,c_38])).

tff(c_30,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_758,plain,(
    ! [A_129,B_130] :
      ( r1_tarski(A_129,B_130)
      | ~ m1_subset_1(A_129,k1_zfmisc_1(B_130)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_764,plain,(
    ! [A_129] :
      ( r1_tarski(A_129,k1_xboole_0)
      | ~ m1_subset_1(A_129,k1_tarski(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_758])).

tff(c_1284,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1280,c_764])).

tff(c_16,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_955,plain,(
    ! [B_162,A_163] :
      ( B_162 = A_163
      | ~ r1_tarski(B_162,A_163)
      | ~ r1_tarski(A_163,B_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_976,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_955])).

tff(c_1287,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1284,c_976])).

tff(c_1293,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_682,c_1287])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:18:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.52  
% 3.13/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.52  %$ r2_hidden > r1_tarski > m1_subset_1 > v3_relat_1 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.13/1.52  
% 3.13/1.52  %Foreground sorts:
% 3.13/1.52  
% 3.13/1.52  
% 3.13/1.52  %Background operators:
% 3.13/1.52  
% 3.13/1.52  
% 3.13/1.52  %Foreground operators:
% 3.13/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.13/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.13/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.13/1.52  tff(v3_relat_1, type, v3_relat_1: $i > $o).
% 3.13/1.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.13/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.13/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.13/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.13/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.13/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.13/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.13/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.13/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.13/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.52  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.13/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.13/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.13/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.13/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.13/1.52  
% 3.35/1.53  tff(f_85, negated_conjecture, ~(![A]: (v1_relat_1(A) => (v3_relat_1(A) <=> (![B]: (r2_hidden(B, k2_relat_1(A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t184_relat_1)).
% 3.35/1.53  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.35/1.53  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.35/1.53  tff(f_61, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.35/1.53  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.35/1.53  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (v3_relat_1(A) <=> r1_tarski(k2_relat_1(A), k1_tarski(k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d15_relat_1)).
% 3.35/1.53  tff(f_65, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.35/1.53  tff(f_55, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 3.35/1.53  tff(f_69, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.35/1.53  tff(f_42, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.35/1.53  tff(c_50, plain, (k1_xboole_0!='#skF_3' | ~v3_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.35/1.53  tff(c_73, plain, (~v3_relat_1('#skF_2')), inference(splitLeft, [status(thm)], [c_50])).
% 3.35/1.53  tff(c_48, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.35/1.53  tff(c_18, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.35/1.53  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.35/1.53  tff(c_192, plain, (![B_57, C_58, A_59]: (r2_hidden(B_57, C_58) | ~r1_tarski(k2_tarski(A_59, B_57), C_58))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.35/1.53  tff(c_207, plain, (![B_60, A_61]: (r2_hidden(B_60, k2_tarski(A_61, B_60)))), inference(resolution, [status(thm)], [c_12, c_192])).
% 3.35/1.53  tff(c_213, plain, (![A_10]: (r2_hidden(A_10, k1_tarski(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_207])).
% 3.35/1.53  tff(c_289, plain, (![A_76, B_77]: (r2_hidden('#skF_1'(A_76, B_77), A_76) | r1_tarski(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.35/1.53  tff(c_60, plain, (![B_33]: (v3_relat_1('#skF_2') | k1_xboole_0=B_33 | ~r2_hidden(B_33, k2_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.35/1.53  tff(c_125, plain, (![B_33]: (k1_xboole_0=B_33 | ~r2_hidden(B_33, k2_relat_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_73, c_60])).
% 3.35/1.53  tff(c_303, plain, (![B_77]: ('#skF_1'(k2_relat_1('#skF_2'), B_77)=k1_xboole_0 | r1_tarski(k2_relat_1('#skF_2'), B_77))), inference(resolution, [status(thm)], [c_289, c_125])).
% 3.35/1.53  tff(c_651, plain, (![A_117]: (v3_relat_1(A_117) | ~r1_tarski(k2_relat_1(A_117), k1_tarski(k1_xboole_0)) | ~v1_relat_1(A_117))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.35/1.53  tff(c_655, plain, (v3_relat_1('#skF_2') | ~v1_relat_1('#skF_2') | '#skF_1'(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_303, c_651])).
% 3.35/1.53  tff(c_658, plain, (v3_relat_1('#skF_2') | '#skF_1'(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_655])).
% 3.35/1.53  tff(c_659, plain, ('#skF_1'(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_73, c_658])).
% 3.35/1.53  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.35/1.53  tff(c_666, plain, (~r2_hidden(k1_xboole_0, k1_tarski(k1_xboole_0)) | r1_tarski(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_659, c_4])).
% 3.35/1.53  tff(c_670, plain, (r1_tarski(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_213, c_666])).
% 3.35/1.53  tff(c_44, plain, (![A_30]: (v3_relat_1(A_30) | ~r1_tarski(k2_relat_1(A_30), k1_tarski(k1_xboole_0)) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.35/1.53  tff(c_674, plain, (v3_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_670, c_44])).
% 3.35/1.53  tff(c_679, plain, (v3_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_674])).
% 3.35/1.53  tff(c_681, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_679])).
% 3.35/1.53  tff(c_682, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_50])).
% 3.35/1.53  tff(c_683, plain, (v3_relat_1('#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 3.35/1.53  tff(c_1263, plain, (![A_198]: (r1_tarski(k2_relat_1(A_198), k1_tarski(k1_xboole_0)) | ~v3_relat_1(A_198) | ~v1_relat_1(A_198))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.35/1.53  tff(c_52, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_2')) | ~v3_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.35/1.53  tff(c_684, plain, (~v3_relat_1('#skF_2')), inference(splitLeft, [status(thm)], [c_52])).
% 3.35/1.53  tff(c_686, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_683, c_684])).
% 3.35/1.53  tff(c_687, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_52])).
% 3.35/1.53  tff(c_1136, plain, (![C_189, B_190, A_191]: (r2_hidden(C_189, B_190) | ~r2_hidden(C_189, A_191) | ~r1_tarski(A_191, B_190))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.35/1.53  tff(c_1175, plain, (![B_190]: (r2_hidden('#skF_3', B_190) | ~r1_tarski(k2_relat_1('#skF_2'), B_190))), inference(resolution, [status(thm)], [c_687, c_1136])).
% 3.35/1.53  tff(c_1267, plain, (r2_hidden('#skF_3', k1_tarski(k1_xboole_0)) | ~v3_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1263, c_1175])).
% 3.35/1.53  tff(c_1272, plain, (r2_hidden('#skF_3', k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_683, c_1267])).
% 3.35/1.53  tff(c_38, plain, (![A_26, B_27]: (m1_subset_1(A_26, B_27) | ~r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.35/1.53  tff(c_1280, plain, (m1_subset_1('#skF_3', k1_tarski(k1_xboole_0))), inference(resolution, [status(thm)], [c_1272, c_38])).
% 3.35/1.53  tff(c_30, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.35/1.53  tff(c_758, plain, (![A_129, B_130]: (r1_tarski(A_129, B_130) | ~m1_subset_1(A_129, k1_zfmisc_1(B_130)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.35/1.53  tff(c_764, plain, (![A_129]: (r1_tarski(A_129, k1_xboole_0) | ~m1_subset_1(A_129, k1_tarski(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_758])).
% 3.35/1.53  tff(c_1284, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_1280, c_764])).
% 3.35/1.53  tff(c_16, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.35/1.53  tff(c_955, plain, (![B_162, A_163]: (B_162=A_163 | ~r1_tarski(B_162, A_163) | ~r1_tarski(A_163, B_162))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.35/1.53  tff(c_976, plain, (![A_9]: (k1_xboole_0=A_9 | ~r1_tarski(A_9, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_955])).
% 3.35/1.53  tff(c_1287, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1284, c_976])).
% 3.35/1.53  tff(c_1293, plain, $false, inference(negUnitSimplification, [status(thm)], [c_682, c_1287])).
% 3.35/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.53  
% 3.35/1.53  Inference rules
% 3.35/1.53  ----------------------
% 3.35/1.53  #Ref     : 0
% 3.35/1.53  #Sup     : 274
% 3.35/1.53  #Fact    : 0
% 3.35/1.53  #Define  : 0
% 3.35/1.53  #Split   : 3
% 3.35/1.53  #Chain   : 0
% 3.35/1.53  #Close   : 0
% 3.35/1.53  
% 3.35/1.53  Ordering : KBO
% 3.35/1.53  
% 3.35/1.53  Simplification rules
% 3.35/1.53  ----------------------
% 3.35/1.53  #Subsume      : 13
% 3.35/1.53  #Demod        : 92
% 3.35/1.53  #Tautology    : 123
% 3.35/1.53  #SimpNegUnit  : 4
% 3.35/1.53  #BackRed      : 0
% 3.35/1.53  
% 3.35/1.53  #Partial instantiations: 0
% 3.35/1.53  #Strategies tried      : 1
% 3.35/1.53  
% 3.35/1.53  Timing (in seconds)
% 3.35/1.53  ----------------------
% 3.35/1.54  Preprocessing        : 0.32
% 3.35/1.54  Parsing              : 0.17
% 3.35/1.54  CNF conversion       : 0.02
% 3.35/1.54  Main loop            : 0.43
% 3.35/1.54  Inferencing          : 0.16
% 3.35/1.54  Reduction            : 0.14
% 3.35/1.54  Demodulation         : 0.10
% 3.35/1.54  BG Simplification    : 0.02
% 3.35/1.54  Subsumption          : 0.07
% 3.35/1.54  Abstraction          : 0.02
% 3.35/1.54  MUC search           : 0.00
% 3.35/1.54  Cooper               : 0.00
% 3.35/1.54  Total                : 0.79
% 3.35/1.54  Index Insertion      : 0.00
% 3.35/1.54  Index Deletion       : 0.00
% 3.35/1.54  Index Matching       : 0.00
% 3.35/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
