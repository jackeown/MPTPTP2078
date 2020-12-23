%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:57 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 156 expanded)
%              Number of leaves         :   32 (  64 expanded)
%              Depth                    :   14
%              Number of atoms          :  109 ( 292 expanded)
%              Number of equality atoms :   15 (  59 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v3_relat_1 > v1_xboole_0 > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( v3_relat_1(A)
        <=> ! [B] :
              ( r2_hidden(B,k2_relat_1(A))
             => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t184_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v3_relat_1(A)
      <=> r1_tarski(k2_relat_1(A),k1_tarski(k1_xboole_0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_28,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_91,plain,(
    ! [A_51,B_52] :
      ( m1_subset_1(A_51,k1_zfmisc_1(B_52))
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_97,plain,(
    ! [A_51] :
      ( m1_subset_1(A_51,k1_tarski(k1_xboole_0))
      | ~ r1_tarski(A_51,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_91])).

tff(c_30,plain,(
    ! [A_30] : ~ v1_xboole_0(k1_zfmisc_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_64,plain,(
    ~ v1_xboole_0(k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_30])).

tff(c_34,plain,(
    ! [A_33,B_34] :
      ( r2_hidden(A_33,B_34)
      | v1_xboole_0(B_34)
      | ~ m1_subset_1(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_46,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v3_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_61,plain,(
    ~ v3_relat_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_44,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_107,plain,(
    ! [A_56,B_57] :
      ( r2_hidden('#skF_1'(A_56,B_57),A_56)
      | r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,(
    ! [B_40] :
      ( v3_relat_1('#skF_2')
      | k1_xboole_0 = B_40
      | ~ r2_hidden(B_40,k2_relat_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_100,plain,(
    ! [B_40] :
      ( k1_xboole_0 = B_40
      | ~ r2_hidden(B_40,k2_relat_1('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_56])).

tff(c_199,plain,(
    ! [B_75] :
      ( '#skF_1'(k2_relat_1('#skF_2'),B_75) = k1_xboole_0
      | r1_tarski(k2_relat_1('#skF_2'),B_75) ) ),
    inference(resolution,[status(thm)],[c_107,c_100])).

tff(c_40,plain,(
    ! [A_37] :
      ( v3_relat_1(A_37)
      | ~ r1_tarski(k2_relat_1(A_37),k1_tarski(k1_xboole_0))
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_203,plain,
    ( v3_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | '#skF_1'(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_199,c_40])).

tff(c_212,plain,
    ( v3_relat_1('#skF_2')
    | '#skF_1'(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_203])).

tff(c_213,plain,(
    '#skF_1'(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_212])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_225,plain,
    ( r2_hidden(k1_xboole_0,k2_relat_1('#skF_2'))
    | r1_tarski(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_6])).

tff(c_258,plain,(
    r1_tarski(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_225])).

tff(c_261,plain,
    ( v3_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_258,c_40])).

tff(c_266,plain,(
    v3_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_261])).

tff(c_268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_266])).

tff(c_270,plain,(
    ~ r1_tarski(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_225])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_222,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | r1_tarski(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_4])).

tff(c_361,plain,(
    ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_270,c_222])).

tff(c_364,plain,
    ( v1_xboole_0(k1_tarski(k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_34,c_361])).

tff(c_367,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_364])).

tff(c_370,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_97,c_367])).

tff(c_374,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_370])).

tff(c_375,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_376,plain,(
    v3_relat_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_501,plain,(
    ! [A_114] :
      ( r1_tarski(k2_relat_1(A_114),k1_tarski(k1_xboole_0))
      | ~ v3_relat_1(A_114)
      | ~ v1_relat_1(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_48,plain,
    ( r2_hidden('#skF_3',k2_relat_1('#skF_2'))
    | ~ v3_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_394,plain,(
    r2_hidden('#skF_3',k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_48])).

tff(c_484,plain,(
    ! [C_110,B_111,A_112] :
      ( r2_hidden(C_110,B_111)
      | ~ r2_hidden(C_110,A_112)
      | ~ r1_tarski(A_112,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_493,plain,(
    ! [B_111] :
      ( r2_hidden('#skF_3',B_111)
      | ~ r1_tarski(k2_relat_1('#skF_2'),B_111) ) ),
    inference(resolution,[status(thm)],[c_394,c_484])).

tff(c_505,plain,
    ( r2_hidden('#skF_3',k1_tarski(k1_xboole_0))
    | ~ v3_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_501,c_493])).

tff(c_513,plain,(
    r2_hidden('#skF_3',k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_376,c_505])).

tff(c_32,plain,(
    ! [A_31,B_32] :
      ( m1_subset_1(A_31,B_32)
      | ~ r2_hidden(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_522,plain,(
    m1_subset_1('#skF_3',k1_tarski(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_513,c_32])).

tff(c_408,plain,(
    ! [A_92,B_93] :
      ( r1_tarski(A_92,B_93)
      | ~ m1_subset_1(A_92,k1_zfmisc_1(B_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_411,plain,(
    ! [A_92] :
      ( r1_tarski(A_92,k1_xboole_0)
      | ~ m1_subset_1(A_92,k1_tarski(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_408])).

tff(c_527,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_522,c_411])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_437,plain,(
    ! [B_102,A_103] :
      ( B_102 = A_103
      | ~ r1_tarski(B_102,A_103)
      | ~ r1_tarski(A_103,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_446,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_437])).

tff(c_530,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_527,c_446])).

tff(c_536,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_375,c_530])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:38:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.41  
% 2.69/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.41  %$ r2_hidden > r1_tarski > m1_subset_1 > v3_relat_1 > v1_xboole_0 > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.69/1.41  
% 2.69/1.41  %Foreground sorts:
% 2.69/1.41  
% 2.69/1.41  
% 2.69/1.41  %Background operators:
% 2.69/1.41  
% 2.69/1.41  
% 2.69/1.41  %Foreground operators:
% 2.69/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.69/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.69/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.69/1.41  tff(v3_relat_1, type, v3_relat_1: $i > $o).
% 2.69/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.69/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.69/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.69/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.69/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.69/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.69/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.69/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.69/1.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.69/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.69/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.69/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.69/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.69/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.69/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.69/1.41  
% 2.69/1.42  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.69/1.42  tff(f_53, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 2.69/1.42  tff(f_70, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.69/1.42  tff(f_56, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.69/1.42  tff(f_66, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.69/1.42  tff(f_86, negated_conjecture, ~(![A]: (v1_relat_1(A) => (v3_relat_1(A) <=> (![B]: (r2_hidden(B, k2_relat_1(A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t184_relat_1)).
% 2.69/1.42  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.69/1.42  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (v3_relat_1(A) <=> r1_tarski(k2_relat_1(A), k1_tarski(k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d15_relat_1)).
% 2.69/1.42  tff(f_60, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.69/1.42  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.69/1.42  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.69/1.42  tff(c_28, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.69/1.42  tff(c_91, plain, (![A_51, B_52]: (m1_subset_1(A_51, k1_zfmisc_1(B_52)) | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.69/1.42  tff(c_97, plain, (![A_51]: (m1_subset_1(A_51, k1_tarski(k1_xboole_0)) | ~r1_tarski(A_51, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_91])).
% 2.69/1.42  tff(c_30, plain, (![A_30]: (~v1_xboole_0(k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.69/1.42  tff(c_64, plain, (~v1_xboole_0(k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_30])).
% 2.69/1.42  tff(c_34, plain, (![A_33, B_34]: (r2_hidden(A_33, B_34) | v1_xboole_0(B_34) | ~m1_subset_1(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.69/1.42  tff(c_46, plain, (k1_xboole_0!='#skF_3' | ~v3_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.69/1.42  tff(c_61, plain, (~v3_relat_1('#skF_2')), inference(splitLeft, [status(thm)], [c_46])).
% 2.69/1.42  tff(c_44, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.69/1.42  tff(c_107, plain, (![A_56, B_57]: (r2_hidden('#skF_1'(A_56, B_57), A_56) | r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.69/1.42  tff(c_56, plain, (![B_40]: (v3_relat_1('#skF_2') | k1_xboole_0=B_40 | ~r2_hidden(B_40, k2_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.69/1.42  tff(c_100, plain, (![B_40]: (k1_xboole_0=B_40 | ~r2_hidden(B_40, k2_relat_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_61, c_56])).
% 2.69/1.42  tff(c_199, plain, (![B_75]: ('#skF_1'(k2_relat_1('#skF_2'), B_75)=k1_xboole_0 | r1_tarski(k2_relat_1('#skF_2'), B_75))), inference(resolution, [status(thm)], [c_107, c_100])).
% 2.69/1.42  tff(c_40, plain, (![A_37]: (v3_relat_1(A_37) | ~r1_tarski(k2_relat_1(A_37), k1_tarski(k1_xboole_0)) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.69/1.42  tff(c_203, plain, (v3_relat_1('#skF_2') | ~v1_relat_1('#skF_2') | '#skF_1'(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_199, c_40])).
% 2.69/1.42  tff(c_212, plain, (v3_relat_1('#skF_2') | '#skF_1'(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_203])).
% 2.69/1.42  tff(c_213, plain, ('#skF_1'(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_61, c_212])).
% 2.69/1.42  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.69/1.42  tff(c_225, plain, (r2_hidden(k1_xboole_0, k2_relat_1('#skF_2')) | r1_tarski(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_213, c_6])).
% 2.69/1.42  tff(c_258, plain, (r1_tarski(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_225])).
% 2.69/1.42  tff(c_261, plain, (v3_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_258, c_40])).
% 2.69/1.42  tff(c_266, plain, (v3_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_261])).
% 2.69/1.42  tff(c_268, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_266])).
% 2.69/1.42  tff(c_270, plain, (~r1_tarski(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))), inference(splitRight, [status(thm)], [c_225])).
% 2.69/1.42  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.69/1.42  tff(c_222, plain, (~r2_hidden(k1_xboole_0, k1_tarski(k1_xboole_0)) | r1_tarski(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_213, c_4])).
% 2.69/1.42  tff(c_361, plain, (~r2_hidden(k1_xboole_0, k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_270, c_222])).
% 2.69/1.42  tff(c_364, plain, (v1_xboole_0(k1_tarski(k1_xboole_0)) | ~m1_subset_1(k1_xboole_0, k1_tarski(k1_xboole_0))), inference(resolution, [status(thm)], [c_34, c_361])).
% 2.69/1.42  tff(c_367, plain, (~m1_subset_1(k1_xboole_0, k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_64, c_364])).
% 2.69/1.42  tff(c_370, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_97, c_367])).
% 2.69/1.42  tff(c_374, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_370])).
% 2.69/1.42  tff(c_375, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_46])).
% 2.69/1.42  tff(c_376, plain, (v3_relat_1('#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 2.69/1.42  tff(c_501, plain, (![A_114]: (r1_tarski(k2_relat_1(A_114), k1_tarski(k1_xboole_0)) | ~v3_relat_1(A_114) | ~v1_relat_1(A_114))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.69/1.42  tff(c_48, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_2')) | ~v3_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.69/1.42  tff(c_394, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_376, c_48])).
% 2.69/1.42  tff(c_484, plain, (![C_110, B_111, A_112]: (r2_hidden(C_110, B_111) | ~r2_hidden(C_110, A_112) | ~r1_tarski(A_112, B_111))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.69/1.42  tff(c_493, plain, (![B_111]: (r2_hidden('#skF_3', B_111) | ~r1_tarski(k2_relat_1('#skF_2'), B_111))), inference(resolution, [status(thm)], [c_394, c_484])).
% 2.69/1.42  tff(c_505, plain, (r2_hidden('#skF_3', k1_tarski(k1_xboole_0)) | ~v3_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_501, c_493])).
% 2.69/1.42  tff(c_513, plain, (r2_hidden('#skF_3', k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_376, c_505])).
% 2.69/1.42  tff(c_32, plain, (![A_31, B_32]: (m1_subset_1(A_31, B_32) | ~r2_hidden(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.69/1.42  tff(c_522, plain, (m1_subset_1('#skF_3', k1_tarski(k1_xboole_0))), inference(resolution, [status(thm)], [c_513, c_32])).
% 2.69/1.42  tff(c_408, plain, (![A_92, B_93]: (r1_tarski(A_92, B_93) | ~m1_subset_1(A_92, k1_zfmisc_1(B_93)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.69/1.42  tff(c_411, plain, (![A_92]: (r1_tarski(A_92, k1_xboole_0) | ~m1_subset_1(A_92, k1_tarski(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_408])).
% 2.69/1.42  tff(c_527, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_522, c_411])).
% 2.69/1.42  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.69/1.42  tff(c_437, plain, (![B_102, A_103]: (B_102=A_103 | ~r1_tarski(B_102, A_103) | ~r1_tarski(A_103, B_102))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.69/1.42  tff(c_446, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_437])).
% 2.69/1.42  tff(c_530, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_527, c_446])).
% 2.69/1.42  tff(c_536, plain, $false, inference(negUnitSimplification, [status(thm)], [c_375, c_530])).
% 2.69/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.42  
% 2.69/1.42  Inference rules
% 2.69/1.42  ----------------------
% 2.69/1.42  #Ref     : 0
% 2.69/1.42  #Sup     : 102
% 2.69/1.42  #Fact    : 0
% 2.69/1.42  #Define  : 0
% 2.69/1.42  #Split   : 6
% 2.69/1.42  #Chain   : 0
% 2.69/1.42  #Close   : 0
% 2.69/1.42  
% 2.69/1.42  Ordering : KBO
% 2.69/1.42  
% 2.69/1.42  Simplification rules
% 2.69/1.42  ----------------------
% 2.69/1.42  #Subsume      : 6
% 2.69/1.42  #Demod        : 22
% 2.69/1.42  #Tautology    : 57
% 2.69/1.42  #SimpNegUnit  : 8
% 2.69/1.42  #BackRed      : 0
% 2.69/1.42  
% 2.69/1.42  #Partial instantiations: 0
% 2.69/1.42  #Strategies tried      : 1
% 2.69/1.42  
% 2.69/1.42  Timing (in seconds)
% 2.69/1.42  ----------------------
% 2.69/1.43  Preprocessing        : 0.32
% 2.69/1.43  Parsing              : 0.17
% 2.69/1.43  CNF conversion       : 0.02
% 2.69/1.43  Main loop            : 0.28
% 2.69/1.43  Inferencing          : 0.10
% 2.69/1.43  Reduction            : 0.08
% 2.69/1.43  Demodulation         : 0.06
% 2.69/1.43  BG Simplification    : 0.02
% 2.69/1.43  Subsumption          : 0.05
% 2.69/1.43  Abstraction          : 0.01
% 2.69/1.43  MUC search           : 0.00
% 2.69/1.43  Cooper               : 0.00
% 2.69/1.43  Total                : 0.64
% 2.69/1.43  Index Insertion      : 0.00
% 2.69/1.43  Index Deletion       : 0.00
% 2.69/1.43  Index Matching       : 0.00
% 2.69/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
