%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:57 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   61 (  76 expanded)
%              Number of leaves         :   31 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :   76 ( 124 expanded)
%              Number of equality atoms :    7 (  11 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,A)
       => ( A != k1_xboole_0
         => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_84,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_79,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_81,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_52,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_91,plain,(
    ! [B_60,A_61] :
      ( v1_xboole_0(B_60)
      | ~ m1_subset_1(B_60,A_61)
      | ~ v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_99,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_91])).

tff(c_100,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_36,plain,(
    ! [B_44,A_43] :
      ( r2_hidden(B_44,A_43)
      | ~ m1_subset_1(B_44,A_43)
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_30,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(k1_tarski(A_39),B_40)
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_46,plain,(
    ! [A_47] : ~ v1_xboole_0(k1_zfmisc_1(A_47)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_42,plain,(
    ! [A_45] : k2_subset_1(A_45) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_44,plain,(
    ! [A_46] : m1_subset_1(k2_subset_1(A_46),k1_zfmisc_1(A_46)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_53,plain,(
    ! [A_46] : m1_subset_1(A_46,k1_zfmisc_1(A_46)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44])).

tff(c_32,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(k1_zfmisc_1(A_41),k1_zfmisc_1(B_42))
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_187,plain,(
    ! [C_87,B_88,A_89] :
      ( r2_hidden(C_87,B_88)
      | ~ r2_hidden(C_87,A_89)
      | ~ r1_tarski(A_89,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_263,plain,(
    ! [B_103,B_104,A_105] :
      ( r2_hidden(B_103,B_104)
      | ~ r1_tarski(A_105,B_104)
      | ~ m1_subset_1(B_103,A_105)
      | v1_xboole_0(A_105) ) ),
    inference(resolution,[status(thm)],[c_36,c_187])).

tff(c_269,plain,(
    ! [B_103,B_42,A_41] :
      ( r2_hidden(B_103,k1_zfmisc_1(B_42))
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_41))
      | v1_xboole_0(k1_zfmisc_1(A_41))
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(resolution,[status(thm)],[c_32,c_263])).

tff(c_373,plain,(
    ! [B_126,B_127,A_128] :
      ( r2_hidden(B_126,k1_zfmisc_1(B_127))
      | ~ m1_subset_1(B_126,k1_zfmisc_1(A_128))
      | ~ r1_tarski(A_128,B_127) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_269])).

tff(c_414,plain,(
    ! [A_135,B_136] :
      ( r2_hidden(A_135,k1_zfmisc_1(B_136))
      | ~ r1_tarski(A_135,B_136) ) ),
    inference(resolution,[status(thm)],[c_53,c_373])).

tff(c_34,plain,(
    ! [B_44,A_43] :
      ( m1_subset_1(B_44,A_43)
      | ~ r2_hidden(B_44,A_43)
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_423,plain,(
    ! [A_135,B_136] :
      ( m1_subset_1(A_135,k1_zfmisc_1(B_136))
      | v1_xboole_0(k1_zfmisc_1(B_136))
      | ~ r1_tarski(A_135,B_136) ) ),
    inference(resolution,[status(thm)],[c_414,c_34])).

tff(c_433,plain,(
    ! [A_137,B_138] :
      ( m1_subset_1(A_137,k1_zfmisc_1(B_138))
      | ~ r1_tarski(A_137,B_138) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_423])).

tff(c_48,plain,(
    ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_451,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_433,c_48])).

tff(c_459,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_451])).

tff(c_462,plain,
    ( ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_459])).

tff(c_465,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_462])).

tff(c_467,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_465])).

tff(c_469,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_476,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_469,c_12])).

tff(c_480,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_476])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:52:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.40  
% 2.53/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.40  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.53/1.40  
% 2.53/1.40  %Foreground sorts:
% 2.53/1.40  
% 2.53/1.40  
% 2.53/1.40  %Background operators:
% 2.53/1.40  
% 2.53/1.40  
% 2.53/1.40  %Foreground operators:
% 2.53/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.53/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.53/1.40  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.53/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.53/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.53/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.53/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.53/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.53/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.53/1.40  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.53/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.53/1.40  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.53/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.53/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.53/1.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.53/1.40  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.53/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.53/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.53/1.40  
% 2.53/1.42  tff(f_92, negated_conjecture, ~(![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 2.53/1.42  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.53/1.42  tff(f_60, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.53/1.42  tff(f_84, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.53/1.42  tff(f_79, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.53/1.42  tff(f_81, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.53/1.42  tff(f_64, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.53/1.42  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.53/1.42  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.53/1.42  tff(c_50, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.53/1.42  tff(c_52, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.53/1.42  tff(c_91, plain, (![B_60, A_61]: (v1_xboole_0(B_60) | ~m1_subset_1(B_60, A_61) | ~v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.53/1.42  tff(c_99, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_91])).
% 2.53/1.42  tff(c_100, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_99])).
% 2.53/1.42  tff(c_36, plain, (![B_44, A_43]: (r2_hidden(B_44, A_43) | ~m1_subset_1(B_44, A_43) | v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.53/1.42  tff(c_30, plain, (![A_39, B_40]: (r1_tarski(k1_tarski(A_39), B_40) | ~r2_hidden(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.53/1.42  tff(c_46, plain, (![A_47]: (~v1_xboole_0(k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.53/1.42  tff(c_42, plain, (![A_45]: (k2_subset_1(A_45)=A_45)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.53/1.42  tff(c_44, plain, (![A_46]: (m1_subset_1(k2_subset_1(A_46), k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.53/1.42  tff(c_53, plain, (![A_46]: (m1_subset_1(A_46, k1_zfmisc_1(A_46)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44])).
% 2.53/1.42  tff(c_32, plain, (![A_41, B_42]: (r1_tarski(k1_zfmisc_1(A_41), k1_zfmisc_1(B_42)) | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.53/1.42  tff(c_187, plain, (![C_87, B_88, A_89]: (r2_hidden(C_87, B_88) | ~r2_hidden(C_87, A_89) | ~r1_tarski(A_89, B_88))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.53/1.42  tff(c_263, plain, (![B_103, B_104, A_105]: (r2_hidden(B_103, B_104) | ~r1_tarski(A_105, B_104) | ~m1_subset_1(B_103, A_105) | v1_xboole_0(A_105))), inference(resolution, [status(thm)], [c_36, c_187])).
% 2.53/1.42  tff(c_269, plain, (![B_103, B_42, A_41]: (r2_hidden(B_103, k1_zfmisc_1(B_42)) | ~m1_subset_1(B_103, k1_zfmisc_1(A_41)) | v1_xboole_0(k1_zfmisc_1(A_41)) | ~r1_tarski(A_41, B_42))), inference(resolution, [status(thm)], [c_32, c_263])).
% 2.53/1.42  tff(c_373, plain, (![B_126, B_127, A_128]: (r2_hidden(B_126, k1_zfmisc_1(B_127)) | ~m1_subset_1(B_126, k1_zfmisc_1(A_128)) | ~r1_tarski(A_128, B_127))), inference(negUnitSimplification, [status(thm)], [c_46, c_269])).
% 2.53/1.42  tff(c_414, plain, (![A_135, B_136]: (r2_hidden(A_135, k1_zfmisc_1(B_136)) | ~r1_tarski(A_135, B_136))), inference(resolution, [status(thm)], [c_53, c_373])).
% 2.53/1.42  tff(c_34, plain, (![B_44, A_43]: (m1_subset_1(B_44, A_43) | ~r2_hidden(B_44, A_43) | v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.53/1.42  tff(c_423, plain, (![A_135, B_136]: (m1_subset_1(A_135, k1_zfmisc_1(B_136)) | v1_xboole_0(k1_zfmisc_1(B_136)) | ~r1_tarski(A_135, B_136))), inference(resolution, [status(thm)], [c_414, c_34])).
% 2.53/1.42  tff(c_433, plain, (![A_137, B_138]: (m1_subset_1(A_137, k1_zfmisc_1(B_138)) | ~r1_tarski(A_137, B_138))), inference(negUnitSimplification, [status(thm)], [c_46, c_423])).
% 2.53/1.42  tff(c_48, plain, (~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.53/1.42  tff(c_451, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_433, c_48])).
% 2.53/1.42  tff(c_459, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_451])).
% 2.53/1.42  tff(c_462, plain, (~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_459])).
% 2.53/1.42  tff(c_465, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_462])).
% 2.53/1.42  tff(c_467, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_465])).
% 2.53/1.42  tff(c_469, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_99])).
% 2.53/1.42  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.53/1.42  tff(c_476, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_469, c_12])).
% 2.53/1.42  tff(c_480, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_476])).
% 2.53/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.42  
% 2.53/1.42  Inference rules
% 2.53/1.42  ----------------------
% 2.53/1.42  #Ref     : 0
% 2.53/1.42  #Sup     : 89
% 2.53/1.42  #Fact    : 0
% 2.53/1.42  #Define  : 0
% 2.53/1.42  #Split   : 1
% 2.53/1.42  #Chain   : 0
% 2.53/1.42  #Close   : 0
% 2.53/1.42  
% 2.53/1.42  Ordering : KBO
% 2.53/1.42  
% 2.53/1.42  Simplification rules
% 2.53/1.42  ----------------------
% 2.53/1.42  #Subsume      : 21
% 2.53/1.42  #Demod        : 3
% 2.53/1.42  #Tautology    : 27
% 2.53/1.42  #SimpNegUnit  : 17
% 2.53/1.42  #BackRed      : 0
% 2.53/1.42  
% 2.53/1.42  #Partial instantiations: 0
% 2.53/1.42  #Strategies tried      : 1
% 2.53/1.42  
% 2.53/1.42  Timing (in seconds)
% 2.53/1.42  ----------------------
% 2.53/1.42  Preprocessing        : 0.34
% 2.53/1.42  Parsing              : 0.19
% 2.53/1.42  CNF conversion       : 0.02
% 2.53/1.42  Main loop            : 0.26
% 2.53/1.42  Inferencing          : 0.11
% 2.53/1.42  Reduction            : 0.07
% 2.53/1.42  Demodulation         : 0.05
% 2.53/1.42  BG Simplification    : 0.02
% 2.53/1.42  Subsumption          : 0.05
% 2.53/1.42  Abstraction          : 0.01
% 2.53/1.42  MUC search           : 0.00
% 2.53/1.42  Cooper               : 0.00
% 2.53/1.42  Total                : 0.63
% 2.53/1.42  Index Insertion      : 0.00
% 2.53/1.42  Index Deletion       : 0.00
% 2.53/1.42  Index Matching       : 0.00
% 2.53/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
