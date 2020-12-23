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
% DateTime   : Thu Dec  3 09:57:00 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 119 expanded)
%              Number of leaves         :   30 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :   87 ( 238 expanded)
%              Number of equality atoms :    7 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,A)
       => ! [C] :
            ( m1_subset_1(C,A)
           => ( A != k1_xboole_0
             => m1_subset_1(k2_tarski(B,C),k1_zfmisc_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_subset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_83,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_78,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_80,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_52,plain,(
    m1_subset_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_67,plain,(
    ! [B_53,A_54] :
      ( v1_xboole_0(B_53)
      | ~ m1_subset_1(B_53,A_54)
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_78,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_67])).

tff(c_80,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_50,plain,(
    m1_subset_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_34,plain,(
    ! [B_42,A_41] :
      ( r2_hidden(B_42,A_41)
      | ~ m1_subset_1(B_42,A_41)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_24,plain,(
    ! [A_36,B_37,C_38] :
      ( r1_tarski(k2_tarski(A_36,B_37),C_38)
      | ~ r2_hidden(B_37,C_38)
      | ~ r2_hidden(A_36,C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_44,plain,(
    ! [A_45] : ~ v1_xboole_0(k1_zfmisc_1(A_45)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_40,plain,(
    ! [A_43] : k2_subset_1(A_43) = A_43 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_42,plain,(
    ! [A_44] : m1_subset_1(k2_subset_1(A_44),k1_zfmisc_1(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_53,plain,(
    ! [A_44] : m1_subset_1(A_44,k1_zfmisc_1(A_44)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42])).

tff(c_30,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(k1_zfmisc_1(A_39),k1_zfmisc_1(B_40))
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_180,plain,(
    ! [C_86,B_87,A_88] :
      ( r2_hidden(C_86,B_87)
      | ~ r2_hidden(C_86,A_88)
      | ~ r1_tarski(A_88,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_273,plain,(
    ! [B_111,B_112,A_113] :
      ( r2_hidden(B_111,B_112)
      | ~ r1_tarski(A_113,B_112)
      | ~ m1_subset_1(B_111,A_113)
      | v1_xboole_0(A_113) ) ),
    inference(resolution,[status(thm)],[c_34,c_180])).

tff(c_277,plain,(
    ! [B_111,B_40,A_39] :
      ( r2_hidden(B_111,k1_zfmisc_1(B_40))
      | ~ m1_subset_1(B_111,k1_zfmisc_1(A_39))
      | v1_xboole_0(k1_zfmisc_1(A_39))
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(resolution,[status(thm)],[c_30,c_273])).

tff(c_299,plain,(
    ! [B_119,B_120,A_121] :
      ( r2_hidden(B_119,k1_zfmisc_1(B_120))
      | ~ m1_subset_1(B_119,k1_zfmisc_1(A_121))
      | ~ r1_tarski(A_121,B_120) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_277])).

tff(c_313,plain,(
    ! [A_122,B_123] :
      ( r2_hidden(A_122,k1_zfmisc_1(B_123))
      | ~ r1_tarski(A_122,B_123) ) ),
    inference(resolution,[status(thm)],[c_53,c_299])).

tff(c_32,plain,(
    ! [B_42,A_41] :
      ( m1_subset_1(B_42,A_41)
      | ~ r2_hidden(B_42,A_41)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_322,plain,(
    ! [A_122,B_123] :
      ( m1_subset_1(A_122,k1_zfmisc_1(B_123))
      | v1_xboole_0(k1_zfmisc_1(B_123))
      | ~ r1_tarski(A_122,B_123) ) ),
    inference(resolution,[status(thm)],[c_313,c_32])).

tff(c_332,plain,(
    ! [A_124,B_125] :
      ( m1_subset_1(A_124,k1_zfmisc_1(B_125))
      | ~ r1_tarski(A_124,B_125) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_322])).

tff(c_46,plain,(
    ~ m1_subset_1(k2_tarski('#skF_3','#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_350,plain,(
    ~ r1_tarski(k2_tarski('#skF_3','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_332,c_46])).

tff(c_357,plain,
    ( ~ r2_hidden('#skF_4','#skF_2')
    | ~ r2_hidden('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_350])).

tff(c_359,plain,(
    ~ r2_hidden('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_357])).

tff(c_371,plain,
    ( ~ m1_subset_1('#skF_3','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_359])).

tff(c_374,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_371])).

tff(c_376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_374])).

tff(c_377,plain,(
    ~ r2_hidden('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_357])).

tff(c_381,plain,
    ( ~ m1_subset_1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_377])).

tff(c_384,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_381])).

tff(c_386,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_384])).

tff(c_388,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_396,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_388,c_8])).

tff(c_400,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_396])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:53:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.32  
% 2.06/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.32  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.06/1.32  
% 2.06/1.32  %Foreground sorts:
% 2.06/1.32  
% 2.06/1.32  
% 2.06/1.32  %Background operators:
% 2.06/1.32  
% 2.06/1.32  
% 2.06/1.32  %Foreground operators:
% 2.06/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.06/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.06/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.06/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.06/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.06/1.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.06/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.06/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.06/1.32  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.06/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.06/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.06/1.32  
% 2.45/1.34  tff(f_94, negated_conjecture, ~(![A, B]: (m1_subset_1(B, A) => (![C]: (m1_subset_1(C, A) => (~(A = k1_xboole_0) => m1_subset_1(k2_tarski(B, C), k1_zfmisc_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_subset_1)).
% 2.45/1.34  tff(f_76, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.45/1.34  tff(f_59, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.45/1.34  tff(f_83, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.45/1.34  tff(f_78, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.45/1.34  tff(f_80, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.45/1.34  tff(f_63, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.45/1.34  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.45/1.34  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.45/1.34  tff(c_48, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.45/1.34  tff(c_52, plain, (m1_subset_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.45/1.34  tff(c_67, plain, (![B_53, A_54]: (v1_xboole_0(B_53) | ~m1_subset_1(B_53, A_54) | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.45/1.34  tff(c_78, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_67])).
% 2.45/1.34  tff(c_80, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_78])).
% 2.45/1.34  tff(c_50, plain, (m1_subset_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.45/1.34  tff(c_34, plain, (![B_42, A_41]: (r2_hidden(B_42, A_41) | ~m1_subset_1(B_42, A_41) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.45/1.34  tff(c_24, plain, (![A_36, B_37, C_38]: (r1_tarski(k2_tarski(A_36, B_37), C_38) | ~r2_hidden(B_37, C_38) | ~r2_hidden(A_36, C_38))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.45/1.34  tff(c_44, plain, (![A_45]: (~v1_xboole_0(k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.45/1.34  tff(c_40, plain, (![A_43]: (k2_subset_1(A_43)=A_43)), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.45/1.34  tff(c_42, plain, (![A_44]: (m1_subset_1(k2_subset_1(A_44), k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.45/1.34  tff(c_53, plain, (![A_44]: (m1_subset_1(A_44, k1_zfmisc_1(A_44)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42])).
% 2.45/1.34  tff(c_30, plain, (![A_39, B_40]: (r1_tarski(k1_zfmisc_1(A_39), k1_zfmisc_1(B_40)) | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.45/1.34  tff(c_180, plain, (![C_86, B_87, A_88]: (r2_hidden(C_86, B_87) | ~r2_hidden(C_86, A_88) | ~r1_tarski(A_88, B_87))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.45/1.34  tff(c_273, plain, (![B_111, B_112, A_113]: (r2_hidden(B_111, B_112) | ~r1_tarski(A_113, B_112) | ~m1_subset_1(B_111, A_113) | v1_xboole_0(A_113))), inference(resolution, [status(thm)], [c_34, c_180])).
% 2.45/1.34  tff(c_277, plain, (![B_111, B_40, A_39]: (r2_hidden(B_111, k1_zfmisc_1(B_40)) | ~m1_subset_1(B_111, k1_zfmisc_1(A_39)) | v1_xboole_0(k1_zfmisc_1(A_39)) | ~r1_tarski(A_39, B_40))), inference(resolution, [status(thm)], [c_30, c_273])).
% 2.45/1.34  tff(c_299, plain, (![B_119, B_120, A_121]: (r2_hidden(B_119, k1_zfmisc_1(B_120)) | ~m1_subset_1(B_119, k1_zfmisc_1(A_121)) | ~r1_tarski(A_121, B_120))), inference(negUnitSimplification, [status(thm)], [c_44, c_277])).
% 2.45/1.34  tff(c_313, plain, (![A_122, B_123]: (r2_hidden(A_122, k1_zfmisc_1(B_123)) | ~r1_tarski(A_122, B_123))), inference(resolution, [status(thm)], [c_53, c_299])).
% 2.45/1.34  tff(c_32, plain, (![B_42, A_41]: (m1_subset_1(B_42, A_41) | ~r2_hidden(B_42, A_41) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.45/1.34  tff(c_322, plain, (![A_122, B_123]: (m1_subset_1(A_122, k1_zfmisc_1(B_123)) | v1_xboole_0(k1_zfmisc_1(B_123)) | ~r1_tarski(A_122, B_123))), inference(resolution, [status(thm)], [c_313, c_32])).
% 2.45/1.34  tff(c_332, plain, (![A_124, B_125]: (m1_subset_1(A_124, k1_zfmisc_1(B_125)) | ~r1_tarski(A_124, B_125))), inference(negUnitSimplification, [status(thm)], [c_44, c_322])).
% 2.45/1.34  tff(c_46, plain, (~m1_subset_1(k2_tarski('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.45/1.34  tff(c_350, plain, (~r1_tarski(k2_tarski('#skF_3', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_332, c_46])).
% 2.45/1.34  tff(c_357, plain, (~r2_hidden('#skF_4', '#skF_2') | ~r2_hidden('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_350])).
% 2.45/1.34  tff(c_359, plain, (~r2_hidden('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_357])).
% 2.45/1.34  tff(c_371, plain, (~m1_subset_1('#skF_3', '#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_359])).
% 2.45/1.34  tff(c_374, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_371])).
% 2.45/1.34  tff(c_376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_374])).
% 2.45/1.34  tff(c_377, plain, (~r2_hidden('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_357])).
% 2.45/1.34  tff(c_381, plain, (~m1_subset_1('#skF_4', '#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_377])).
% 2.45/1.34  tff(c_384, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_381])).
% 2.45/1.34  tff(c_386, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_384])).
% 2.45/1.34  tff(c_388, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_78])).
% 2.45/1.34  tff(c_8, plain, (![A_6]: (k1_xboole_0=A_6 | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.45/1.34  tff(c_396, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_388, c_8])).
% 2.45/1.34  tff(c_400, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_396])).
% 2.45/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.34  
% 2.45/1.34  Inference rules
% 2.45/1.34  ----------------------
% 2.45/1.34  #Ref     : 0
% 2.45/1.34  #Sup     : 71
% 2.45/1.34  #Fact    : 0
% 2.45/1.34  #Define  : 0
% 2.45/1.34  #Split   : 3
% 2.45/1.34  #Chain   : 0
% 2.45/1.34  #Close   : 0
% 2.45/1.34  
% 2.45/1.34  Ordering : KBO
% 2.45/1.34  
% 2.45/1.34  Simplification rules
% 2.45/1.34  ----------------------
% 2.45/1.34  #Subsume      : 20
% 2.45/1.34  #Demod        : 4
% 2.45/1.34  #Tautology    : 21
% 2.45/1.34  #SimpNegUnit  : 10
% 2.45/1.34  #BackRed      : 0
% 2.45/1.34  
% 2.45/1.34  #Partial instantiations: 0
% 2.45/1.34  #Strategies tried      : 1
% 2.45/1.34  
% 2.45/1.34  Timing (in seconds)
% 2.45/1.34  ----------------------
% 2.45/1.34  Preprocessing        : 0.31
% 2.45/1.34  Parsing              : 0.16
% 2.45/1.34  CNF conversion       : 0.02
% 2.45/1.34  Main loop            : 0.23
% 2.45/1.34  Inferencing          : 0.09
% 2.45/1.34  Reduction            : 0.06
% 2.45/1.34  Demodulation         : 0.04
% 2.45/1.34  BG Simplification    : 0.02
% 2.45/1.34  Subsumption          : 0.04
% 2.45/1.34  Abstraction          : 0.01
% 2.45/1.34  MUC search           : 0.00
% 2.45/1.34  Cooper               : 0.00
% 2.45/1.34  Total                : 0.56
% 2.45/1.34  Index Insertion      : 0.00
% 2.45/1.34  Index Deletion       : 0.00
% 2.45/1.34  Index Matching       : 0.00
% 2.45/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
