%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:06 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   69 (  94 expanded)
%              Number of leaves         :   34 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :   82 ( 128 expanded)
%              Number of equality atoms :   27 (  49 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_4 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_62,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_88,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_91,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_68,plain,(
    ! [A_28] : k1_subset_1(A_28) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_76,plain,
    ( k1_subset_1('#skF_8') != '#skF_9'
    | ~ r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_84,plain,
    ( k1_xboole_0 != '#skF_9'
    | ~ r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_76])).

tff(c_122,plain,(
    ~ r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_82,plain,
    ( r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9'))
    | k1_subset_1('#skF_8') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_83,plain,
    ( r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9'))
    | k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_82])).

tff(c_123,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_83])).

tff(c_46,plain,(
    ! [A_20] : k4_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_126,plain,(
    ! [A_20] : k4_xboole_0(A_20,'#skF_9') = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_46])).

tff(c_74,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_297,plain,(
    ! [A_76,B_77] :
      ( k4_xboole_0(A_76,B_77) = k3_subset_1(A_76,B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_307,plain,(
    k4_xboole_0('#skF_8','#skF_9') = k3_subset_1('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_74,c_297])).

tff(c_311,plain,(
    k3_subset_1('#skF_8','#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_307])).

tff(c_312,plain,(
    ~ r1_tarski('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_122])).

tff(c_72,plain,(
    ! [A_31] : ~ v1_xboole_0(k1_zfmisc_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_257,plain,(
    ! [B_74,A_75] :
      ( r2_hidden(B_74,A_75)
      | ~ m1_subset_1(B_74,A_75)
      | v1_xboole_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_48,plain,(
    ! [C_25,A_21] :
      ( r1_tarski(C_25,A_21)
      | ~ r2_hidden(C_25,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_286,plain,(
    ! [B_74,A_21] :
      ( r1_tarski(B_74,A_21)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_21))
      | v1_xboole_0(k1_zfmisc_1(A_21)) ) ),
    inference(resolution,[status(thm)],[c_257,c_48])).

tff(c_317,plain,(
    ! [B_78,A_79] :
      ( r1_tarski(B_78,A_79)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_79)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_286])).

tff(c_327,plain,(
    r1_tarski('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_74,c_317])).

tff(c_333,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_312,c_327])).

tff(c_334,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_38,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_5'(A_13),A_13)
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_335,plain,(
    r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_347,plain,(
    ! [A_82,B_83] :
      ( k3_xboole_0(A_82,B_83) = A_82
      | ~ r1_tarski(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_351,plain,(
    k3_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9')) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_335,c_347])).

tff(c_439,plain,(
    ! [D_104,B_105,A_106] :
      ( r2_hidden(D_104,B_105)
      | ~ r2_hidden(D_104,k3_xboole_0(A_106,B_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_647,plain,(
    ! [D_121] :
      ( r2_hidden(D_121,k3_subset_1('#skF_8','#skF_9'))
      | ~ r2_hidden(D_121,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_439])).

tff(c_545,plain,(
    ! [A_112,B_113] :
      ( k4_xboole_0(A_112,B_113) = k3_subset_1(A_112,B_113)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(A_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_558,plain,(
    k4_xboole_0('#skF_8','#skF_9') = k3_subset_1('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_74,c_545])).

tff(c_22,plain,(
    ! [D_12,B_8,A_7] :
      ( ~ r2_hidden(D_12,B_8)
      | ~ r2_hidden(D_12,k4_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_569,plain,(
    ! [D_12] :
      ( ~ r2_hidden(D_12,'#skF_9')
      | ~ r2_hidden(D_12,k3_subset_1('#skF_8','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_22])).

tff(c_660,plain,(
    ! [D_122] : ~ r2_hidden(D_122,'#skF_9') ),
    inference(resolution,[status(thm)],[c_647,c_569])).

tff(c_668,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_38,c_660])).

tff(c_673,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_334,c_668])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:07:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.43  
% 2.60/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.44  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_4 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7
% 2.60/1.44  
% 2.60/1.44  %Foreground sorts:
% 2.60/1.44  
% 2.60/1.44  
% 2.60/1.44  %Background operators:
% 2.60/1.44  
% 2.60/1.44  
% 2.60/1.44  %Foreground operators:
% 2.60/1.44  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.60/1.44  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.60/1.44  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.60/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.60/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.60/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.60/1.44  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.60/1.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.60/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.60/1.44  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.60/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.60/1.44  tff('#skF_9', type, '#skF_9': $i).
% 2.60/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.60/1.44  tff('#skF_8', type, '#skF_8': $i).
% 2.60/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.44  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.60/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.44  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.60/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.60/1.44  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.60/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.60/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.60/1.44  
% 2.60/1.45  tff(f_84, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.60/1.45  tff(f_98, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 2.60/1.45  tff(f_62, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.60/1.45  tff(f_88, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.60/1.45  tff(f_91, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.60/1.45  tff(f_82, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.60/1.45  tff(f_69, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.60/1.45  tff(f_52, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.60/1.45  tff(f_58, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.60/1.45  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.60/1.45  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.60/1.45  tff(c_68, plain, (![A_28]: (k1_subset_1(A_28)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.60/1.45  tff(c_76, plain, (k1_subset_1('#skF_8')!='#skF_9' | ~r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.60/1.45  tff(c_84, plain, (k1_xboole_0!='#skF_9' | ~r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_76])).
% 2.60/1.45  tff(c_122, plain, (~r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(splitLeft, [status(thm)], [c_84])).
% 2.60/1.45  tff(c_82, plain, (r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9')) | k1_subset_1('#skF_8')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.60/1.45  tff(c_83, plain, (r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9')) | k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_82])).
% 2.60/1.45  tff(c_123, plain, (k1_xboole_0='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_122, c_83])).
% 2.60/1.45  tff(c_46, plain, (![A_20]: (k4_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.60/1.45  tff(c_126, plain, (![A_20]: (k4_xboole_0(A_20, '#skF_9')=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_123, c_46])).
% 2.60/1.45  tff(c_74, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.60/1.45  tff(c_297, plain, (![A_76, B_77]: (k4_xboole_0(A_76, B_77)=k3_subset_1(A_76, B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.60/1.45  tff(c_307, plain, (k4_xboole_0('#skF_8', '#skF_9')=k3_subset_1('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_74, c_297])).
% 2.60/1.45  tff(c_311, plain, (k3_subset_1('#skF_8', '#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_126, c_307])).
% 2.60/1.45  tff(c_312, plain, (~r1_tarski('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_311, c_122])).
% 2.60/1.45  tff(c_72, plain, (![A_31]: (~v1_xboole_0(k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.60/1.45  tff(c_257, plain, (![B_74, A_75]: (r2_hidden(B_74, A_75) | ~m1_subset_1(B_74, A_75) | v1_xboole_0(A_75))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.60/1.45  tff(c_48, plain, (![C_25, A_21]: (r1_tarski(C_25, A_21) | ~r2_hidden(C_25, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.60/1.45  tff(c_286, plain, (![B_74, A_21]: (r1_tarski(B_74, A_21) | ~m1_subset_1(B_74, k1_zfmisc_1(A_21)) | v1_xboole_0(k1_zfmisc_1(A_21)))), inference(resolution, [status(thm)], [c_257, c_48])).
% 2.60/1.45  tff(c_317, plain, (![B_78, A_79]: (r1_tarski(B_78, A_79) | ~m1_subset_1(B_78, k1_zfmisc_1(A_79)))), inference(negUnitSimplification, [status(thm)], [c_72, c_286])).
% 2.60/1.45  tff(c_327, plain, (r1_tarski('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_74, c_317])).
% 2.60/1.45  tff(c_333, plain, $false, inference(negUnitSimplification, [status(thm)], [c_312, c_327])).
% 2.60/1.45  tff(c_334, plain, (k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_84])).
% 2.60/1.45  tff(c_38, plain, (![A_13]: (r2_hidden('#skF_5'(A_13), A_13) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.60/1.45  tff(c_335, plain, (r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(splitRight, [status(thm)], [c_84])).
% 2.60/1.45  tff(c_347, plain, (![A_82, B_83]: (k3_xboole_0(A_82, B_83)=A_82 | ~r1_tarski(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.60/1.45  tff(c_351, plain, (k3_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9'))='#skF_9'), inference(resolution, [status(thm)], [c_335, c_347])).
% 2.60/1.45  tff(c_439, plain, (![D_104, B_105, A_106]: (r2_hidden(D_104, B_105) | ~r2_hidden(D_104, k3_xboole_0(A_106, B_105)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.60/1.45  tff(c_647, plain, (![D_121]: (r2_hidden(D_121, k3_subset_1('#skF_8', '#skF_9')) | ~r2_hidden(D_121, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_351, c_439])).
% 2.60/1.45  tff(c_545, plain, (![A_112, B_113]: (k4_xboole_0(A_112, B_113)=k3_subset_1(A_112, B_113) | ~m1_subset_1(B_113, k1_zfmisc_1(A_112)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.60/1.45  tff(c_558, plain, (k4_xboole_0('#skF_8', '#skF_9')=k3_subset_1('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_74, c_545])).
% 2.60/1.45  tff(c_22, plain, (![D_12, B_8, A_7]: (~r2_hidden(D_12, B_8) | ~r2_hidden(D_12, k4_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.60/1.45  tff(c_569, plain, (![D_12]: (~r2_hidden(D_12, '#skF_9') | ~r2_hidden(D_12, k3_subset_1('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_558, c_22])).
% 2.60/1.45  tff(c_660, plain, (![D_122]: (~r2_hidden(D_122, '#skF_9'))), inference(resolution, [status(thm)], [c_647, c_569])).
% 2.60/1.45  tff(c_668, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_38, c_660])).
% 2.60/1.45  tff(c_673, plain, $false, inference(negUnitSimplification, [status(thm)], [c_334, c_668])).
% 2.60/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.45  
% 2.60/1.45  Inference rules
% 2.60/1.45  ----------------------
% 2.60/1.45  #Ref     : 0
% 2.60/1.45  #Sup     : 131
% 2.60/1.45  #Fact    : 0
% 2.60/1.45  #Define  : 0
% 2.60/1.45  #Split   : 3
% 2.60/1.45  #Chain   : 0
% 2.60/1.45  #Close   : 0
% 2.60/1.45  
% 2.60/1.45  Ordering : KBO
% 2.60/1.45  
% 2.60/1.45  Simplification rules
% 2.60/1.45  ----------------------
% 2.60/1.45  #Subsume      : 17
% 2.60/1.45  #Demod        : 13
% 2.60/1.45  #Tautology    : 56
% 2.60/1.45  #SimpNegUnit  : 11
% 2.60/1.45  #BackRed      : 6
% 2.60/1.45  
% 2.60/1.45  #Partial instantiations: 0
% 2.60/1.45  #Strategies tried      : 1
% 2.60/1.45  
% 2.60/1.45  Timing (in seconds)
% 2.60/1.45  ----------------------
% 2.60/1.45  Preprocessing        : 0.36
% 2.60/1.45  Parsing              : 0.17
% 2.60/1.45  CNF conversion       : 0.03
% 2.60/1.45  Main loop            : 0.28
% 2.60/1.45  Inferencing          : 0.10
% 2.60/1.45  Reduction            : 0.08
% 2.60/1.45  Demodulation         : 0.06
% 2.60/1.45  BG Simplification    : 0.02
% 2.60/1.45  Subsumption          : 0.05
% 2.60/1.45  Abstraction          : 0.02
% 2.60/1.45  MUC search           : 0.00
% 2.60/1.45  Cooper               : 0.00
% 2.60/1.45  Total                : 0.67
% 2.60/1.45  Index Insertion      : 0.00
% 2.60/1.45  Index Deletion       : 0.00
% 2.60/1.45  Index Matching       : 0.00
% 2.60/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
