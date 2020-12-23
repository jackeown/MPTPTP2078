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
% DateTime   : Thu Dec  3 09:56:02 EST 2020

% Result     : Theorem 4.25s
% Output     : CNFRefutation 4.25s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 117 expanded)
%              Number of leaves         :   29 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :   81 ( 176 expanded)
%              Number of equality atoms :   24 (  60 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_74,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_52,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_54,plain,(
    ! [A_26] : k1_subset_1(A_26) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_68,plain,
    ( r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7'))
    | k1_subset_1('#skF_6') = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_69,plain,
    ( r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7'))
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_68])).

tff(c_133,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_32,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_134,plain,(
    ! [A_18] : k4_xboole_0(A_18,'#skF_7') = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_32])).

tff(c_193,plain,(
    ! [D_56,B_57,A_58] :
      ( ~ r2_hidden(D_56,B_57)
      | ~ r2_hidden(D_56,k4_xboole_0(A_58,B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_202,plain,(
    ! [D_59,A_60] :
      ( ~ r2_hidden(D_59,'#skF_7')
      | ~ r2_hidden(D_59,A_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_193])).

tff(c_428,plain,(
    ! [B_77,A_78] :
      ( ~ r2_hidden('#skF_1'('#skF_7',B_77),A_78)
      | r1_tarski('#skF_7',B_77) ) ),
    inference(resolution,[status(thm)],[c_8,c_202])).

tff(c_442,plain,(
    ! [B_4] : r1_tarski('#skF_7',B_4) ),
    inference(resolution,[status(thm)],[c_8,c_428])).

tff(c_62,plain,
    ( k1_subset_1('#skF_6') != '#skF_7'
    | ~ r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_70,plain,
    ( k1_xboole_0 != '#skF_7'
    | ~ r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_62])).

tff(c_132,plain,(
    ~ r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_448,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_132])).

tff(c_449,plain,(
    r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_452,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_449,c_132])).

tff(c_453,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_455,plain,(
    r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_453,c_69])).

tff(c_663,plain,(
    ! [C_108,B_109,A_110] :
      ( r2_hidden(C_108,B_109)
      | ~ r2_hidden(C_108,A_110)
      | ~ r1_tarski(A_110,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2670,plain,(
    ! [A_224,B_225,B_226] :
      ( r2_hidden('#skF_1'(A_224,B_225),B_226)
      | ~ r1_tarski(A_224,B_226)
      | r1_tarski(A_224,B_225) ) ),
    inference(resolution,[status(thm)],[c_8,c_663])).

tff(c_60,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_817,plain,(
    ! [A_118,B_119] :
      ( k4_xboole_0(A_118,B_119) = k3_subset_1(A_118,B_119)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(A_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_830,plain,(
    k4_xboole_0('#skF_6','#skF_7') = k3_subset_1('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_817])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( ~ r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_891,plain,(
    ! [D_13] :
      ( ~ r2_hidden(D_13,'#skF_7')
      | ~ r2_hidden(D_13,k3_subset_1('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_830,c_12])).

tff(c_2741,plain,(
    ! [A_227,B_228] :
      ( ~ r2_hidden('#skF_1'(A_227,B_228),'#skF_7')
      | ~ r1_tarski(A_227,k3_subset_1('#skF_6','#skF_7'))
      | r1_tarski(A_227,B_228) ) ),
    inference(resolution,[status(thm)],[c_2670,c_891])).

tff(c_2752,plain,(
    ! [B_4] :
      ( ~ r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7'))
      | r1_tarski('#skF_7',B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_2741])).

tff(c_2763,plain,(
    ! [B_229] : r1_tarski('#skF_7',B_229) ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_2752])).

tff(c_30,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2778,plain,(
    ! [B_230] : k3_xboole_0('#skF_7',B_230) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_2763,c_30])).

tff(c_512,plain,(
    ! [A_96,B_97] :
      ( r2_hidden('#skF_1'(A_96,B_97),A_96)
      | r1_tarski(A_96,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_471,plain,(
    ! [D_83,B_84,A_85] :
      ( ~ r2_hidden(D_83,B_84)
      | ~ r2_hidden(D_83,k4_xboole_0(A_85,B_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_474,plain,(
    ! [D_83,A_18] :
      ( ~ r2_hidden(D_83,k1_xboole_0)
      | ~ r2_hidden(D_83,A_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_471])).

tff(c_738,plain,(
    ! [B_113,A_114] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0,B_113),A_114)
      | r1_tarski(k1_xboole_0,B_113) ) ),
    inference(resolution,[status(thm)],[c_512,c_474])).

tff(c_755,plain,(
    ! [B_115] : r1_tarski(k1_xboole_0,B_115) ),
    inference(resolution,[status(thm)],[c_8,c_738])).

tff(c_760,plain,(
    ! [B_116] : k3_xboole_0(k1_xboole_0,B_116) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_755,c_30])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_775,plain,(
    ! [B_116] : k3_xboole_0(B_116,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_760,c_2])).

tff(c_2783,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_2778,c_775])).

tff(c_2819,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_453,c_2783])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:36:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.25/1.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.25/1.79  
% 4.25/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.25/1.79  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 4.25/1.79  
% 4.25/1.79  %Foreground sorts:
% 4.25/1.79  
% 4.25/1.79  
% 4.25/1.79  %Background operators:
% 4.25/1.79  
% 4.25/1.79  
% 4.25/1.79  %Foreground operators:
% 4.25/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.25/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.25/1.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.25/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.25/1.79  tff('#skF_7', type, '#skF_7': $i).
% 4.25/1.79  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.25/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.25/1.79  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.25/1.79  tff('#skF_6', type, '#skF_6': $i).
% 4.25/1.79  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.25/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.25/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.25/1.79  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.25/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.25/1.79  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 4.25/1.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.25/1.79  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.25/1.79  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.25/1.79  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.25/1.79  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.25/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.25/1.79  
% 4.25/1.81  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.25/1.81  tff(f_74, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 4.25/1.81  tff(f_88, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 4.25/1.81  tff(f_52, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.25/1.81  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.25/1.81  tff(f_78, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.25/1.81  tff(f_50, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.25/1.81  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.25/1.81  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.25/1.81  tff(c_54, plain, (![A_26]: (k1_subset_1(A_26)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.25/1.81  tff(c_68, plain, (r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7')) | k1_subset_1('#skF_6')='#skF_7'), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.25/1.81  tff(c_69, plain, (r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7')) | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_68])).
% 4.25/1.81  tff(c_133, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_69])).
% 4.25/1.81  tff(c_32, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.25/1.81  tff(c_134, plain, (![A_18]: (k4_xboole_0(A_18, '#skF_7')=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_133, c_32])).
% 4.25/1.81  tff(c_193, plain, (![D_56, B_57, A_58]: (~r2_hidden(D_56, B_57) | ~r2_hidden(D_56, k4_xboole_0(A_58, B_57)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.25/1.81  tff(c_202, plain, (![D_59, A_60]: (~r2_hidden(D_59, '#skF_7') | ~r2_hidden(D_59, A_60))), inference(superposition, [status(thm), theory('equality')], [c_134, c_193])).
% 4.25/1.81  tff(c_428, plain, (![B_77, A_78]: (~r2_hidden('#skF_1'('#skF_7', B_77), A_78) | r1_tarski('#skF_7', B_77))), inference(resolution, [status(thm)], [c_8, c_202])).
% 4.25/1.81  tff(c_442, plain, (![B_4]: (r1_tarski('#skF_7', B_4))), inference(resolution, [status(thm)], [c_8, c_428])).
% 4.25/1.81  tff(c_62, plain, (k1_subset_1('#skF_6')!='#skF_7' | ~r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.25/1.81  tff(c_70, plain, (k1_xboole_0!='#skF_7' | ~r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_62])).
% 4.25/1.81  tff(c_132, plain, (~r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_70])).
% 4.25/1.81  tff(c_448, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_442, c_132])).
% 4.25/1.81  tff(c_449, plain, (r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_69])).
% 4.25/1.81  tff(c_452, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_449, c_132])).
% 4.25/1.81  tff(c_453, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_70])).
% 4.25/1.81  tff(c_455, plain, (r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_453, c_69])).
% 4.25/1.81  tff(c_663, plain, (![C_108, B_109, A_110]: (r2_hidden(C_108, B_109) | ~r2_hidden(C_108, A_110) | ~r1_tarski(A_110, B_109))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.25/1.81  tff(c_2670, plain, (![A_224, B_225, B_226]: (r2_hidden('#skF_1'(A_224, B_225), B_226) | ~r1_tarski(A_224, B_226) | r1_tarski(A_224, B_225))), inference(resolution, [status(thm)], [c_8, c_663])).
% 4.25/1.81  tff(c_60, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.25/1.81  tff(c_817, plain, (![A_118, B_119]: (k4_xboole_0(A_118, B_119)=k3_subset_1(A_118, B_119) | ~m1_subset_1(B_119, k1_zfmisc_1(A_118)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.25/1.81  tff(c_830, plain, (k4_xboole_0('#skF_6', '#skF_7')=k3_subset_1('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_60, c_817])).
% 4.25/1.81  tff(c_12, plain, (![D_13, B_9, A_8]: (~r2_hidden(D_13, B_9) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.25/1.81  tff(c_891, plain, (![D_13]: (~r2_hidden(D_13, '#skF_7') | ~r2_hidden(D_13, k3_subset_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_830, c_12])).
% 4.25/1.81  tff(c_2741, plain, (![A_227, B_228]: (~r2_hidden('#skF_1'(A_227, B_228), '#skF_7') | ~r1_tarski(A_227, k3_subset_1('#skF_6', '#skF_7')) | r1_tarski(A_227, B_228))), inference(resolution, [status(thm)], [c_2670, c_891])).
% 4.25/1.81  tff(c_2752, plain, (![B_4]: (~r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7')) | r1_tarski('#skF_7', B_4))), inference(resolution, [status(thm)], [c_8, c_2741])).
% 4.25/1.81  tff(c_2763, plain, (![B_229]: (r1_tarski('#skF_7', B_229))), inference(demodulation, [status(thm), theory('equality')], [c_455, c_2752])).
% 4.25/1.81  tff(c_30, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.25/1.81  tff(c_2778, plain, (![B_230]: (k3_xboole_0('#skF_7', B_230)='#skF_7')), inference(resolution, [status(thm)], [c_2763, c_30])).
% 4.25/1.81  tff(c_512, plain, (![A_96, B_97]: (r2_hidden('#skF_1'(A_96, B_97), A_96) | r1_tarski(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.25/1.81  tff(c_471, plain, (![D_83, B_84, A_85]: (~r2_hidden(D_83, B_84) | ~r2_hidden(D_83, k4_xboole_0(A_85, B_84)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.25/1.81  tff(c_474, plain, (![D_83, A_18]: (~r2_hidden(D_83, k1_xboole_0) | ~r2_hidden(D_83, A_18))), inference(superposition, [status(thm), theory('equality')], [c_32, c_471])).
% 4.25/1.81  tff(c_738, plain, (![B_113, A_114]: (~r2_hidden('#skF_1'(k1_xboole_0, B_113), A_114) | r1_tarski(k1_xboole_0, B_113))), inference(resolution, [status(thm)], [c_512, c_474])).
% 4.25/1.81  tff(c_755, plain, (![B_115]: (r1_tarski(k1_xboole_0, B_115))), inference(resolution, [status(thm)], [c_8, c_738])).
% 4.25/1.81  tff(c_760, plain, (![B_116]: (k3_xboole_0(k1_xboole_0, B_116)=k1_xboole_0)), inference(resolution, [status(thm)], [c_755, c_30])).
% 4.25/1.81  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.25/1.81  tff(c_775, plain, (![B_116]: (k3_xboole_0(B_116, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_760, c_2])).
% 4.25/1.81  tff(c_2783, plain, (k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_2778, c_775])).
% 4.25/1.81  tff(c_2819, plain, $false, inference(negUnitSimplification, [status(thm)], [c_453, c_2783])).
% 4.25/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.25/1.81  
% 4.25/1.81  Inference rules
% 4.25/1.81  ----------------------
% 4.25/1.81  #Ref     : 0
% 4.25/1.81  #Sup     : 608
% 4.25/1.81  #Fact    : 0
% 4.25/1.81  #Define  : 0
% 4.25/1.81  #Split   : 10
% 4.25/1.81  #Chain   : 0
% 4.25/1.81  #Close   : 0
% 4.25/1.81  
% 4.25/1.81  Ordering : KBO
% 4.25/1.81  
% 4.25/1.81  Simplification rules
% 4.25/1.81  ----------------------
% 4.25/1.81  #Subsume      : 54
% 4.25/1.81  #Demod        : 180
% 4.25/1.81  #Tautology    : 252
% 4.25/1.81  #SimpNegUnit  : 24
% 4.25/1.81  #BackRed      : 41
% 4.25/1.81  
% 4.25/1.81  #Partial instantiations: 0
% 4.25/1.81  #Strategies tried      : 1
% 4.25/1.81  
% 4.25/1.81  Timing (in seconds)
% 4.25/1.81  ----------------------
% 4.25/1.81  Preprocessing        : 0.33
% 4.25/1.81  Parsing              : 0.18
% 4.25/1.81  CNF conversion       : 0.02
% 4.25/1.81  Main loop            : 0.70
% 4.25/1.81  Inferencing          : 0.24
% 4.25/1.81  Reduction            : 0.22
% 4.25/1.81  Demodulation         : 0.16
% 4.25/1.81  BG Simplification    : 0.03
% 4.25/1.81  Subsumption          : 0.14
% 4.25/1.81  Abstraction          : 0.04
% 4.25/1.81  MUC search           : 0.00
% 4.25/1.81  Cooper               : 0.00
% 4.25/1.81  Total                : 1.06
% 4.25/1.81  Index Insertion      : 0.00
% 4.25/1.81  Index Deletion       : 0.00
% 4.25/1.81  Index Matching       : 0.00
% 4.25/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
