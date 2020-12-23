%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:28 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 137 expanded)
%              Number of leaves         :   25 (  57 expanded)
%              Depth                    :    7
%              Number of atoms          :   98 ( 248 expanded)
%              Number of equality atoms :   34 (  71 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B,C,D] :
            ( ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
              | r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(D,C)) )
           => r1_tarski(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
     => ( k2_zfmisc_1(A,B) = k1_xboole_0
        | ( r1_tarski(A,C)
          & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_12] : k3_xboole_0(A_12,A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r1_xboole_0(A_10,B_11)
      | k3_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_474,plain,(
    ! [A_99,B_100,C_101] :
      ( ~ r1_xboole_0(A_99,B_100)
      | ~ r2_hidden(C_101,k3_xboole_0(A_99,B_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_488,plain,(
    ! [A_102,C_103] :
      ( ~ r1_xboole_0(A_102,A_102)
      | ~ r2_hidden(C_103,A_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_474])).

tff(c_491,plain,(
    ! [C_103,B_11] :
      ( ~ r2_hidden(C_103,B_11)
      | k3_xboole_0(B_11,B_11) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_488])).

tff(c_495,plain,(
    ! [C_104,B_105] :
      ( ~ r2_hidden(C_104,B_105)
      | k1_xboole_0 != B_105 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_491])).

tff(c_505,plain,(
    ! [A_106] :
      ( k1_xboole_0 != A_106
      | v1_xboole_0(A_106) ) ),
    inference(resolution,[status(thm)],[c_4,c_495])).

tff(c_442,plain,(
    ! [A_90,B_91] :
      ( r2_hidden('#skF_2'(A_90,B_91),A_90)
      | r1_tarski(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_454,plain,(
    ! [A_95,B_96] :
      ( ~ v1_xboole_0(A_95)
      | r1_tarski(A_95,B_96) ) ),
    inference(resolution,[status(thm)],[c_442,c_2])).

tff(c_32,plain,(
    ~ r1_tarski('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_462,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_454,c_32])).

tff(c_516,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(resolution,[status(thm)],[c_505,c_462])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_517,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_505,c_36])).

tff(c_98,plain,(
    ! [A_45,B_46,C_47] :
      ( ~ r1_xboole_0(A_45,B_46)
      | ~ r2_hidden(C_47,k3_xboole_0(A_45,B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_112,plain,(
    ! [A_48,C_49] :
      ( ~ r1_xboole_0(A_48,A_48)
      | ~ r2_hidden(C_49,A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_98])).

tff(c_115,plain,(
    ! [C_49,B_11] :
      ( ~ r2_hidden(C_49,B_11)
      | k3_xboole_0(B_11,B_11) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_112])).

tff(c_119,plain,(
    ! [C_50,B_51] :
      ( ~ r2_hidden(C_50,B_51)
      | k1_xboole_0 != B_51 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_115])).

tff(c_140,plain,(
    ! [A_54] :
      ( k1_xboole_0 != A_54
      | v1_xboole_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_4,c_119])).

tff(c_148,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_140,c_36])).

tff(c_82,plain,(
    ! [A_40,B_41] :
      ( r2_hidden('#skF_2'(A_40,B_41),A_40)
      | r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_93,plain,(
    ! [A_43,B_44] :
      ( ~ v1_xboole_0(A_43)
      | r1_tarski(A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_82,c_2])).

tff(c_97,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_93,c_32])).

tff(c_147,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(resolution,[status(thm)],[c_140,c_97])).

tff(c_34,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_5','#skF_4'),k2_zfmisc_1('#skF_7','#skF_6'))
    | r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_80,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_273,plain,(
    ! [A_76,C_77,B_78,D_79] :
      ( r1_tarski(A_76,C_77)
      | k2_zfmisc_1(A_76,B_78) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_76,B_78),k2_zfmisc_1(C_77,D_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_303,plain,
    ( r1_tarski('#skF_4','#skF_6')
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_80,c_273])).

tff(c_308,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_303])).

tff(c_22,plain,(
    ! [B_20,A_19] :
      ( k1_xboole_0 = B_20
      | k1_xboole_0 = A_19
      | k2_zfmisc_1(A_19,B_20) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_320,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_22])).

tff(c_328,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_147,c_320])).

tff(c_330,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_303])).

tff(c_406,plain,(
    ! [B_86,D_87,A_88,C_89] :
      ( r1_tarski(B_86,D_87)
      | k2_zfmisc_1(A_88,B_86) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_88,B_86),k2_zfmisc_1(C_89,D_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_419,plain,
    ( r1_tarski('#skF_5','#skF_7')
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_80,c_406])).

tff(c_439,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_330,c_32,c_419])).

tff(c_440,plain,(
    r1_tarski(k2_zfmisc_1('#skF_5','#skF_4'),k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_672,plain,(
    ! [A_132,C_133,B_134,D_135] :
      ( r1_tarski(A_132,C_133)
      | k2_zfmisc_1(A_132,B_134) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_132,B_134),k2_zfmisc_1(C_133,D_135)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_685,plain,
    ( r1_tarski('#skF_5','#skF_7')
    | k2_zfmisc_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_440,c_672])).

tff(c_704,plain,(
    k2_zfmisc_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_685])).

tff(c_720,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_704,c_22])).

tff(c_728,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_516,c_517,c_720])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:10:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.50  
% 2.75/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.50  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 2.75/1.50  
% 2.75/1.50  %Foreground sorts:
% 2.75/1.50  
% 2.75/1.50  
% 2.75/1.50  %Background operators:
% 2.75/1.50  
% 2.75/1.50  
% 2.75/1.50  %Foreground operators:
% 2.75/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.75/1.50  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.75/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.75/1.50  tff('#skF_7', type, '#skF_7': $i).
% 2.75/1.50  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.75/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.75/1.50  tff('#skF_5', type, '#skF_5': $i).
% 2.75/1.50  tff('#skF_6', type, '#skF_6': $i).
% 2.75/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.75/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.75/1.50  tff('#skF_4', type, '#skF_4': $i).
% 2.75/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.75/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.75/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.75/1.50  
% 2.75/1.52  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.75/1.52  tff(f_44, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.75/1.52  tff(f_42, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.75/1.52  tff(f_58, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.75/1.52  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.75/1.52  tff(f_83, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B, C, D]: ((r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) | r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(D, C))) => r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_zfmisc_1)).
% 2.75/1.52  tff(f_72, axiom, (![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 2.75/1.52  tff(f_64, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.75/1.52  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.75/1.52  tff(c_16, plain, (![A_12]: (k3_xboole_0(A_12, A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.75/1.52  tff(c_14, plain, (![A_10, B_11]: (r1_xboole_0(A_10, B_11) | k3_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.75/1.52  tff(c_474, plain, (![A_99, B_100, C_101]: (~r1_xboole_0(A_99, B_100) | ~r2_hidden(C_101, k3_xboole_0(A_99, B_100)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.75/1.52  tff(c_488, plain, (![A_102, C_103]: (~r1_xboole_0(A_102, A_102) | ~r2_hidden(C_103, A_102))), inference(superposition, [status(thm), theory('equality')], [c_16, c_474])).
% 2.75/1.52  tff(c_491, plain, (![C_103, B_11]: (~r2_hidden(C_103, B_11) | k3_xboole_0(B_11, B_11)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_488])).
% 2.75/1.52  tff(c_495, plain, (![C_104, B_105]: (~r2_hidden(C_104, B_105) | k1_xboole_0!=B_105)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_491])).
% 2.75/1.52  tff(c_505, plain, (![A_106]: (k1_xboole_0!=A_106 | v1_xboole_0(A_106))), inference(resolution, [status(thm)], [c_4, c_495])).
% 2.75/1.52  tff(c_442, plain, (![A_90, B_91]: (r2_hidden('#skF_2'(A_90, B_91), A_90) | r1_tarski(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.75/1.52  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.75/1.52  tff(c_454, plain, (![A_95, B_96]: (~v1_xboole_0(A_95) | r1_tarski(A_95, B_96))), inference(resolution, [status(thm)], [c_442, c_2])).
% 2.75/1.52  tff(c_32, plain, (~r1_tarski('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.75/1.52  tff(c_462, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_454, c_32])).
% 2.75/1.52  tff(c_516, plain, (k1_xboole_0!='#skF_5'), inference(resolution, [status(thm)], [c_505, c_462])).
% 2.75/1.52  tff(c_36, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.75/1.52  tff(c_517, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_505, c_36])).
% 2.75/1.52  tff(c_98, plain, (![A_45, B_46, C_47]: (~r1_xboole_0(A_45, B_46) | ~r2_hidden(C_47, k3_xboole_0(A_45, B_46)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.75/1.52  tff(c_112, plain, (![A_48, C_49]: (~r1_xboole_0(A_48, A_48) | ~r2_hidden(C_49, A_48))), inference(superposition, [status(thm), theory('equality')], [c_16, c_98])).
% 2.75/1.52  tff(c_115, plain, (![C_49, B_11]: (~r2_hidden(C_49, B_11) | k3_xboole_0(B_11, B_11)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_112])).
% 2.75/1.52  tff(c_119, plain, (![C_50, B_51]: (~r2_hidden(C_50, B_51) | k1_xboole_0!=B_51)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_115])).
% 2.75/1.52  tff(c_140, plain, (![A_54]: (k1_xboole_0!=A_54 | v1_xboole_0(A_54))), inference(resolution, [status(thm)], [c_4, c_119])).
% 2.75/1.52  tff(c_148, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_140, c_36])).
% 2.75/1.52  tff(c_82, plain, (![A_40, B_41]: (r2_hidden('#skF_2'(A_40, B_41), A_40) | r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.75/1.52  tff(c_93, plain, (![A_43, B_44]: (~v1_xboole_0(A_43) | r1_tarski(A_43, B_44))), inference(resolution, [status(thm)], [c_82, c_2])).
% 2.75/1.52  tff(c_97, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_93, c_32])).
% 2.75/1.52  tff(c_147, plain, (k1_xboole_0!='#skF_5'), inference(resolution, [status(thm)], [c_140, c_97])).
% 2.75/1.52  tff(c_34, plain, (r1_tarski(k2_zfmisc_1('#skF_5', '#skF_4'), k2_zfmisc_1('#skF_7', '#skF_6')) | r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.75/1.52  tff(c_80, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_34])).
% 2.75/1.52  tff(c_273, plain, (![A_76, C_77, B_78, D_79]: (r1_tarski(A_76, C_77) | k2_zfmisc_1(A_76, B_78)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_76, B_78), k2_zfmisc_1(C_77, D_79)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.75/1.52  tff(c_303, plain, (r1_tarski('#skF_4', '#skF_6') | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_80, c_273])).
% 2.75/1.52  tff(c_308, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_303])).
% 2.75/1.52  tff(c_22, plain, (![B_20, A_19]: (k1_xboole_0=B_20 | k1_xboole_0=A_19 | k2_zfmisc_1(A_19, B_20)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.75/1.52  tff(c_320, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_308, c_22])).
% 2.75/1.52  tff(c_328, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_147, c_320])).
% 2.75/1.52  tff(c_330, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_303])).
% 2.75/1.52  tff(c_406, plain, (![B_86, D_87, A_88, C_89]: (r1_tarski(B_86, D_87) | k2_zfmisc_1(A_88, B_86)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_88, B_86), k2_zfmisc_1(C_89, D_87)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.75/1.52  tff(c_419, plain, (r1_tarski('#skF_5', '#skF_7') | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_80, c_406])).
% 2.75/1.52  tff(c_439, plain, $false, inference(negUnitSimplification, [status(thm)], [c_330, c_32, c_419])).
% 2.75/1.52  tff(c_440, plain, (r1_tarski(k2_zfmisc_1('#skF_5', '#skF_4'), k2_zfmisc_1('#skF_7', '#skF_6'))), inference(splitRight, [status(thm)], [c_34])).
% 2.75/1.52  tff(c_672, plain, (![A_132, C_133, B_134, D_135]: (r1_tarski(A_132, C_133) | k2_zfmisc_1(A_132, B_134)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_132, B_134), k2_zfmisc_1(C_133, D_135)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.75/1.52  tff(c_685, plain, (r1_tarski('#skF_5', '#skF_7') | k2_zfmisc_1('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_440, c_672])).
% 2.75/1.52  tff(c_704, plain, (k2_zfmisc_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_32, c_685])).
% 2.75/1.52  tff(c_720, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_704, c_22])).
% 2.75/1.52  tff(c_728, plain, $false, inference(negUnitSimplification, [status(thm)], [c_516, c_517, c_720])).
% 2.75/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.52  
% 2.75/1.52  Inference rules
% 2.75/1.52  ----------------------
% 2.75/1.52  #Ref     : 0
% 2.75/1.52  #Sup     : 154
% 2.75/1.52  #Fact    : 0
% 2.75/1.52  #Define  : 0
% 2.75/1.52  #Split   : 2
% 2.75/1.52  #Chain   : 0
% 2.75/1.52  #Close   : 0
% 2.75/1.52  
% 2.75/1.52  Ordering : KBO
% 2.75/1.52  
% 2.75/1.52  Simplification rules
% 2.75/1.52  ----------------------
% 2.75/1.52  #Subsume      : 35
% 2.75/1.52  #Demod        : 30
% 2.75/1.52  #Tautology    : 45
% 2.75/1.52  #SimpNegUnit  : 6
% 2.75/1.52  #BackRed      : 2
% 2.75/1.52  
% 2.75/1.52  #Partial instantiations: 0
% 2.75/1.52  #Strategies tried      : 1
% 2.75/1.52  
% 2.75/1.52  Timing (in seconds)
% 2.75/1.52  ----------------------
% 2.75/1.52  Preprocessing        : 0.37
% 2.75/1.52  Parsing              : 0.21
% 2.75/1.52  CNF conversion       : 0.02
% 2.75/1.52  Main loop            : 0.33
% 2.75/1.52  Inferencing          : 0.13
% 2.75/1.52  Reduction            : 0.09
% 2.75/1.52  Demodulation         : 0.06
% 2.75/1.52  BG Simplification    : 0.02
% 2.75/1.52  Subsumption          : 0.06
% 2.75/1.52  Abstraction          : 0.01
% 2.75/1.52  MUC search           : 0.00
% 2.75/1.52  Cooper               : 0.00
% 2.75/1.52  Total                : 0.73
% 2.75/1.52  Index Insertion      : 0.00
% 2.75/1.52  Index Deletion       : 0.00
% 2.75/1.52  Index Matching       : 0.00
% 2.75/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
