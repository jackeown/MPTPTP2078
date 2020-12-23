%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:30 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   64 (  94 expanded)
%              Number of leaves         :   31 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :   99 ( 183 expanded)
%              Number of equality atoms :    4 (   7 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_65,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_50,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_48,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_46,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_36,plain,(
    ! [A_41,B_43] :
      ( r1_tarski(k2_relat_1(A_41),k2_relat_1(B_43))
      | ~ r1_tarski(A_41,B_43)
      | ~ v1_relat_1(B_43)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_105,plain,(
    ! [A_71] :
      ( k2_xboole_0(k1_relat_1(A_71),k2_relat_1(A_71)) = k3_relat_1(A_71)
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,k2_xboole_0(C_8,B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_111,plain,(
    ! [A_6,A_71] :
      ( r1_tarski(A_6,k3_relat_1(A_71))
      | ~ r1_tarski(A_6,k2_relat_1(A_71))
      | ~ v1_relat_1(A_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_8])).

tff(c_38,plain,(
    ! [A_41,B_43] :
      ( r1_tarski(k1_relat_1(A_41),k1_relat_1(B_43))
      | ~ r1_tarski(A_41,B_43)
      | ~ v1_relat_1(B_43)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_117,plain,(
    ! [C_72,B_73,A_74] :
      ( r2_hidden(C_72,B_73)
      | ~ r2_hidden(C_72,A_74)
      | ~ r1_tarski(A_74,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_120,plain,(
    ! [A_1,B_2,B_73] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_73)
      | ~ r1_tarski(A_1,B_73)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_117])).

tff(c_225,plain,(
    ! [C_106,A_107] :
      ( r2_hidden(k4_tarski(C_106,'#skF_5'(A_107,k1_relat_1(A_107),C_106)),A_107)
      | ~ r2_hidden(C_106,k1_relat_1(A_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_42,plain,(
    ! [A_44,C_46,B_45] :
      ( r2_hidden(A_44,k3_relat_1(C_46))
      | ~ r2_hidden(k4_tarski(A_44,B_45),C_46)
      | ~ v1_relat_1(C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_248,plain,(
    ! [C_110,A_111] :
      ( r2_hidden(C_110,k3_relat_1(A_111))
      | ~ v1_relat_1(A_111)
      | ~ r2_hidden(C_110,k1_relat_1(A_111)) ) ),
    inference(resolution,[status(thm)],[c_225,c_42])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_334,plain,(
    ! [A_127,A_128] :
      ( r1_tarski(A_127,k3_relat_1(A_128))
      | ~ v1_relat_1(A_128)
      | ~ r2_hidden('#skF_1'(A_127,k3_relat_1(A_128)),k1_relat_1(A_128)) ) ),
    inference(resolution,[status(thm)],[c_248,c_4])).

tff(c_343,plain,(
    ! [A_128,A_1] :
      ( ~ v1_relat_1(A_128)
      | ~ r1_tarski(A_1,k1_relat_1(A_128))
      | r1_tarski(A_1,k3_relat_1(A_128)) ) ),
    inference(resolution,[status(thm)],[c_120,c_334])).

tff(c_34,plain,(
    ! [A_40] :
      ( k2_xboole_0(k1_relat_1(A_40),k2_relat_1(A_40)) = k3_relat_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_136,plain,(
    ! [A_83,C_84,B_85] :
      ( r1_tarski(k2_xboole_0(A_83,C_84),B_85)
      | ~ r1_tarski(C_84,B_85)
      | ~ r1_tarski(A_83,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_526,plain,(
    ! [A_166,B_167] :
      ( r1_tarski(k3_relat_1(A_166),B_167)
      | ~ r1_tarski(k2_relat_1(A_166),B_167)
      | ~ r1_tarski(k1_relat_1(A_166),B_167)
      | ~ v1_relat_1(A_166) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_136])).

tff(c_44,plain,(
    ~ r1_tarski(k3_relat_1('#skF_6'),k3_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_569,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),k3_relat_1('#skF_7'))
    | ~ r1_tarski(k1_relat_1('#skF_6'),k3_relat_1('#skF_7'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_526,c_44])).

tff(c_589,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),k3_relat_1('#skF_7'))
    | ~ r1_tarski(k1_relat_1('#skF_6'),k3_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_569])).

tff(c_590,plain,(
    ~ r1_tarski(k1_relat_1('#skF_6'),k3_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_589])).

tff(c_593,plain,
    ( ~ v1_relat_1('#skF_7')
    | ~ r1_tarski(k1_relat_1('#skF_6'),k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_343,c_590])).

tff(c_599,plain,(
    ~ r1_tarski(k1_relat_1('#skF_6'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_593])).

tff(c_605,plain,
    ( ~ r1_tarski('#skF_6','#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_599])).

tff(c_609,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_605])).

tff(c_610,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),k3_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_589])).

tff(c_617,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),k2_relat_1('#skF_7'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_111,c_610])).

tff(c_623,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_617])).

tff(c_661,plain,
    ( ~ r1_tarski('#skF_6','#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_623])).

tff(c_665,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_661])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:30:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.42  
% 2.73/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.42  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 2.73/1.42  
% 2.73/1.42  %Foreground sorts:
% 2.73/1.42  
% 2.73/1.42  
% 2.73/1.42  %Background operators:
% 2.73/1.42  
% 2.73/1.42  
% 2.73/1.42  %Foreground operators:
% 2.73/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.42  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.73/1.42  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.73/1.42  tff('#skF_7', type, '#skF_7': $i).
% 2.73/1.42  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.73/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.73/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.73/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.73/1.42  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.73/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.73/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.73/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.42  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.73/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.73/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.73/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.73/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.73/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.73/1.42  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.73/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.73/1.42  
% 2.73/1.44  tff(f_98, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 2.73/1.44  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 2.73/1.44  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 2.73/1.44  tff(f_36, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.73/1.44  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.73/1.44  tff(f_65, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 2.73/1.44  tff(f_88, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relat_1)).
% 2.73/1.44  tff(f_42, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 2.73/1.44  tff(c_50, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.73/1.44  tff(c_48, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.73/1.44  tff(c_46, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.73/1.44  tff(c_36, plain, (![A_41, B_43]: (r1_tarski(k2_relat_1(A_41), k2_relat_1(B_43)) | ~r1_tarski(A_41, B_43) | ~v1_relat_1(B_43) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.73/1.44  tff(c_105, plain, (![A_71]: (k2_xboole_0(k1_relat_1(A_71), k2_relat_1(A_71))=k3_relat_1(A_71) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.73/1.44  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, k2_xboole_0(C_8, B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.73/1.44  tff(c_111, plain, (![A_6, A_71]: (r1_tarski(A_6, k3_relat_1(A_71)) | ~r1_tarski(A_6, k2_relat_1(A_71)) | ~v1_relat_1(A_71))), inference(superposition, [status(thm), theory('equality')], [c_105, c_8])).
% 2.73/1.44  tff(c_38, plain, (![A_41, B_43]: (r1_tarski(k1_relat_1(A_41), k1_relat_1(B_43)) | ~r1_tarski(A_41, B_43) | ~v1_relat_1(B_43) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.73/1.44  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.73/1.44  tff(c_117, plain, (![C_72, B_73, A_74]: (r2_hidden(C_72, B_73) | ~r2_hidden(C_72, A_74) | ~r1_tarski(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.73/1.44  tff(c_120, plain, (![A_1, B_2, B_73]: (r2_hidden('#skF_1'(A_1, B_2), B_73) | ~r1_tarski(A_1, B_73) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_117])).
% 2.73/1.44  tff(c_225, plain, (![C_106, A_107]: (r2_hidden(k4_tarski(C_106, '#skF_5'(A_107, k1_relat_1(A_107), C_106)), A_107) | ~r2_hidden(C_106, k1_relat_1(A_107)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.73/1.44  tff(c_42, plain, (![A_44, C_46, B_45]: (r2_hidden(A_44, k3_relat_1(C_46)) | ~r2_hidden(k4_tarski(A_44, B_45), C_46) | ~v1_relat_1(C_46))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.73/1.44  tff(c_248, plain, (![C_110, A_111]: (r2_hidden(C_110, k3_relat_1(A_111)) | ~v1_relat_1(A_111) | ~r2_hidden(C_110, k1_relat_1(A_111)))), inference(resolution, [status(thm)], [c_225, c_42])).
% 2.73/1.44  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.73/1.44  tff(c_334, plain, (![A_127, A_128]: (r1_tarski(A_127, k3_relat_1(A_128)) | ~v1_relat_1(A_128) | ~r2_hidden('#skF_1'(A_127, k3_relat_1(A_128)), k1_relat_1(A_128)))), inference(resolution, [status(thm)], [c_248, c_4])).
% 2.73/1.44  tff(c_343, plain, (![A_128, A_1]: (~v1_relat_1(A_128) | ~r1_tarski(A_1, k1_relat_1(A_128)) | r1_tarski(A_1, k3_relat_1(A_128)))), inference(resolution, [status(thm)], [c_120, c_334])).
% 2.73/1.44  tff(c_34, plain, (![A_40]: (k2_xboole_0(k1_relat_1(A_40), k2_relat_1(A_40))=k3_relat_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.73/1.44  tff(c_136, plain, (![A_83, C_84, B_85]: (r1_tarski(k2_xboole_0(A_83, C_84), B_85) | ~r1_tarski(C_84, B_85) | ~r1_tarski(A_83, B_85))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.73/1.44  tff(c_526, plain, (![A_166, B_167]: (r1_tarski(k3_relat_1(A_166), B_167) | ~r1_tarski(k2_relat_1(A_166), B_167) | ~r1_tarski(k1_relat_1(A_166), B_167) | ~v1_relat_1(A_166))), inference(superposition, [status(thm), theory('equality')], [c_34, c_136])).
% 2.73/1.44  tff(c_44, plain, (~r1_tarski(k3_relat_1('#skF_6'), k3_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.73/1.44  tff(c_569, plain, (~r1_tarski(k2_relat_1('#skF_6'), k3_relat_1('#skF_7')) | ~r1_tarski(k1_relat_1('#skF_6'), k3_relat_1('#skF_7')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_526, c_44])).
% 2.73/1.44  tff(c_589, plain, (~r1_tarski(k2_relat_1('#skF_6'), k3_relat_1('#skF_7')) | ~r1_tarski(k1_relat_1('#skF_6'), k3_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_569])).
% 2.73/1.44  tff(c_590, plain, (~r1_tarski(k1_relat_1('#skF_6'), k3_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_589])).
% 2.73/1.44  tff(c_593, plain, (~v1_relat_1('#skF_7') | ~r1_tarski(k1_relat_1('#skF_6'), k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_343, c_590])).
% 2.73/1.44  tff(c_599, plain, (~r1_tarski(k1_relat_1('#skF_6'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_593])).
% 2.73/1.44  tff(c_605, plain, (~r1_tarski('#skF_6', '#skF_7') | ~v1_relat_1('#skF_7') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_599])).
% 2.73/1.44  tff(c_609, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_605])).
% 2.73/1.44  tff(c_610, plain, (~r1_tarski(k2_relat_1('#skF_6'), k3_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_589])).
% 2.73/1.44  tff(c_617, plain, (~r1_tarski(k2_relat_1('#skF_6'), k2_relat_1('#skF_7')) | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_111, c_610])).
% 2.73/1.44  tff(c_623, plain, (~r1_tarski(k2_relat_1('#skF_6'), k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_617])).
% 2.73/1.44  tff(c_661, plain, (~r1_tarski('#skF_6', '#skF_7') | ~v1_relat_1('#skF_7') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_623])).
% 2.73/1.44  tff(c_665, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_661])).
% 2.73/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.44  
% 2.73/1.44  Inference rules
% 2.73/1.44  ----------------------
% 2.73/1.44  #Ref     : 0
% 2.73/1.44  #Sup     : 132
% 2.73/1.44  #Fact    : 0
% 2.73/1.44  #Define  : 0
% 2.73/1.44  #Split   : 3
% 2.73/1.44  #Chain   : 0
% 2.73/1.44  #Close   : 0
% 2.73/1.44  
% 2.73/1.44  Ordering : KBO
% 2.73/1.44  
% 2.73/1.44  Simplification rules
% 2.73/1.44  ----------------------
% 2.73/1.44  #Subsume      : 18
% 2.73/1.44  #Demod        : 20
% 2.73/1.44  #Tautology    : 14
% 2.73/1.44  #SimpNegUnit  : 1
% 2.73/1.44  #BackRed      : 1
% 2.73/1.44  
% 2.73/1.44  #Partial instantiations: 0
% 2.73/1.44  #Strategies tried      : 1
% 2.73/1.44  
% 2.73/1.44  Timing (in seconds)
% 2.73/1.44  ----------------------
% 2.73/1.44  Preprocessing        : 0.31
% 2.73/1.44  Parsing              : 0.16
% 2.73/1.44  CNF conversion       : 0.02
% 2.73/1.44  Main loop            : 0.35
% 2.73/1.44  Inferencing          : 0.13
% 2.73/1.44  Reduction            : 0.09
% 2.73/1.44  Demodulation         : 0.06
% 2.73/1.44  BG Simplification    : 0.02
% 2.73/1.44  Subsumption          : 0.09
% 2.73/1.44  Abstraction          : 0.02
% 2.73/1.44  MUC search           : 0.00
% 2.73/1.44  Cooper               : 0.00
% 2.73/1.44  Total                : 0.69
% 2.73/1.44  Index Insertion      : 0.00
% 2.73/1.44  Index Deletion       : 0.00
% 2.73/1.44  Index Matching       : 0.00
% 2.73/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
