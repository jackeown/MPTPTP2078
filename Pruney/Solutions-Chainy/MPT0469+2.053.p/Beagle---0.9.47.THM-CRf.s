%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:58 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 133 expanded)
%              Number of leaves         :   25 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :   61 ( 183 expanded)
%              Number of equality atoms :   20 (  65 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_2 > #skF_8 > #skF_7 > #skF_9 > #skF_5 > #skF_4 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_37,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_57,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_8,plain,(
    v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_35,plain,(
    ! [A_44] :
      ( k1_xboole_0 = A_44
      | ~ v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_39,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_35])).

tff(c_34,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_57,plain,
    ( k2_relat_1('#skF_2') != '#skF_2'
    | k1_relat_1('#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_39,c_39,c_39,c_34])).

tff(c_58,plain,(
    k1_relat_1('#skF_2') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_57])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_498,plain,(
    ! [C_75,A_76] :
      ( r2_hidden(k4_tarski(C_75,'#skF_6'(A_76,k1_relat_1(A_76),C_75)),A_76)
      | ~ r2_hidden(C_75,k1_relat_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_61,plain,(
    ! [A_55,C_56] :
      ( r2_hidden(k4_tarski('#skF_10'(A_55,k2_relat_1(A_55),C_56),C_56),A_55)
      | ~ r2_hidden(C_56,k2_relat_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ! [A_57,C_58] :
      ( ~ v1_xboole_0(A_57)
      | ~ r2_hidden(C_58,k2_relat_1(A_57)) ) ),
    inference(resolution,[status(thm)],[c_61,c_2])).

tff(c_85,plain,(
    ! [A_59] :
      ( ~ v1_xboole_0(A_59)
      | v1_xboole_0(k2_relat_1(A_59)) ) ),
    inference(resolution,[status(thm)],[c_4,c_74])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_40,plain,(
    ! [A_5] :
      ( A_5 = '#skF_2'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_6])).

tff(c_90,plain,(
    ! [A_60] :
      ( k2_relat_1(A_60) = '#skF_2'
      | ~ v1_xboole_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_85,c_40])).

tff(c_98,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_90])).

tff(c_73,plain,(
    ! [A_55,C_56] :
      ( ~ v1_xboole_0(A_55)
      | ~ r2_hidden(C_56,k2_relat_1(A_55)) ) ),
    inference(resolution,[status(thm)],[c_61,c_2])).

tff(c_105,plain,(
    ! [C_56] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ r2_hidden(C_56,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_73])).

tff(c_114,plain,(
    ! [C_56] : ~ r2_hidden(C_56,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_105])).

tff(c_531,plain,(
    ! [C_77] : ~ r2_hidden(C_77,k1_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_498,c_114])).

tff(c_546,plain,(
    v1_xboole_0(k1_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_4,c_531])).

tff(c_552,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_546,c_40])).

tff(c_557,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_552])).

tff(c_558,plain,(
    k2_relat_1('#skF_2') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_57])).

tff(c_567,plain,(
    ! [A_86,C_87] :
      ( r2_hidden(k4_tarski('#skF_10'(A_86,k2_relat_1(A_86),C_87),C_87),A_86)
      | ~ r2_hidden(C_87,k2_relat_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_580,plain,(
    ! [A_88,C_89] :
      ( ~ v1_xboole_0(A_88)
      | ~ r2_hidden(C_89,k2_relat_1(A_88)) ) ),
    inference(resolution,[status(thm)],[c_567,c_2])).

tff(c_613,plain,(
    ! [A_92] :
      ( ~ v1_xboole_0(A_92)
      | v1_xboole_0(k2_relat_1(A_92)) ) ),
    inference(resolution,[status(thm)],[c_4,c_580])).

tff(c_618,plain,(
    ! [A_93] :
      ( k2_relat_1(A_93) = '#skF_2'
      | ~ v1_xboole_0(A_93) ) ),
    inference(resolution,[status(thm)],[c_613,c_40])).

tff(c_624,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_618])).

tff(c_629,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_558,c_624])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:55:49 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.27  
% 2.27/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.27  %$ r2_hidden > v1_xboole_0 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_2 > #skF_8 > #skF_7 > #skF_9 > #skF_5 > #skF_4 > #skF_10
% 2.27/1.27  
% 2.27/1.27  %Foreground sorts:
% 2.27/1.27  
% 2.27/1.27  
% 2.27/1.27  %Background operators:
% 2.27/1.27  
% 2.27/1.27  
% 2.27/1.27  %Foreground operators:
% 2.27/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.27  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.27/1.27  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.27/1.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.27/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.27/1.27  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.27/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.27/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.27  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 2.27/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.27  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.27/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.27/1.27  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 2.27/1.27  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.27/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.27/1.27  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.27/1.27  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 2.27/1.27  
% 2.27/1.29  tff(f_37, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 2.27/1.29  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.27/1.29  tff(f_57, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.27/1.29  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.27/1.29  tff(f_45, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 2.27/1.29  tff(f_53, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 2.27/1.29  tff(c_8, plain, (v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.27/1.29  tff(c_35, plain, (![A_44]: (k1_xboole_0=A_44 | ~v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.27/1.29  tff(c_39, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_8, c_35])).
% 2.27/1.29  tff(c_34, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.27/1.29  tff(c_57, plain, (k2_relat_1('#skF_2')!='#skF_2' | k1_relat_1('#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_39, c_39, c_39, c_39, c_34])).
% 2.27/1.29  tff(c_58, plain, (k1_relat_1('#skF_2')!='#skF_2'), inference(splitLeft, [status(thm)], [c_57])).
% 2.27/1.29  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.27/1.29  tff(c_498, plain, (![C_75, A_76]: (r2_hidden(k4_tarski(C_75, '#skF_6'(A_76, k1_relat_1(A_76), C_75)), A_76) | ~r2_hidden(C_75, k1_relat_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.27/1.29  tff(c_61, plain, (![A_55, C_56]: (r2_hidden(k4_tarski('#skF_10'(A_55, k2_relat_1(A_55), C_56), C_56), A_55) | ~r2_hidden(C_56, k2_relat_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.27/1.29  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.27/1.29  tff(c_74, plain, (![A_57, C_58]: (~v1_xboole_0(A_57) | ~r2_hidden(C_58, k2_relat_1(A_57)))), inference(resolution, [status(thm)], [c_61, c_2])).
% 2.27/1.29  tff(c_85, plain, (![A_59]: (~v1_xboole_0(A_59) | v1_xboole_0(k2_relat_1(A_59)))), inference(resolution, [status(thm)], [c_4, c_74])).
% 2.27/1.29  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.27/1.29  tff(c_40, plain, (![A_5]: (A_5='#skF_2' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_6])).
% 2.27/1.29  tff(c_90, plain, (![A_60]: (k2_relat_1(A_60)='#skF_2' | ~v1_xboole_0(A_60))), inference(resolution, [status(thm)], [c_85, c_40])).
% 2.27/1.29  tff(c_98, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_8, c_90])).
% 2.27/1.29  tff(c_73, plain, (![A_55, C_56]: (~v1_xboole_0(A_55) | ~r2_hidden(C_56, k2_relat_1(A_55)))), inference(resolution, [status(thm)], [c_61, c_2])).
% 2.27/1.29  tff(c_105, plain, (![C_56]: (~v1_xboole_0('#skF_2') | ~r2_hidden(C_56, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_98, c_73])).
% 2.27/1.29  tff(c_114, plain, (![C_56]: (~r2_hidden(C_56, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_105])).
% 2.27/1.29  tff(c_531, plain, (![C_77]: (~r2_hidden(C_77, k1_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_498, c_114])).
% 2.27/1.29  tff(c_546, plain, (v1_xboole_0(k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_4, c_531])).
% 2.27/1.29  tff(c_552, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_546, c_40])).
% 2.27/1.29  tff(c_557, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_552])).
% 2.27/1.29  tff(c_558, plain, (k2_relat_1('#skF_2')!='#skF_2'), inference(splitRight, [status(thm)], [c_57])).
% 2.27/1.29  tff(c_567, plain, (![A_86, C_87]: (r2_hidden(k4_tarski('#skF_10'(A_86, k2_relat_1(A_86), C_87), C_87), A_86) | ~r2_hidden(C_87, k2_relat_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.27/1.29  tff(c_580, plain, (![A_88, C_89]: (~v1_xboole_0(A_88) | ~r2_hidden(C_89, k2_relat_1(A_88)))), inference(resolution, [status(thm)], [c_567, c_2])).
% 2.27/1.29  tff(c_613, plain, (![A_92]: (~v1_xboole_0(A_92) | v1_xboole_0(k2_relat_1(A_92)))), inference(resolution, [status(thm)], [c_4, c_580])).
% 2.27/1.29  tff(c_618, plain, (![A_93]: (k2_relat_1(A_93)='#skF_2' | ~v1_xboole_0(A_93))), inference(resolution, [status(thm)], [c_613, c_40])).
% 2.27/1.29  tff(c_624, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_8, c_618])).
% 2.27/1.29  tff(c_629, plain, $false, inference(negUnitSimplification, [status(thm)], [c_558, c_624])).
% 2.27/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.29  
% 2.27/1.29  Inference rules
% 2.27/1.29  ----------------------
% 2.27/1.29  #Ref     : 0
% 2.27/1.29  #Sup     : 137
% 2.27/1.29  #Fact    : 0
% 2.27/1.29  #Define  : 0
% 2.27/1.29  #Split   : 1
% 2.27/1.29  #Chain   : 0
% 2.27/1.29  #Close   : 0
% 2.27/1.29  
% 2.27/1.29  Ordering : KBO
% 2.27/1.29  
% 2.27/1.29  Simplification rules
% 2.27/1.29  ----------------------
% 2.27/1.29  #Subsume      : 23
% 2.27/1.29  #Demod        : 115
% 2.27/1.29  #Tautology    : 73
% 2.27/1.29  #SimpNegUnit  : 2
% 2.27/1.29  #BackRed      : 1
% 2.27/1.29  
% 2.27/1.29  #Partial instantiations: 0
% 2.27/1.29  #Strategies tried      : 1
% 2.27/1.29  
% 2.27/1.29  Timing (in seconds)
% 2.27/1.29  ----------------------
% 2.27/1.29  Preprocessing        : 0.28
% 2.27/1.29  Parsing              : 0.15
% 2.27/1.29  CNF conversion       : 0.03
% 2.27/1.29  Main loop            : 0.26
% 2.27/1.29  Inferencing          : 0.10
% 2.27/1.29  Reduction            : 0.07
% 2.27/1.29  Demodulation         : 0.05
% 2.27/1.29  BG Simplification    : 0.01
% 2.27/1.29  Subsumption          : 0.06
% 2.27/1.29  Abstraction          : 0.01
% 2.27/1.29  MUC search           : 0.00
% 2.27/1.29  Cooper               : 0.00
% 2.27/1.29  Total                : 0.57
% 2.27/1.29  Index Insertion      : 0.00
% 2.27/1.29  Index Deletion       : 0.00
% 2.27/1.29  Index Matching       : 0.00
% 2.27/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
