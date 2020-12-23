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
% DateTime   : Thu Dec  3 10:02:13 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 141 expanded)
%              Number of leaves         :   25 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :   96 ( 287 expanded)
%              Number of equality atoms :   14 (  36 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > #skF_4 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r2_hidden(k4_tarski(A,B),C)
        <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_44,plain,
    ( ~ r2_hidden('#skF_9',k11_relat_1('#skF_10','#skF_8'))
    | ~ r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_67,plain,(
    ~ r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_50,plain,
    ( r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_10')
    | r2_hidden('#skF_9',k11_relat_1('#skF_10','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_68,plain,(
    r2_hidden('#skF_9',k11_relat_1('#skF_10','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_50])).

tff(c_32,plain,(
    ! [A_48,B_50] :
      ( k9_relat_1(A_48,k1_tarski(B_50)) = k11_relat_1(A_48,B_50)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_77,plain,(
    ! [A_68,B_69,C_70] :
      ( r2_hidden('#skF_7'(A_68,B_69,C_70),B_69)
      | ~ r2_hidden(A_68,k9_relat_1(C_70,B_69))
      | ~ v1_relat_1(C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_90,plain,(
    ! [A_76,A_77,C_78] :
      ( '#skF_7'(A_76,k1_tarski(A_77),C_78) = A_77
      | ~ r2_hidden(A_76,k9_relat_1(C_78,k1_tarski(A_77)))
      | ~ v1_relat_1(C_78) ) ),
    inference(resolution,[status(thm)],[c_77,c_2])).

tff(c_284,plain,(
    ! [A_107,B_108,A_109] :
      ( '#skF_7'(A_107,k1_tarski(B_108),A_109) = B_108
      | ~ r2_hidden(A_107,k11_relat_1(A_109,B_108))
      | ~ v1_relat_1(A_109)
      | ~ v1_relat_1(A_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_90])).

tff(c_306,plain,
    ( '#skF_7'('#skF_9',k1_tarski('#skF_8'),'#skF_10') = '#skF_8'
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_68,c_284])).

tff(c_314,plain,(
    '#skF_7'('#skF_9',k1_tarski('#skF_8'),'#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_306])).

tff(c_38,plain,(
    ! [A_51,B_52,C_53] :
      ( r2_hidden(k4_tarski('#skF_7'(A_51,B_52,C_53),A_51),C_53)
      | ~ r2_hidden(A_51,k9_relat_1(C_53,B_52))
      | ~ v1_relat_1(C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_340,plain,
    ( r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_10')
    | ~ r2_hidden('#skF_9',k9_relat_1('#skF_10',k1_tarski('#skF_8')))
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_38])).

tff(c_350,plain,
    ( r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_10')
    | ~ r2_hidden('#skF_9',k9_relat_1('#skF_10',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_340])).

tff(c_351,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_10',k1_tarski('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_350])).

tff(c_362,plain,
    ( ~ r2_hidden('#skF_9',k11_relat_1('#skF_10','#skF_8'))
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_351])).

tff(c_368,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_68,c_362])).

tff(c_369,plain,(
    ~ r2_hidden('#skF_9',k11_relat_1('#skF_10','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_371,plain,(
    r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_369,c_50])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_447,plain,(
    ! [D_135,A_136,B_137,E_138] :
      ( r2_hidden(D_135,k9_relat_1(A_136,B_137))
      | ~ r2_hidden(E_138,B_137)
      | ~ r2_hidden(k4_tarski(E_138,D_135),A_136)
      | ~ v1_relat_1(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_468,plain,(
    ! [D_135,A_136,C_5] :
      ( r2_hidden(D_135,k9_relat_1(A_136,k1_tarski(C_5)))
      | ~ r2_hidden(k4_tarski(C_5,D_135),A_136)
      | ~ v1_relat_1(A_136) ) ),
    inference(resolution,[status(thm)],[c_4,c_447])).

tff(c_469,plain,(
    ! [D_139,A_140,C_141] :
      ( r2_hidden(D_139,k9_relat_1(A_140,k1_tarski(C_141)))
      | ~ r2_hidden(k4_tarski(C_141,D_139),A_140)
      | ~ v1_relat_1(A_140) ) ),
    inference(resolution,[status(thm)],[c_4,c_447])).

tff(c_387,plain,(
    ! [A_121,B_122,C_123] :
      ( r2_hidden('#skF_7'(A_121,B_122,C_123),B_122)
      | ~ r2_hidden(A_121,k9_relat_1(C_123,B_122))
      | ~ v1_relat_1(C_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_392,plain,(
    ! [A_121,A_1,C_123] :
      ( '#skF_7'(A_121,k1_tarski(A_1),C_123) = A_1
      | ~ r2_hidden(A_121,k9_relat_1(C_123,k1_tarski(A_1)))
      | ~ v1_relat_1(C_123) ) ),
    inference(resolution,[status(thm)],[c_387,c_2])).

tff(c_485,plain,(
    ! [D_142,C_143,A_144] :
      ( '#skF_7'(D_142,k1_tarski(C_143),A_144) = C_143
      | ~ r2_hidden(k4_tarski(C_143,D_142),A_144)
      | ~ v1_relat_1(A_144) ) ),
    inference(resolution,[status(thm)],[c_469,c_392])).

tff(c_495,plain,
    ( '#skF_7'('#skF_9',k1_tarski('#skF_8'),'#skF_10') = '#skF_8'
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_371,c_485])).

tff(c_504,plain,(
    '#skF_7'('#skF_9',k1_tarski('#skF_8'),'#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_495])).

tff(c_40,plain,(
    ! [A_51,B_52,C_53] :
      ( r2_hidden('#skF_7'(A_51,B_52,C_53),k1_relat_1(C_53))
      | ~ r2_hidden(A_51,k9_relat_1(C_53,B_52))
      | ~ v1_relat_1(C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_512,plain,
    ( r2_hidden('#skF_8',k1_relat_1('#skF_10'))
    | ~ r2_hidden('#skF_9',k9_relat_1('#skF_10',k1_tarski('#skF_8')))
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_504,c_40])).

tff(c_521,plain,
    ( r2_hidden('#skF_8',k1_relat_1('#skF_10'))
    | ~ r2_hidden('#skF_9',k9_relat_1('#skF_10',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_512])).

tff(c_525,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_10',k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_521])).

tff(c_545,plain,
    ( ~ r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_468,c_525])).

tff(c_552,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_371,c_545])).

tff(c_554,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_10',k1_tarski('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_521])).

tff(c_565,plain,
    ( r2_hidden('#skF_9',k11_relat_1('#skF_10','#skF_8'))
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_554])).

tff(c_571,plain,(
    r2_hidden('#skF_9',k11_relat_1('#skF_10','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_565])).

tff(c_573,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_369,c_571])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:24:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.35  
% 2.54/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.35  %$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > #skF_4 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_1
% 2.54/1.35  
% 2.54/1.35  %Foreground sorts:
% 2.54/1.35  
% 2.54/1.35  
% 2.54/1.35  %Background operators:
% 2.54/1.35  
% 2.54/1.35  
% 2.54/1.35  %Foreground operators:
% 2.54/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.54/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.54/1.35  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.54/1.35  tff('#skF_10', type, '#skF_10': $i).
% 2.54/1.35  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.54/1.35  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.54/1.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.54/1.35  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 2.54/1.35  tff('#skF_9', type, '#skF_9': $i).
% 2.54/1.35  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 2.54/1.35  tff('#skF_8', type, '#skF_8': $i).
% 2.54/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.54/1.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.54/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.54/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.54/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.54/1.35  
% 2.54/1.36  tff(f_68, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 2.54/1.36  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 2.54/1.36  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 2.54/1.36  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.54/1.36  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_relat_1)).
% 2.54/1.36  tff(c_42, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.54/1.36  tff(c_44, plain, (~r2_hidden('#skF_9', k11_relat_1('#skF_10', '#skF_8')) | ~r2_hidden(k4_tarski('#skF_8', '#skF_9'), '#skF_10')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.54/1.36  tff(c_67, plain, (~r2_hidden(k4_tarski('#skF_8', '#skF_9'), '#skF_10')), inference(splitLeft, [status(thm)], [c_44])).
% 2.54/1.36  tff(c_50, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_9'), '#skF_10') | r2_hidden('#skF_9', k11_relat_1('#skF_10', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.54/1.36  tff(c_68, plain, (r2_hidden('#skF_9', k11_relat_1('#skF_10', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_67, c_50])).
% 2.54/1.36  tff(c_32, plain, (![A_48, B_50]: (k9_relat_1(A_48, k1_tarski(B_50))=k11_relat_1(A_48, B_50) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.54/1.36  tff(c_77, plain, (![A_68, B_69, C_70]: (r2_hidden('#skF_7'(A_68, B_69, C_70), B_69) | ~r2_hidden(A_68, k9_relat_1(C_70, B_69)) | ~v1_relat_1(C_70))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.54/1.36  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.54/1.36  tff(c_90, plain, (![A_76, A_77, C_78]: ('#skF_7'(A_76, k1_tarski(A_77), C_78)=A_77 | ~r2_hidden(A_76, k9_relat_1(C_78, k1_tarski(A_77))) | ~v1_relat_1(C_78))), inference(resolution, [status(thm)], [c_77, c_2])).
% 2.54/1.36  tff(c_284, plain, (![A_107, B_108, A_109]: ('#skF_7'(A_107, k1_tarski(B_108), A_109)=B_108 | ~r2_hidden(A_107, k11_relat_1(A_109, B_108)) | ~v1_relat_1(A_109) | ~v1_relat_1(A_109))), inference(superposition, [status(thm), theory('equality')], [c_32, c_90])).
% 2.54/1.36  tff(c_306, plain, ('#skF_7'('#skF_9', k1_tarski('#skF_8'), '#skF_10')='#skF_8' | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_68, c_284])).
% 2.54/1.36  tff(c_314, plain, ('#skF_7'('#skF_9', k1_tarski('#skF_8'), '#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_306])).
% 2.54/1.36  tff(c_38, plain, (![A_51, B_52, C_53]: (r2_hidden(k4_tarski('#skF_7'(A_51, B_52, C_53), A_51), C_53) | ~r2_hidden(A_51, k9_relat_1(C_53, B_52)) | ~v1_relat_1(C_53))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.54/1.36  tff(c_340, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_9'), '#skF_10') | ~r2_hidden('#skF_9', k9_relat_1('#skF_10', k1_tarski('#skF_8'))) | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_314, c_38])).
% 2.54/1.36  tff(c_350, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_9'), '#skF_10') | ~r2_hidden('#skF_9', k9_relat_1('#skF_10', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_340])).
% 2.54/1.36  tff(c_351, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_10', k1_tarski('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_67, c_350])).
% 2.54/1.36  tff(c_362, plain, (~r2_hidden('#skF_9', k11_relat_1('#skF_10', '#skF_8')) | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_32, c_351])).
% 2.54/1.36  tff(c_368, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_68, c_362])).
% 2.54/1.36  tff(c_369, plain, (~r2_hidden('#skF_9', k11_relat_1('#skF_10', '#skF_8'))), inference(splitRight, [status(thm)], [c_44])).
% 2.54/1.36  tff(c_371, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_9'), '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_369, c_50])).
% 2.54/1.36  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.54/1.36  tff(c_447, plain, (![D_135, A_136, B_137, E_138]: (r2_hidden(D_135, k9_relat_1(A_136, B_137)) | ~r2_hidden(E_138, B_137) | ~r2_hidden(k4_tarski(E_138, D_135), A_136) | ~v1_relat_1(A_136))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.54/1.36  tff(c_468, plain, (![D_135, A_136, C_5]: (r2_hidden(D_135, k9_relat_1(A_136, k1_tarski(C_5))) | ~r2_hidden(k4_tarski(C_5, D_135), A_136) | ~v1_relat_1(A_136))), inference(resolution, [status(thm)], [c_4, c_447])).
% 2.54/1.36  tff(c_469, plain, (![D_139, A_140, C_141]: (r2_hidden(D_139, k9_relat_1(A_140, k1_tarski(C_141))) | ~r2_hidden(k4_tarski(C_141, D_139), A_140) | ~v1_relat_1(A_140))), inference(resolution, [status(thm)], [c_4, c_447])).
% 2.54/1.36  tff(c_387, plain, (![A_121, B_122, C_123]: (r2_hidden('#skF_7'(A_121, B_122, C_123), B_122) | ~r2_hidden(A_121, k9_relat_1(C_123, B_122)) | ~v1_relat_1(C_123))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.54/1.36  tff(c_392, plain, (![A_121, A_1, C_123]: ('#skF_7'(A_121, k1_tarski(A_1), C_123)=A_1 | ~r2_hidden(A_121, k9_relat_1(C_123, k1_tarski(A_1))) | ~v1_relat_1(C_123))), inference(resolution, [status(thm)], [c_387, c_2])).
% 2.54/1.36  tff(c_485, plain, (![D_142, C_143, A_144]: ('#skF_7'(D_142, k1_tarski(C_143), A_144)=C_143 | ~r2_hidden(k4_tarski(C_143, D_142), A_144) | ~v1_relat_1(A_144))), inference(resolution, [status(thm)], [c_469, c_392])).
% 2.54/1.36  tff(c_495, plain, ('#skF_7'('#skF_9', k1_tarski('#skF_8'), '#skF_10')='#skF_8' | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_371, c_485])).
% 2.54/1.36  tff(c_504, plain, ('#skF_7'('#skF_9', k1_tarski('#skF_8'), '#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_495])).
% 2.54/1.36  tff(c_40, plain, (![A_51, B_52, C_53]: (r2_hidden('#skF_7'(A_51, B_52, C_53), k1_relat_1(C_53)) | ~r2_hidden(A_51, k9_relat_1(C_53, B_52)) | ~v1_relat_1(C_53))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.54/1.36  tff(c_512, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_10')) | ~r2_hidden('#skF_9', k9_relat_1('#skF_10', k1_tarski('#skF_8'))) | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_504, c_40])).
% 2.54/1.36  tff(c_521, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_10')) | ~r2_hidden('#skF_9', k9_relat_1('#skF_10', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_512])).
% 2.54/1.36  tff(c_525, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_10', k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_521])).
% 2.54/1.36  tff(c_545, plain, (~r2_hidden(k4_tarski('#skF_8', '#skF_9'), '#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_468, c_525])).
% 2.54/1.36  tff(c_552, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_371, c_545])).
% 2.54/1.36  tff(c_554, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_10', k1_tarski('#skF_8')))), inference(splitRight, [status(thm)], [c_521])).
% 2.54/1.36  tff(c_565, plain, (r2_hidden('#skF_9', k11_relat_1('#skF_10', '#skF_8')) | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_32, c_554])).
% 2.54/1.36  tff(c_571, plain, (r2_hidden('#skF_9', k11_relat_1('#skF_10', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_565])).
% 2.54/1.36  tff(c_573, plain, $false, inference(negUnitSimplification, [status(thm)], [c_369, c_571])).
% 2.54/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.36  
% 2.54/1.36  Inference rules
% 2.54/1.36  ----------------------
% 2.54/1.36  #Ref     : 0
% 2.54/1.36  #Sup     : 113
% 2.54/1.36  #Fact    : 0
% 2.54/1.36  #Define  : 0
% 2.54/1.36  #Split   : 2
% 2.54/1.36  #Chain   : 0
% 2.54/1.36  #Close   : 0
% 2.54/1.36  
% 2.54/1.36  Ordering : KBO
% 2.54/1.36  
% 2.54/1.36  Simplification rules
% 2.54/1.36  ----------------------
% 2.54/1.36  #Subsume      : 3
% 2.54/1.36  #Demod        : 26
% 2.54/1.36  #Tautology    : 28
% 2.54/1.36  #SimpNegUnit  : 4
% 2.54/1.36  #BackRed      : 0
% 2.54/1.36  
% 2.54/1.36  #Partial instantiations: 0
% 2.54/1.36  #Strategies tried      : 1
% 2.54/1.36  
% 2.54/1.36  Timing (in seconds)
% 2.54/1.36  ----------------------
% 2.70/1.36  Preprocessing        : 0.28
% 2.70/1.36  Parsing              : 0.14
% 2.70/1.36  CNF conversion       : 0.03
% 2.70/1.36  Main loop            : 0.31
% 2.70/1.36  Inferencing          : 0.12
% 2.70/1.36  Reduction            : 0.08
% 2.70/1.36  Demodulation         : 0.05
% 2.70/1.36  BG Simplification    : 0.02
% 2.70/1.36  Subsumption          : 0.06
% 2.70/1.36  Abstraction          : 0.02
% 2.70/1.36  MUC search           : 0.00
% 2.70/1.36  Cooper               : 0.00
% 2.70/1.37  Total                : 0.62
% 2.70/1.37  Index Insertion      : 0.00
% 2.70/1.37  Index Deletion       : 0.00
% 2.70/1.37  Index Matching       : 0.00
% 2.70/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
