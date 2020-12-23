%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:16 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   62 (  77 expanded)
%              Number of leaves         :   31 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 ( 111 expanded)
%              Number of equality atoms :   18 (  31 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_47,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(c_10,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_183,plain,(
    ! [A_70,B_71,C_72] :
      ( ~ r1_xboole_0(A_70,B_71)
      | ~ r2_hidden(C_72,k3_xboole_0(A_70,B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_186,plain,(
    ! [A_8,C_72] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_72,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_183])).

tff(c_188,plain,(
    ! [C_72] : ~ r2_hidden(C_72,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_186])).

tff(c_46,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_7'))
    | k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_81,plain,(
    k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_38,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_68,plain,(
    ! [A_45,B_46] :
      ( r1_xboole_0(k1_tarski(A_45),B_46)
      | r2_hidden(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_71,plain,(
    ! [B_46,A_45] :
      ( r1_xboole_0(B_46,k1_tarski(A_45))
      | r2_hidden(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_68,c_2])).

tff(c_100,plain,(
    ! [B_59,A_60] :
      ( k9_relat_1(B_59,A_60) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_59),A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_147,plain,(
    ! [B_68,A_69] :
      ( k9_relat_1(B_68,k1_tarski(A_69)) = k1_xboole_0
      | ~ v1_relat_1(B_68)
      | r2_hidden(A_69,k1_relat_1(B_68)) ) ),
    inference(resolution,[status(thm)],[c_71,c_100])).

tff(c_40,plain,
    ( k11_relat_1('#skF_7','#skF_6') = k1_xboole_0
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_82,plain,(
    ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_154,plain,
    ( k9_relat_1('#skF_7',k1_tarski('#skF_6')) = k1_xboole_0
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_147,c_82])).

tff(c_158,plain,(
    k9_relat_1('#skF_7',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_154])).

tff(c_16,plain,(
    ! [A_13,B_15] :
      ( k9_relat_1(A_13,k1_tarski(B_15)) = k11_relat_1(A_13,B_15)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_162,plain,
    ( k11_relat_1('#skF_7','#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_16])).

tff(c_169,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_162])).

tff(c_171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_169])).

tff(c_172,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_172])).

tff(c_175,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_176,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_288,plain,(
    ! [C_99,A_100] :
      ( r2_hidden(k4_tarski(C_99,'#skF_5'(A_100,k1_relat_1(A_100),C_99)),A_100)
      | ~ r2_hidden(C_99,k1_relat_1(A_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_36,plain,(
    ! [B_38,C_39,A_37] :
      ( r2_hidden(B_38,k11_relat_1(C_39,A_37))
      | ~ r2_hidden(k4_tarski(A_37,B_38),C_39)
      | ~ v1_relat_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1636,plain,(
    ! [A_163,C_164] :
      ( r2_hidden('#skF_5'(A_163,k1_relat_1(A_163),C_164),k11_relat_1(A_163,C_164))
      | ~ v1_relat_1(A_163)
      | ~ r2_hidden(C_164,k1_relat_1(A_163)) ) ),
    inference(resolution,[status(thm)],[c_288,c_36])).

tff(c_1660,plain,
    ( r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k1_xboole_0)
    | ~ v1_relat_1('#skF_7')
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_1636])).

tff(c_1665,plain,(
    r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_38,c_1660])).

tff(c_1667,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_1665])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:33:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.18/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.51  
% 3.18/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.51  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 3.18/1.51  
% 3.18/1.51  %Foreground sorts:
% 3.18/1.51  
% 3.18/1.51  
% 3.18/1.51  %Background operators:
% 3.18/1.51  
% 3.18/1.51  
% 3.18/1.51  %Foreground operators:
% 3.18/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.18/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.18/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.18/1.51  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.18/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.18/1.51  tff('#skF_7', type, '#skF_7': $i).
% 3.18/1.51  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.18/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.18/1.51  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.18/1.51  tff('#skF_6', type, '#skF_6': $i).
% 3.18/1.51  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.18/1.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.18/1.51  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.18/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.18/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.18/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.18/1.51  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.18/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.18/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.18/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.18/1.51  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.18/1.51  
% 3.18/1.53  tff(f_47, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.18/1.53  tff(f_45, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.18/1.53  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.18/1.53  tff(f_87, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 3.18/1.53  tff(f_54, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.18/1.53  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.18/1.53  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 3.18/1.53  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 3.18/1.53  tff(f_67, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.18/1.53  tff(f_79, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 3.18/1.53  tff(c_10, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.18/1.53  tff(c_8, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.18/1.53  tff(c_183, plain, (![A_70, B_71, C_72]: (~r1_xboole_0(A_70, B_71) | ~r2_hidden(C_72, k3_xboole_0(A_70, B_71)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.18/1.53  tff(c_186, plain, (![A_8, C_72]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_72, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_183])).
% 3.18/1.53  tff(c_188, plain, (![C_72]: (~r2_hidden(C_72, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_186])).
% 3.18/1.53  tff(c_46, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7')) | k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.18/1.53  tff(c_81, plain, (k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_46])).
% 3.18/1.53  tff(c_38, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.18/1.53  tff(c_68, plain, (![A_45, B_46]: (r1_xboole_0(k1_tarski(A_45), B_46) | r2_hidden(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.18/1.53  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.18/1.53  tff(c_71, plain, (![B_46, A_45]: (r1_xboole_0(B_46, k1_tarski(A_45)) | r2_hidden(A_45, B_46))), inference(resolution, [status(thm)], [c_68, c_2])).
% 3.18/1.53  tff(c_100, plain, (![B_59, A_60]: (k9_relat_1(B_59, A_60)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_59), A_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.18/1.53  tff(c_147, plain, (![B_68, A_69]: (k9_relat_1(B_68, k1_tarski(A_69))=k1_xboole_0 | ~v1_relat_1(B_68) | r2_hidden(A_69, k1_relat_1(B_68)))), inference(resolution, [status(thm)], [c_71, c_100])).
% 3.18/1.53  tff(c_40, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0 | ~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.18/1.53  tff(c_82, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_40])).
% 3.18/1.53  tff(c_154, plain, (k9_relat_1('#skF_7', k1_tarski('#skF_6'))=k1_xboole_0 | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_147, c_82])).
% 3.18/1.53  tff(c_158, plain, (k9_relat_1('#skF_7', k1_tarski('#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_154])).
% 3.18/1.53  tff(c_16, plain, (![A_13, B_15]: (k9_relat_1(A_13, k1_tarski(B_15))=k11_relat_1(A_13, B_15) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.18/1.53  tff(c_162, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_158, c_16])).
% 3.18/1.53  tff(c_169, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_162])).
% 3.18/1.53  tff(c_171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_169])).
% 3.18/1.53  tff(c_172, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 3.18/1.53  tff(c_174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_172])).
% 3.18/1.53  tff(c_175, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_46])).
% 3.18/1.53  tff(c_176, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_46])).
% 3.18/1.53  tff(c_288, plain, (![C_99, A_100]: (r2_hidden(k4_tarski(C_99, '#skF_5'(A_100, k1_relat_1(A_100), C_99)), A_100) | ~r2_hidden(C_99, k1_relat_1(A_100)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.18/1.53  tff(c_36, plain, (![B_38, C_39, A_37]: (r2_hidden(B_38, k11_relat_1(C_39, A_37)) | ~r2_hidden(k4_tarski(A_37, B_38), C_39) | ~v1_relat_1(C_39))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.18/1.53  tff(c_1636, plain, (![A_163, C_164]: (r2_hidden('#skF_5'(A_163, k1_relat_1(A_163), C_164), k11_relat_1(A_163, C_164)) | ~v1_relat_1(A_163) | ~r2_hidden(C_164, k1_relat_1(A_163)))), inference(resolution, [status(thm)], [c_288, c_36])).
% 3.18/1.53  tff(c_1660, plain, (r2_hidden('#skF_5'('#skF_7', k1_relat_1('#skF_7'), '#skF_6'), k1_xboole_0) | ~v1_relat_1('#skF_7') | ~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_176, c_1636])).
% 3.18/1.53  tff(c_1665, plain, (r2_hidden('#skF_5'('#skF_7', k1_relat_1('#skF_7'), '#skF_6'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_175, c_38, c_1660])).
% 3.18/1.53  tff(c_1667, plain, $false, inference(negUnitSimplification, [status(thm)], [c_188, c_1665])).
% 3.18/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.53  
% 3.18/1.53  Inference rules
% 3.18/1.53  ----------------------
% 3.18/1.53  #Ref     : 0
% 3.18/1.53  #Sup     : 351
% 3.18/1.53  #Fact    : 0
% 3.18/1.53  #Define  : 0
% 3.18/1.53  #Split   : 4
% 3.18/1.53  #Chain   : 0
% 3.18/1.53  #Close   : 0
% 3.18/1.53  
% 3.18/1.53  Ordering : KBO
% 3.18/1.53  
% 3.18/1.53  Simplification rules
% 3.18/1.53  ----------------------
% 3.18/1.53  #Subsume      : 88
% 3.18/1.53  #Demod        : 270
% 3.18/1.53  #Tautology    : 122
% 3.18/1.53  #SimpNegUnit  : 35
% 3.18/1.53  #BackRed      : 8
% 3.18/1.53  
% 3.18/1.53  #Partial instantiations: 0
% 3.18/1.53  #Strategies tried      : 1
% 3.18/1.53  
% 3.18/1.53  Timing (in seconds)
% 3.18/1.53  ----------------------
% 3.18/1.53  Preprocessing        : 0.31
% 3.18/1.53  Parsing              : 0.16
% 3.18/1.53  CNF conversion       : 0.02
% 3.18/1.53  Main loop            : 0.46
% 3.18/1.53  Inferencing          : 0.17
% 3.18/1.53  Reduction            : 0.14
% 3.18/1.53  Demodulation         : 0.09
% 3.18/1.53  BG Simplification    : 0.02
% 3.18/1.53  Subsumption          : 0.09
% 3.18/1.53  Abstraction          : 0.03
% 3.18/1.53  MUC search           : 0.00
% 3.18/1.53  Cooper               : 0.00
% 3.18/1.53  Total                : 0.79
% 3.18/1.53  Index Insertion      : 0.00
% 3.18/1.53  Index Deletion       : 0.00
% 3.18/1.53  Index Matching       : 0.00
% 3.18/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
