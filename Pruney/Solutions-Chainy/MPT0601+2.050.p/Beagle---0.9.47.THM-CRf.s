%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:20 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   68 (  81 expanded)
%              Number of leaves         :   38 (  46 expanded)
%              Depth                    :    6
%              Number of atoms          :   70 ( 102 expanded)
%              Number of equality atoms :   23 (  34 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_66,axiom,(
    ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_8,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_90,plain,(
    ! [A_74,B_75] : k4_xboole_0(k1_tarski(A_74),k2_tarski(A_74,B_75)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_97,plain,(
    ! [A_6] : k4_xboole_0(k1_tarski(A_6),k1_tarski(A_6)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_90])).

tff(c_28,plain,(
    ! [B_39] : k4_xboole_0(k1_tarski(B_39),k1_tarski(B_39)) != k1_tarski(B_39) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_359,plain,(
    ! [B_39] : k1_tarski(B_39) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_28])).

tff(c_72,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(k1_tarski(A_69),B_70)
      | ~ r2_hidden(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_77,plain,(
    ! [A_69] :
      ( k1_tarski(A_69) = k1_xboole_0
      | ~ r2_hidden(A_69,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_72,c_6])).

tff(c_360,plain,(
    ! [A_69] : ~ r2_hidden(A_69,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_359,c_77])).

tff(c_60,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_7'))
    | k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_107,plain,(
    k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_52,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_279,plain,(
    ! [A_104,B_105,C_106] :
      ( r2_hidden(k4_tarski(A_104,B_105),C_106)
      | ~ r2_hidden(B_105,k11_relat_1(C_106,A_104))
      | ~ v1_relat_1(C_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_38,plain,(
    ! [C_59,A_44,D_62] :
      ( r2_hidden(C_59,k1_relat_1(A_44))
      | ~ r2_hidden(k4_tarski(C_59,D_62),A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_290,plain,(
    ! [A_107,C_108,B_109] :
      ( r2_hidden(A_107,k1_relat_1(C_108))
      | ~ r2_hidden(B_109,k11_relat_1(C_108,A_107))
      | ~ v1_relat_1(C_108) ) ),
    inference(resolution,[status(thm)],[c_279,c_38])).

tff(c_299,plain,(
    ! [A_110,C_111] :
      ( r2_hidden(A_110,k1_relat_1(C_111))
      | ~ v1_relat_1(C_111)
      | k11_relat_1(C_111,A_110) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_290])).

tff(c_54,plain,
    ( k11_relat_1('#skF_7','#skF_6') = k1_xboole_0
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_139,plain,(
    ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_54])).

tff(c_306,plain,
    ( ~ v1_relat_1('#skF_7')
    | k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_299,c_139])).

tff(c_310,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_306])).

tff(c_312,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_310])).

tff(c_313,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_314,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_540,plain,(
    ! [C_155,A_156] :
      ( r2_hidden(k4_tarski(C_155,'#skF_5'(A_156,k1_relat_1(A_156),C_155)),A_156)
      | ~ r2_hidden(C_155,k1_relat_1(A_156)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_50,plain,(
    ! [B_64,C_65,A_63] :
      ( r2_hidden(B_64,k11_relat_1(C_65,A_63))
      | ~ r2_hidden(k4_tarski(A_63,B_64),C_65)
      | ~ v1_relat_1(C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_989,plain,(
    ! [A_190,C_191] :
      ( r2_hidden('#skF_5'(A_190,k1_relat_1(A_190),C_191),k11_relat_1(A_190,C_191))
      | ~ v1_relat_1(A_190)
      | ~ r2_hidden(C_191,k1_relat_1(A_190)) ) ),
    inference(resolution,[status(thm)],[c_540,c_50])).

tff(c_1009,plain,
    ( r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k1_xboole_0)
    | ~ v1_relat_1('#skF_7')
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_989])).

tff(c_1014,plain,(
    r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_52,c_1009])).

tff(c_1016,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_360,c_1014])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:16:11 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.45  
% 2.83/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.46  %$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4
% 2.83/1.46  
% 2.83/1.46  %Foreground sorts:
% 2.83/1.46  
% 2.83/1.46  
% 2.83/1.46  %Background operators:
% 2.83/1.46  
% 2.83/1.46  
% 2.83/1.46  %Foreground operators:
% 2.83/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.83/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.83/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.83/1.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.83/1.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.83/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.83/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.83/1.46  tff('#skF_7', type, '#skF_7': $i).
% 2.83/1.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.83/1.46  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.83/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.83/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.83/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.83/1.46  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.83/1.46  tff('#skF_6', type, '#skF_6': $i).
% 2.83/1.46  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.83/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.83/1.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.83/1.46  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.83/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.83/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.83/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.83/1.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.83/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.83/1.46  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.83/1.46  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.83/1.46  
% 3.16/1.47  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.16/1.47  tff(f_66, axiom, (![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 3.16/1.47  tff(f_64, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.16/1.47  tff(f_57, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.16/1.47  tff(f_39, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.16/1.47  tff(f_90, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 3.16/1.47  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.16/1.47  tff(f_82, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 3.16/1.47  tff(f_76, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.16/1.47  tff(c_8, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.16/1.47  tff(c_90, plain, (![A_74, B_75]: (k4_xboole_0(k1_tarski(A_74), k2_tarski(A_74, B_75))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.16/1.47  tff(c_97, plain, (![A_6]: (k4_xboole_0(k1_tarski(A_6), k1_tarski(A_6))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_90])).
% 3.16/1.47  tff(c_28, plain, (![B_39]: (k4_xboole_0(k1_tarski(B_39), k1_tarski(B_39))!=k1_tarski(B_39))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.16/1.47  tff(c_359, plain, (![B_39]: (k1_tarski(B_39)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_97, c_28])).
% 3.16/1.47  tff(c_72, plain, (![A_69, B_70]: (r1_tarski(k1_tarski(A_69), B_70) | ~r2_hidden(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.16/1.47  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.16/1.47  tff(c_77, plain, (![A_69]: (k1_tarski(A_69)=k1_xboole_0 | ~r2_hidden(A_69, k1_xboole_0))), inference(resolution, [status(thm)], [c_72, c_6])).
% 3.16/1.47  tff(c_360, plain, (![A_69]: (~r2_hidden(A_69, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_359, c_77])).
% 3.16/1.47  tff(c_60, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7')) | k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.16/1.47  tff(c_107, plain, (k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_60])).
% 3.16/1.47  tff(c_52, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.16/1.47  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.16/1.47  tff(c_279, plain, (![A_104, B_105, C_106]: (r2_hidden(k4_tarski(A_104, B_105), C_106) | ~r2_hidden(B_105, k11_relat_1(C_106, A_104)) | ~v1_relat_1(C_106))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.16/1.47  tff(c_38, plain, (![C_59, A_44, D_62]: (r2_hidden(C_59, k1_relat_1(A_44)) | ~r2_hidden(k4_tarski(C_59, D_62), A_44))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.16/1.47  tff(c_290, plain, (![A_107, C_108, B_109]: (r2_hidden(A_107, k1_relat_1(C_108)) | ~r2_hidden(B_109, k11_relat_1(C_108, A_107)) | ~v1_relat_1(C_108))), inference(resolution, [status(thm)], [c_279, c_38])).
% 3.16/1.47  tff(c_299, plain, (![A_110, C_111]: (r2_hidden(A_110, k1_relat_1(C_111)) | ~v1_relat_1(C_111) | k11_relat_1(C_111, A_110)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_290])).
% 3.16/1.47  tff(c_54, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0 | ~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.16/1.47  tff(c_139, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_107, c_54])).
% 3.16/1.47  tff(c_306, plain, (~v1_relat_1('#skF_7') | k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_299, c_139])).
% 3.16/1.47  tff(c_310, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_306])).
% 3.16/1.47  tff(c_312, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_310])).
% 3.16/1.47  tff(c_313, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_60])).
% 3.16/1.47  tff(c_314, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_60])).
% 3.16/1.47  tff(c_540, plain, (![C_155, A_156]: (r2_hidden(k4_tarski(C_155, '#skF_5'(A_156, k1_relat_1(A_156), C_155)), A_156) | ~r2_hidden(C_155, k1_relat_1(A_156)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.16/1.47  tff(c_50, plain, (![B_64, C_65, A_63]: (r2_hidden(B_64, k11_relat_1(C_65, A_63)) | ~r2_hidden(k4_tarski(A_63, B_64), C_65) | ~v1_relat_1(C_65))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.16/1.47  tff(c_989, plain, (![A_190, C_191]: (r2_hidden('#skF_5'(A_190, k1_relat_1(A_190), C_191), k11_relat_1(A_190, C_191)) | ~v1_relat_1(A_190) | ~r2_hidden(C_191, k1_relat_1(A_190)))), inference(resolution, [status(thm)], [c_540, c_50])).
% 3.16/1.47  tff(c_1009, plain, (r2_hidden('#skF_5'('#skF_7', k1_relat_1('#skF_7'), '#skF_6'), k1_xboole_0) | ~v1_relat_1('#skF_7') | ~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_314, c_989])).
% 3.16/1.47  tff(c_1014, plain, (r2_hidden('#skF_5'('#skF_7', k1_relat_1('#skF_7'), '#skF_6'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_313, c_52, c_1009])).
% 3.16/1.47  tff(c_1016, plain, $false, inference(negUnitSimplification, [status(thm)], [c_360, c_1014])).
% 3.16/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.47  
% 3.16/1.47  Inference rules
% 3.16/1.47  ----------------------
% 3.16/1.47  #Ref     : 0
% 3.16/1.47  #Sup     : 210
% 3.16/1.47  #Fact    : 0
% 3.16/1.47  #Define  : 0
% 3.16/1.47  #Split   : 3
% 3.16/1.47  #Chain   : 0
% 3.16/1.47  #Close   : 0
% 3.16/1.47  
% 3.16/1.47  Ordering : KBO
% 3.16/1.47  
% 3.16/1.47  Simplification rules
% 3.16/1.47  ----------------------
% 3.16/1.47  #Subsume      : 29
% 3.16/1.47  #Demod        : 80
% 3.16/1.47  #Tautology    : 104
% 3.16/1.47  #SimpNegUnit  : 32
% 3.16/1.47  #BackRed      : 3
% 3.16/1.47  
% 3.16/1.47  #Partial instantiations: 0
% 3.16/1.47  #Strategies tried      : 1
% 3.16/1.47  
% 3.16/1.47  Timing (in seconds)
% 3.16/1.47  ----------------------
% 3.21/1.47  Preprocessing        : 0.35
% 3.21/1.47  Parsing              : 0.19
% 3.21/1.47  CNF conversion       : 0.02
% 3.21/1.47  Main loop            : 0.37
% 3.21/1.47  Inferencing          : 0.14
% 3.21/1.47  Reduction            : 0.11
% 3.21/1.47  Demodulation         : 0.08
% 3.21/1.47  BG Simplification    : 0.02
% 3.21/1.47  Subsumption          : 0.07
% 3.21/1.47  Abstraction          : 0.02
% 3.21/1.47  MUC search           : 0.00
% 3.21/1.47  Cooper               : 0.00
% 3.21/1.47  Total                : 0.75
% 3.21/1.47  Index Insertion      : 0.00
% 3.21/1.47  Index Deletion       : 0.00
% 3.21/1.47  Index Matching       : 0.00
% 3.21/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
