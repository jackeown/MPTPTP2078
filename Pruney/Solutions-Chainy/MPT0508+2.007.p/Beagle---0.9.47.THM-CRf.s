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
% DateTime   : Thu Dec  3 09:59:55 EST 2020

% Result     : Theorem 4.47s
% Output     : CNFRefutation 4.51s
% Verified   : 
% Statistics : Number of formulae       :   59 (  94 expanded)
%              Number of leaves         :   26 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :   98 ( 186 expanded)
%              Number of equality atoms :   12 (  22 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > k4_tarski > k2_xboole_0 > #nlpp > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k7_relat_1(C,A),k7_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k7_relat_1(B,A),k7_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_32,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_36,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_34,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_42,plain,(
    ! [A_43,B_44] :
      ( k2_xboole_0(A_43,B_44) = B_44
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_53,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_34,c_42])).

tff(c_72,plain,(
    ! [B_46,A_47] :
      ( r1_tarski(k7_relat_1(B_46,A_47),B_46)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( k2_xboole_0(A_11,B_12) = B_12
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_255,plain,(
    ! [B_74,A_75] :
      ( k2_xboole_0(k7_relat_1(B_74,A_75),B_74) = B_74
      | ~ v1_relat_1(B_74) ) ),
    inference(resolution,[status(thm)],[c_72,c_16])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_78,plain,(
    ! [A_51,C_52,B_53] :
      ( r1_tarski(A_51,C_52)
      | ~ r1_tarski(k2_xboole_0(A_51,B_53),C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_93,plain,(
    ! [A_54,B_55] : r1_tarski(A_54,k2_xboole_0(A_54,B_55)) ),
    inference(resolution,[status(thm)],[c_12,c_78])).

tff(c_14,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(A_8,C_10)
      | ~ r1_tarski(k2_xboole_0(A_8,B_9),C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_110,plain,(
    ! [A_8,B_9,B_55] : r1_tarski(A_8,k2_xboole_0(k2_xboole_0(A_8,B_9),B_55)) ),
    inference(resolution,[status(thm)],[c_93,c_14])).

tff(c_700,plain,(
    ! [B_104,A_105,B_106] :
      ( r1_tarski(k7_relat_1(B_104,A_105),k2_xboole_0(B_104,B_106))
      | ~ v1_relat_1(B_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_110])).

tff(c_726,plain,(
    ! [A_105] :
      ( r1_tarski(k7_relat_1('#skF_7',A_105),'#skF_8')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_700])).

tff(c_736,plain,(
    ! [A_105] : r1_tarski(k7_relat_1('#skF_7',A_105),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_726])).

tff(c_22,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_2'(A_13),A_13)
      | v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_246,plain,(
    ! [C_71,B_72,A_73] :
      ( r2_hidden(C_71,B_72)
      | ~ r2_hidden(C_71,A_73)
      | ~ r1_tarski(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_252,plain,(
    ! [A_13,B_72] :
      ( r2_hidden('#skF_2'(A_13),B_72)
      | ~ r1_tarski(A_13,B_72)
      | v1_relat_1(A_13) ) ),
    inference(resolution,[status(thm)],[c_22,c_246])).

tff(c_401,plain,(
    ! [A_81,B_82] :
      ( k4_tarski('#skF_3'(A_81,B_82),'#skF_4'(A_81,B_82)) = B_82
      | ~ r2_hidden(B_82,A_81)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_20,plain,(
    ! [C_26,D_27,A_13] :
      ( k4_tarski(C_26,D_27) != '#skF_2'(A_13)
      | v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_405,plain,(
    ! [B_82,A_13,A_81] :
      ( B_82 != '#skF_2'(A_13)
      | v1_relat_1(A_13)
      | ~ r2_hidden(B_82,A_81)
      | ~ v1_relat_1(A_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_20])).

tff(c_847,plain,(
    ! [A_121,A_122] :
      ( v1_relat_1(A_121)
      | ~ r2_hidden('#skF_2'(A_121),A_122)
      | ~ v1_relat_1(A_122) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_405])).

tff(c_856,plain,(
    ! [B_123,A_124] :
      ( ~ v1_relat_1(B_123)
      | ~ r1_tarski(A_124,B_123)
      | v1_relat_1(A_124) ) ),
    inference(resolution,[status(thm)],[c_252,c_847])).

tff(c_868,plain,(
    ! [A_105] :
      ( ~ v1_relat_1('#skF_8')
      | v1_relat_1(k7_relat_1('#skF_7',A_105)) ) ),
    inference(resolution,[status(thm)],[c_736,c_856])).

tff(c_916,plain,(
    ! [A_105] : v1_relat_1(k7_relat_1('#skF_7',A_105)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_868])).

tff(c_24,plain,(
    ! [C_33,A_31,B_32] :
      ( k7_relat_1(k7_relat_1(C_33,A_31),B_32) = k7_relat_1(C_33,A_31)
      | ~ r1_tarski(A_31,B_32)
      | ~ v1_relat_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_777,plain,(
    ! [B_109,A_110,C_111] :
      ( r1_tarski(k7_relat_1(B_109,A_110),k7_relat_1(C_111,A_110))
      | ~ r1_tarski(B_109,C_111)
      | ~ v1_relat_1(C_111)
      | ~ v1_relat_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2888,plain,(
    ! [C_245,A_246,C_247,B_248] :
      ( r1_tarski(k7_relat_1(C_245,A_246),k7_relat_1(C_247,B_248))
      | ~ r1_tarski(k7_relat_1(C_245,A_246),C_247)
      | ~ v1_relat_1(C_247)
      | ~ v1_relat_1(k7_relat_1(C_245,A_246))
      | ~ r1_tarski(A_246,B_248)
      | ~ v1_relat_1(C_245) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_777])).

tff(c_30,plain,(
    ~ r1_tarski(k7_relat_1('#skF_7','#skF_5'),k7_relat_1('#skF_8','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2906,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_7','#skF_5'),'#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ v1_relat_1(k7_relat_1('#skF_7','#skF_5'))
    | ~ r1_tarski('#skF_5','#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_2888,c_30])).

tff(c_2928,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_916,c_36,c_736,c_2906])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:32:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.47/1.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.47/1.78  
% 4.47/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.51/1.79  %$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > k4_tarski > k2_xboole_0 > #nlpp > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_1 > #skF_4
% 4.51/1.79  
% 4.51/1.79  %Foreground sorts:
% 4.51/1.79  
% 4.51/1.79  
% 4.51/1.79  %Background operators:
% 4.51/1.79  
% 4.51/1.79  
% 4.51/1.79  %Foreground operators:
% 4.51/1.79  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.51/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.51/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.51/1.79  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.51/1.79  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.51/1.79  tff('#skF_7', type, '#skF_7': $i).
% 4.51/1.79  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.51/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.51/1.79  tff('#skF_5', type, '#skF_5': $i).
% 4.51/1.79  tff('#skF_6', type, '#skF_6': $i).
% 4.51/1.79  tff('#skF_8', type, '#skF_8': $i).
% 4.51/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.51/1.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.51/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.51/1.79  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.51/1.79  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.51/1.79  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.51/1.79  
% 4.51/1.81  tff(f_87, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k7_relat_1(C, A), k7_relat_1(D, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_relat_1)).
% 4.51/1.81  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.51/1.81  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 4.51/1.81  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.51/1.81  tff(f_42, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 4.51/1.81  tff(f_56, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 4.51/1.81  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.51/1.81  tff(f_62, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_relat_1)).
% 4.51/1.81  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k7_relat_1(B, A), k7_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_relat_1)).
% 4.51/1.81  tff(c_38, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.51/1.81  tff(c_32, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.51/1.81  tff(c_36, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.51/1.81  tff(c_34, plain, (r1_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.51/1.81  tff(c_42, plain, (![A_43, B_44]: (k2_xboole_0(A_43, B_44)=B_44 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.51/1.81  tff(c_53, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_34, c_42])).
% 4.51/1.81  tff(c_72, plain, (![B_46, A_47]: (r1_tarski(k7_relat_1(B_46, A_47), B_46) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.51/1.81  tff(c_16, plain, (![A_11, B_12]: (k2_xboole_0(A_11, B_12)=B_12 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.51/1.81  tff(c_255, plain, (![B_74, A_75]: (k2_xboole_0(k7_relat_1(B_74, A_75), B_74)=B_74 | ~v1_relat_1(B_74))), inference(resolution, [status(thm)], [c_72, c_16])).
% 4.51/1.81  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.51/1.81  tff(c_78, plain, (![A_51, C_52, B_53]: (r1_tarski(A_51, C_52) | ~r1_tarski(k2_xboole_0(A_51, B_53), C_52))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.51/1.81  tff(c_93, plain, (![A_54, B_55]: (r1_tarski(A_54, k2_xboole_0(A_54, B_55)))), inference(resolution, [status(thm)], [c_12, c_78])).
% 4.51/1.81  tff(c_14, plain, (![A_8, C_10, B_9]: (r1_tarski(A_8, C_10) | ~r1_tarski(k2_xboole_0(A_8, B_9), C_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.51/1.81  tff(c_110, plain, (![A_8, B_9, B_55]: (r1_tarski(A_8, k2_xboole_0(k2_xboole_0(A_8, B_9), B_55)))), inference(resolution, [status(thm)], [c_93, c_14])).
% 4.51/1.81  tff(c_700, plain, (![B_104, A_105, B_106]: (r1_tarski(k7_relat_1(B_104, A_105), k2_xboole_0(B_104, B_106)) | ~v1_relat_1(B_104))), inference(superposition, [status(thm), theory('equality')], [c_255, c_110])).
% 4.51/1.81  tff(c_726, plain, (![A_105]: (r1_tarski(k7_relat_1('#skF_7', A_105), '#skF_8') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_53, c_700])).
% 4.51/1.81  tff(c_736, plain, (![A_105]: (r1_tarski(k7_relat_1('#skF_7', A_105), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_726])).
% 4.51/1.81  tff(c_22, plain, (![A_13]: (r2_hidden('#skF_2'(A_13), A_13) | v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.51/1.81  tff(c_246, plain, (![C_71, B_72, A_73]: (r2_hidden(C_71, B_72) | ~r2_hidden(C_71, A_73) | ~r1_tarski(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.51/1.81  tff(c_252, plain, (![A_13, B_72]: (r2_hidden('#skF_2'(A_13), B_72) | ~r1_tarski(A_13, B_72) | v1_relat_1(A_13))), inference(resolution, [status(thm)], [c_22, c_246])).
% 4.51/1.81  tff(c_401, plain, (![A_81, B_82]: (k4_tarski('#skF_3'(A_81, B_82), '#skF_4'(A_81, B_82))=B_82 | ~r2_hidden(B_82, A_81) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.51/1.81  tff(c_20, plain, (![C_26, D_27, A_13]: (k4_tarski(C_26, D_27)!='#skF_2'(A_13) | v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.51/1.81  tff(c_405, plain, (![B_82, A_13, A_81]: (B_82!='#skF_2'(A_13) | v1_relat_1(A_13) | ~r2_hidden(B_82, A_81) | ~v1_relat_1(A_81))), inference(superposition, [status(thm), theory('equality')], [c_401, c_20])).
% 4.51/1.81  tff(c_847, plain, (![A_121, A_122]: (v1_relat_1(A_121) | ~r2_hidden('#skF_2'(A_121), A_122) | ~v1_relat_1(A_122))), inference(reflexivity, [status(thm), theory('equality')], [c_405])).
% 4.51/1.81  tff(c_856, plain, (![B_123, A_124]: (~v1_relat_1(B_123) | ~r1_tarski(A_124, B_123) | v1_relat_1(A_124))), inference(resolution, [status(thm)], [c_252, c_847])).
% 4.51/1.81  tff(c_868, plain, (![A_105]: (~v1_relat_1('#skF_8') | v1_relat_1(k7_relat_1('#skF_7', A_105)))), inference(resolution, [status(thm)], [c_736, c_856])).
% 4.51/1.81  tff(c_916, plain, (![A_105]: (v1_relat_1(k7_relat_1('#skF_7', A_105)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_868])).
% 4.51/1.81  tff(c_24, plain, (![C_33, A_31, B_32]: (k7_relat_1(k7_relat_1(C_33, A_31), B_32)=k7_relat_1(C_33, A_31) | ~r1_tarski(A_31, B_32) | ~v1_relat_1(C_33))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.51/1.81  tff(c_777, plain, (![B_109, A_110, C_111]: (r1_tarski(k7_relat_1(B_109, A_110), k7_relat_1(C_111, A_110)) | ~r1_tarski(B_109, C_111) | ~v1_relat_1(C_111) | ~v1_relat_1(B_109))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.51/1.81  tff(c_2888, plain, (![C_245, A_246, C_247, B_248]: (r1_tarski(k7_relat_1(C_245, A_246), k7_relat_1(C_247, B_248)) | ~r1_tarski(k7_relat_1(C_245, A_246), C_247) | ~v1_relat_1(C_247) | ~v1_relat_1(k7_relat_1(C_245, A_246)) | ~r1_tarski(A_246, B_248) | ~v1_relat_1(C_245))), inference(superposition, [status(thm), theory('equality')], [c_24, c_777])).
% 4.51/1.81  tff(c_30, plain, (~r1_tarski(k7_relat_1('#skF_7', '#skF_5'), k7_relat_1('#skF_8', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.51/1.81  tff(c_2906, plain, (~r1_tarski(k7_relat_1('#skF_7', '#skF_5'), '#skF_8') | ~v1_relat_1('#skF_8') | ~v1_relat_1(k7_relat_1('#skF_7', '#skF_5')) | ~r1_tarski('#skF_5', '#skF_6') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_2888, c_30])).
% 4.51/1.81  tff(c_2928, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_916, c_36, c_736, c_2906])).
% 4.51/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.51/1.81  
% 4.51/1.81  Inference rules
% 4.51/1.81  ----------------------
% 4.51/1.81  #Ref     : 1
% 4.51/1.81  #Sup     : 662
% 4.51/1.81  #Fact    : 0
% 4.51/1.81  #Define  : 0
% 4.51/1.81  #Split   : 4
% 4.51/1.81  #Chain   : 0
% 4.51/1.81  #Close   : 0
% 4.51/1.81  
% 4.51/1.81  Ordering : KBO
% 4.51/1.81  
% 4.51/1.81  Simplification rules
% 4.51/1.81  ----------------------
% 4.51/1.81  #Subsume      : 129
% 4.51/1.81  #Demod        : 340
% 4.51/1.81  #Tautology    : 287
% 4.51/1.81  #SimpNegUnit  : 15
% 4.51/1.81  #BackRed      : 0
% 4.51/1.81  
% 4.51/1.81  #Partial instantiations: 0
% 4.51/1.81  #Strategies tried      : 1
% 4.51/1.81  
% 4.51/1.81  Timing (in seconds)
% 4.51/1.81  ----------------------
% 4.51/1.81  Preprocessing        : 0.28
% 4.51/1.81  Parsing              : 0.15
% 4.51/1.81  CNF conversion       : 0.02
% 4.51/1.81  Main loop            : 0.74
% 4.51/1.81  Inferencing          : 0.26
% 4.51/1.81  Reduction            : 0.26
% 4.51/1.81  Demodulation         : 0.19
% 4.51/1.81  BG Simplification    : 0.03
% 4.51/1.81  Subsumption          : 0.15
% 4.51/1.81  Abstraction          : 0.04
% 4.51/1.81  MUC search           : 0.00
% 4.51/1.81  Cooper               : 0.00
% 4.51/1.81  Total                : 1.07
% 4.51/1.81  Index Insertion      : 0.00
% 4.51/1.81  Index Deletion       : 0.00
% 4.51/1.81  Index Matching       : 0.00
% 4.51/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
