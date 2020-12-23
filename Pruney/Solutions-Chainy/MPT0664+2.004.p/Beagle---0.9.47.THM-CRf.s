%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:13 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 185 expanded)
%              Number of leaves         :   24 (  78 expanded)
%              Depth                    :   13
%              Number of atoms          :  120 ( 535 expanded)
%              Number of equality atoms :   26 ( 136 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k3_xboole_0 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,B)
         => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_funct_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(c_40,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_44,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_30,plain,(
    ! [A_11,B_14] :
      ( k1_funct_1(A_11,B_14) = k1_xboole_0
      | r2_hidden(B_14,k1_relat_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_22,plain,(
    ! [B_10,A_9] :
      ( k3_xboole_0(k1_relat_1(B_10),A_9) = k1_relat_1(k7_relat_1(B_10,A_9))
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_64,plain,(
    ! [D_33,A_34,B_35] :
      ( r2_hidden(D_33,k3_xboole_0(A_34,B_35))
      | ~ r2_hidden(D_33,B_35)
      | ~ r2_hidden(D_33,A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_73,plain,(
    ! [D_33,B_10,A_9] :
      ( r2_hidden(D_33,k1_relat_1(k7_relat_1(B_10,A_9)))
      | ~ r2_hidden(D_33,A_9)
      | ~ r2_hidden(D_33,k1_relat_1(B_10))
      | ~ v1_relat_1(B_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_64])).

tff(c_290,plain,(
    ! [C_65,B_66,A_67] :
      ( k1_funct_1(k7_relat_1(C_65,B_66),A_67) = k1_funct_1(C_65,A_67)
      | ~ r2_hidden(A_67,k1_relat_1(k7_relat_1(C_65,B_66)))
      | ~ v1_funct_1(C_65)
      | ~ v1_relat_1(C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_591,plain,(
    ! [B_90,A_91,D_92] :
      ( k1_funct_1(k7_relat_1(B_90,A_91),D_92) = k1_funct_1(B_90,D_92)
      | ~ v1_funct_1(B_90)
      | ~ r2_hidden(D_92,A_91)
      | ~ r2_hidden(D_92,k1_relat_1(B_90))
      | ~ v1_relat_1(B_90) ) ),
    inference(resolution,[status(thm)],[c_73,c_290])).

tff(c_966,plain,(
    ! [A_114,A_115,B_116] :
      ( k1_funct_1(k7_relat_1(A_114,A_115),B_116) = k1_funct_1(A_114,B_116)
      | ~ r2_hidden(B_116,A_115)
      | k1_funct_1(A_114,B_116) = k1_xboole_0
      | ~ v1_funct_1(A_114)
      | ~ v1_relat_1(A_114) ) ),
    inference(resolution,[status(thm)],[c_30,c_591])).

tff(c_38,plain,(
    k1_funct_1(k7_relat_1('#skF_5','#skF_4'),'#skF_3') != k1_funct_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_978,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | k1_funct_1('#skF_5','#skF_3') = k1_xboole_0
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_966,c_38])).

tff(c_988,plain,(
    k1_funct_1('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_978])).

tff(c_32,plain,(
    ! [A_16,B_17] :
      ( v1_funct_1(k7_relat_1(A_16,B_17))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k7_relat_1(A_7,B_8))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_49,plain,(
    ! [B_31,A_32] :
      ( k3_xboole_0(k1_relat_1(B_31),A_32) = k1_relat_1(k7_relat_1(B_31,A_32))
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_83,plain,(
    ! [D_41,B_42,A_43] :
      ( r2_hidden(D_41,k1_relat_1(B_42))
      | ~ r2_hidden(D_41,k1_relat_1(k7_relat_1(B_42,A_43)))
      | ~ v1_relat_1(B_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_6])).

tff(c_1052,plain,(
    ! [B_119,B_120,A_121] :
      ( r2_hidden(B_119,k1_relat_1(B_120))
      | ~ v1_relat_1(B_120)
      | k1_funct_1(k7_relat_1(B_120,A_121),B_119) = k1_xboole_0
      | ~ v1_funct_1(k7_relat_1(B_120,A_121))
      | ~ v1_relat_1(k7_relat_1(B_120,A_121)) ) ),
    inference(resolution,[status(thm)],[c_30,c_83])).

tff(c_1056,plain,(
    ! [B_122,A_123,B_124] :
      ( r2_hidden(B_122,k1_relat_1(A_123))
      | k1_funct_1(k7_relat_1(A_123,B_124),B_122) = k1_xboole_0
      | ~ v1_funct_1(k7_relat_1(A_123,B_124))
      | ~ v1_relat_1(A_123) ) ),
    inference(resolution,[status(thm)],[c_20,c_1052])).

tff(c_1060,plain,(
    ! [B_125,A_126,B_127] :
      ( r2_hidden(B_125,k1_relat_1(A_126))
      | k1_funct_1(k7_relat_1(A_126,B_127),B_125) = k1_xboole_0
      | ~ v1_funct_1(A_126)
      | ~ v1_relat_1(A_126) ) ),
    inference(resolution,[status(thm)],[c_32,c_1056])).

tff(c_26,plain,(
    ! [B_14,A_11] :
      ( r2_hidden(k4_tarski(B_14,k1_funct_1(A_11,B_14)),A_11)
      | ~ r2_hidden(B_14,k1_relat_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_994,plain,
    ( r2_hidden(k4_tarski('#skF_3',k1_xboole_0),'#skF_5')
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_988,c_26])).

tff(c_998,plain,
    ( r2_hidden(k4_tarski('#skF_3',k1_xboole_0),'#skF_5')
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_994])).

tff(c_1011,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_998])).

tff(c_1063,plain,(
    ! [B_127] :
      ( k1_funct_1(k7_relat_1('#skF_5',B_127),'#skF_3') = k1_xboole_0
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1060,c_1011])).

tff(c_1132,plain,(
    ! [B_127] : k1_funct_1(k7_relat_1('#skF_5',B_127),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1063])).

tff(c_990,plain,(
    k1_funct_1(k7_relat_1('#skF_5','#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_988,c_38])).

tff(c_1238,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1132,c_990])).

tff(c_1240,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_998])).

tff(c_332,plain,(
    ! [B_10,A_9,D_33] :
      ( k1_funct_1(k7_relat_1(B_10,A_9),D_33) = k1_funct_1(B_10,D_33)
      | ~ v1_funct_1(B_10)
      | ~ r2_hidden(D_33,A_9)
      | ~ r2_hidden(D_33,k1_relat_1(B_10))
      | ~ v1_relat_1(B_10) ) ),
    inference(resolution,[status(thm)],[c_73,c_290])).

tff(c_1242,plain,(
    ! [A_9] :
      ( k1_funct_1(k7_relat_1('#skF_5',A_9),'#skF_3') = k1_funct_1('#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ r2_hidden('#skF_3',A_9)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1240,c_332])).

tff(c_1252,plain,(
    ! [A_132] :
      ( k1_funct_1(k7_relat_1('#skF_5',A_132),'#skF_3') = k1_xboole_0
      | ~ r2_hidden('#skF_3',A_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_988,c_1242])).

tff(c_1258,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1252,c_990])).

tff(c_1283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1258])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:13:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.57  
% 3.70/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.57  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k3_xboole_0 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 3.70/1.57  
% 3.70/1.57  %Foreground sorts:
% 3.70/1.57  
% 3.70/1.57  
% 3.70/1.57  %Background operators:
% 3.70/1.57  
% 3.70/1.57  
% 3.70/1.57  %Foreground operators:
% 3.70/1.57  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.70/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.70/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.70/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.70/1.57  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.70/1.57  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.70/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.70/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.70/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.70/1.57  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.70/1.57  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.70/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.70/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.70/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.70/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.70/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.70/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.70/1.57  
% 3.70/1.59  tff(f_85, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, B) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_funct_1)).
% 3.70/1.59  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 3.70/1.59  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 3.70/1.59  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.70/1.59  tff(f_76, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_funct_1)).
% 3.70/1.59  tff(f_68, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 3.70/1.59  tff(f_38, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.70/1.59  tff(c_40, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.70/1.59  tff(c_44, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.70/1.59  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.70/1.59  tff(c_30, plain, (![A_11, B_14]: (k1_funct_1(A_11, B_14)=k1_xboole_0 | r2_hidden(B_14, k1_relat_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.70/1.59  tff(c_22, plain, (![B_10, A_9]: (k3_xboole_0(k1_relat_1(B_10), A_9)=k1_relat_1(k7_relat_1(B_10, A_9)) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.70/1.59  tff(c_64, plain, (![D_33, A_34, B_35]: (r2_hidden(D_33, k3_xboole_0(A_34, B_35)) | ~r2_hidden(D_33, B_35) | ~r2_hidden(D_33, A_34))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.70/1.59  tff(c_73, plain, (![D_33, B_10, A_9]: (r2_hidden(D_33, k1_relat_1(k7_relat_1(B_10, A_9))) | ~r2_hidden(D_33, A_9) | ~r2_hidden(D_33, k1_relat_1(B_10)) | ~v1_relat_1(B_10))), inference(superposition, [status(thm), theory('equality')], [c_22, c_64])).
% 3.70/1.59  tff(c_290, plain, (![C_65, B_66, A_67]: (k1_funct_1(k7_relat_1(C_65, B_66), A_67)=k1_funct_1(C_65, A_67) | ~r2_hidden(A_67, k1_relat_1(k7_relat_1(C_65, B_66))) | ~v1_funct_1(C_65) | ~v1_relat_1(C_65))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.70/1.59  tff(c_591, plain, (![B_90, A_91, D_92]: (k1_funct_1(k7_relat_1(B_90, A_91), D_92)=k1_funct_1(B_90, D_92) | ~v1_funct_1(B_90) | ~r2_hidden(D_92, A_91) | ~r2_hidden(D_92, k1_relat_1(B_90)) | ~v1_relat_1(B_90))), inference(resolution, [status(thm)], [c_73, c_290])).
% 3.70/1.59  tff(c_966, plain, (![A_114, A_115, B_116]: (k1_funct_1(k7_relat_1(A_114, A_115), B_116)=k1_funct_1(A_114, B_116) | ~r2_hidden(B_116, A_115) | k1_funct_1(A_114, B_116)=k1_xboole_0 | ~v1_funct_1(A_114) | ~v1_relat_1(A_114))), inference(resolution, [status(thm)], [c_30, c_591])).
% 3.70/1.59  tff(c_38, plain, (k1_funct_1(k7_relat_1('#skF_5', '#skF_4'), '#skF_3')!=k1_funct_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.70/1.59  tff(c_978, plain, (~r2_hidden('#skF_3', '#skF_4') | k1_funct_1('#skF_5', '#skF_3')=k1_xboole_0 | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_966, c_38])).
% 3.70/1.59  tff(c_988, plain, (k1_funct_1('#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_978])).
% 3.70/1.59  tff(c_32, plain, (![A_16, B_17]: (v1_funct_1(k7_relat_1(A_16, B_17)) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.70/1.59  tff(c_20, plain, (![A_7, B_8]: (v1_relat_1(k7_relat_1(A_7, B_8)) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.70/1.59  tff(c_49, plain, (![B_31, A_32]: (k3_xboole_0(k1_relat_1(B_31), A_32)=k1_relat_1(k7_relat_1(B_31, A_32)) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.70/1.59  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.70/1.59  tff(c_83, plain, (![D_41, B_42, A_43]: (r2_hidden(D_41, k1_relat_1(B_42)) | ~r2_hidden(D_41, k1_relat_1(k7_relat_1(B_42, A_43))) | ~v1_relat_1(B_42))), inference(superposition, [status(thm), theory('equality')], [c_49, c_6])).
% 3.70/1.59  tff(c_1052, plain, (![B_119, B_120, A_121]: (r2_hidden(B_119, k1_relat_1(B_120)) | ~v1_relat_1(B_120) | k1_funct_1(k7_relat_1(B_120, A_121), B_119)=k1_xboole_0 | ~v1_funct_1(k7_relat_1(B_120, A_121)) | ~v1_relat_1(k7_relat_1(B_120, A_121)))), inference(resolution, [status(thm)], [c_30, c_83])).
% 3.70/1.59  tff(c_1056, plain, (![B_122, A_123, B_124]: (r2_hidden(B_122, k1_relat_1(A_123)) | k1_funct_1(k7_relat_1(A_123, B_124), B_122)=k1_xboole_0 | ~v1_funct_1(k7_relat_1(A_123, B_124)) | ~v1_relat_1(A_123))), inference(resolution, [status(thm)], [c_20, c_1052])).
% 3.70/1.59  tff(c_1060, plain, (![B_125, A_126, B_127]: (r2_hidden(B_125, k1_relat_1(A_126)) | k1_funct_1(k7_relat_1(A_126, B_127), B_125)=k1_xboole_0 | ~v1_funct_1(A_126) | ~v1_relat_1(A_126))), inference(resolution, [status(thm)], [c_32, c_1056])).
% 3.70/1.59  tff(c_26, plain, (![B_14, A_11]: (r2_hidden(k4_tarski(B_14, k1_funct_1(A_11, B_14)), A_11) | ~r2_hidden(B_14, k1_relat_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.70/1.59  tff(c_994, plain, (r2_hidden(k4_tarski('#skF_3', k1_xboole_0), '#skF_5') | ~r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_988, c_26])).
% 3.70/1.59  tff(c_998, plain, (r2_hidden(k4_tarski('#skF_3', k1_xboole_0), '#skF_5') | ~r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_994])).
% 3.70/1.59  tff(c_1011, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_998])).
% 3.70/1.59  tff(c_1063, plain, (![B_127]: (k1_funct_1(k7_relat_1('#skF_5', B_127), '#skF_3')=k1_xboole_0 | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_1060, c_1011])).
% 3.70/1.59  tff(c_1132, plain, (![B_127]: (k1_funct_1(k7_relat_1('#skF_5', B_127), '#skF_3')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_1063])).
% 3.70/1.59  tff(c_990, plain, (k1_funct_1(k7_relat_1('#skF_5', '#skF_4'), '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_988, c_38])).
% 3.70/1.59  tff(c_1238, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1132, c_990])).
% 3.70/1.59  tff(c_1240, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_998])).
% 3.70/1.59  tff(c_332, plain, (![B_10, A_9, D_33]: (k1_funct_1(k7_relat_1(B_10, A_9), D_33)=k1_funct_1(B_10, D_33) | ~v1_funct_1(B_10) | ~r2_hidden(D_33, A_9) | ~r2_hidden(D_33, k1_relat_1(B_10)) | ~v1_relat_1(B_10))), inference(resolution, [status(thm)], [c_73, c_290])).
% 3.70/1.59  tff(c_1242, plain, (![A_9]: (k1_funct_1(k7_relat_1('#skF_5', A_9), '#skF_3')=k1_funct_1('#skF_5', '#skF_3') | ~v1_funct_1('#skF_5') | ~r2_hidden('#skF_3', A_9) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_1240, c_332])).
% 3.70/1.59  tff(c_1252, plain, (![A_132]: (k1_funct_1(k7_relat_1('#skF_5', A_132), '#skF_3')=k1_xboole_0 | ~r2_hidden('#skF_3', A_132))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_988, c_1242])).
% 3.70/1.59  tff(c_1258, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1252, c_990])).
% 3.70/1.59  tff(c_1283, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_1258])).
% 3.70/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.59  
% 3.70/1.59  Inference rules
% 3.70/1.59  ----------------------
% 3.70/1.59  #Ref     : 0
% 3.70/1.59  #Sup     : 280
% 3.70/1.59  #Fact    : 0
% 3.70/1.59  #Define  : 0
% 3.70/1.59  #Split   : 1
% 3.70/1.59  #Chain   : 0
% 3.70/1.59  #Close   : 0
% 3.70/1.59  
% 3.70/1.59  Ordering : KBO
% 3.70/1.59  
% 3.70/1.59  Simplification rules
% 3.70/1.59  ----------------------
% 3.70/1.59  #Subsume      : 39
% 3.70/1.59  #Demod        : 66
% 3.70/1.59  #Tautology    : 44
% 3.70/1.59  #SimpNegUnit  : 0
% 3.70/1.59  #BackRed      : 2
% 3.70/1.59  
% 3.70/1.59  #Partial instantiations: 0
% 3.70/1.59  #Strategies tried      : 1
% 3.70/1.59  
% 3.70/1.59  Timing (in seconds)
% 3.70/1.59  ----------------------
% 3.70/1.59  Preprocessing        : 0.31
% 3.70/1.59  Parsing              : 0.16
% 3.70/1.59  CNF conversion       : 0.02
% 3.70/1.59  Main loop            : 0.48
% 3.70/1.59  Inferencing          : 0.18
% 3.70/1.59  Reduction            : 0.11
% 3.70/1.59  Demodulation         : 0.08
% 3.70/1.59  BG Simplification    : 0.03
% 3.70/1.59  Subsumption          : 0.12
% 3.70/1.59  Abstraction          : 0.03
% 3.70/1.59  MUC search           : 0.00
% 3.70/1.59  Cooper               : 0.00
% 3.70/1.59  Total                : 0.82
% 3.70/1.59  Index Insertion      : 0.00
% 3.70/1.59  Index Deletion       : 0.00
% 3.70/1.59  Index Matching       : 0.00
% 3.70/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
