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
% DateTime   : Thu Dec  3 10:04:13 EST 2020

% Result     : Theorem 4.32s
% Output     : CNFRefutation 4.32s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 164 expanded)
%              Number of leaves         :   24 (  71 expanded)
%              Depth                    :   12
%              Number of atoms          :  112 ( 481 expanded)
%              Number of equality atoms :   23 ( 121 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,B)
         => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).

tff(f_64,axiom,(
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

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_funct_1)).

tff(f_72,axiom,(
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

tff(f_46,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(c_44,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_48,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_34,plain,(
    ! [A_12,B_15] :
      ( k1_funct_1(A_12,B_15) = k1_xboole_0
      | r2_hidden(B_15,k1_relat_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k3_xboole_0(A_1,B_2))
      | ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_276,plain,(
    ! [C_64,B_65,A_66] :
      ( k1_funct_1(k7_relat_1(C_64,B_65),A_66) = k1_funct_1(C_64,A_66)
      | ~ r2_hidden(A_66,k3_xboole_0(k1_relat_1(C_64),B_65))
      | ~ v1_funct_1(C_64)
      | ~ v1_relat_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_712,plain,(
    ! [C_105,B_106,D_107] :
      ( k1_funct_1(k7_relat_1(C_105,B_106),D_107) = k1_funct_1(C_105,D_107)
      | ~ v1_funct_1(C_105)
      | ~ v1_relat_1(C_105)
      | ~ r2_hidden(D_107,B_106)
      | ~ r2_hidden(D_107,k1_relat_1(C_105)) ) ),
    inference(resolution,[status(thm)],[c_2,c_276])).

tff(c_771,plain,(
    ! [A_108,B_109,B_110] :
      ( k1_funct_1(k7_relat_1(A_108,B_109),B_110) = k1_funct_1(A_108,B_110)
      | ~ r2_hidden(B_110,B_109)
      | k1_funct_1(A_108,B_110) = k1_xboole_0
      | ~ v1_funct_1(A_108)
      | ~ v1_relat_1(A_108) ) ),
    inference(resolution,[status(thm)],[c_34,c_712])).

tff(c_42,plain,(
    k1_funct_1(k7_relat_1('#skF_5','#skF_4'),'#skF_3') != k1_funct_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_787,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | k1_funct_1('#skF_5','#skF_3') = k1_xboole_0
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_771,c_42])).

tff(c_801,plain,(
    k1_funct_1('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_787])).

tff(c_36,plain,(
    ! [A_17,B_18] :
      ( v1_funct_1(k7_relat_1(A_17,B_18))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k7_relat_1(A_7,B_8))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_69,plain,(
    ! [A_40,C_41,B_42] :
      ( r2_hidden(A_40,k1_relat_1(C_41))
      | ~ r2_hidden(A_40,k1_relat_1(k7_relat_1(C_41,B_42)))
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_826,plain,(
    ! [B_111,C_112,B_113] :
      ( r2_hidden(B_111,k1_relat_1(C_112))
      | ~ v1_relat_1(C_112)
      | k1_funct_1(k7_relat_1(C_112,B_113),B_111) = k1_xboole_0
      | ~ v1_funct_1(k7_relat_1(C_112,B_113))
      | ~ v1_relat_1(k7_relat_1(C_112,B_113)) ) ),
    inference(resolution,[status(thm)],[c_34,c_69])).

tff(c_836,plain,(
    ! [B_114,A_115,B_116] :
      ( r2_hidden(B_114,k1_relat_1(A_115))
      | k1_funct_1(k7_relat_1(A_115,B_116),B_114) = k1_xboole_0
      | ~ v1_funct_1(k7_relat_1(A_115,B_116))
      | ~ v1_relat_1(A_115) ) ),
    inference(resolution,[status(thm)],[c_20,c_826])).

tff(c_840,plain,(
    ! [B_117,A_118,B_119] :
      ( r2_hidden(B_117,k1_relat_1(A_118))
      | k1_funct_1(k7_relat_1(A_118,B_119),B_117) = k1_xboole_0
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118) ) ),
    inference(resolution,[status(thm)],[c_36,c_836])).

tff(c_30,plain,(
    ! [B_15,A_12] :
      ( r2_hidden(k4_tarski(B_15,k1_funct_1(A_12,B_15)),A_12)
      | ~ r2_hidden(B_15,k1_relat_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_808,plain,
    ( r2_hidden(k4_tarski('#skF_3',k1_xboole_0),'#skF_5')
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_801,c_30])).

tff(c_812,plain,
    ( r2_hidden(k4_tarski('#skF_3',k1_xboole_0),'#skF_5')
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_808])).

tff(c_825,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_812])).

tff(c_843,plain,(
    ! [B_119] :
      ( k1_funct_1(k7_relat_1('#skF_5',B_119),'#skF_3') = k1_xboole_0
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_840,c_825])).

tff(c_902,plain,(
    ! [B_119] : k1_funct_1(k7_relat_1('#skF_5',B_119),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_843])).

tff(c_804,plain,(
    k1_funct_1(k7_relat_1('#skF_5','#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_801,c_42])).

tff(c_917,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_902,c_804])).

tff(c_919,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_812])).

tff(c_316,plain,(
    ! [C_64,B_2,D_6] :
      ( k1_funct_1(k7_relat_1(C_64,B_2),D_6) = k1_funct_1(C_64,D_6)
      | ~ v1_funct_1(C_64)
      | ~ v1_relat_1(C_64)
      | ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k1_relat_1(C_64)) ) ),
    inference(resolution,[status(thm)],[c_2,c_276])).

tff(c_921,plain,(
    ! [B_2] :
      ( k1_funct_1(k7_relat_1('#skF_5',B_2),'#skF_3') = k1_funct_1('#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ r2_hidden('#skF_3',B_2) ) ),
    inference(resolution,[status(thm)],[c_919,c_316])).

tff(c_931,plain,(
    ! [B_120] :
      ( k1_funct_1(k7_relat_1('#skF_5',B_120),'#skF_3') = k1_xboole_0
      | ~ r2_hidden('#skF_3',B_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_801,c_921])).

tff(c_937,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_931,c_804])).

tff(c_970,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_937])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:41:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.32/2.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.32/2.10  
% 4.32/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.32/2.11  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k3_xboole_0 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 4.32/2.11  
% 4.32/2.11  %Foreground sorts:
% 4.32/2.11  
% 4.32/2.11  
% 4.32/2.11  %Background operators:
% 4.32/2.11  
% 4.32/2.11  
% 4.32/2.11  %Foreground operators:
% 4.32/2.11  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.32/2.11  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.32/2.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.32/2.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.32/2.11  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.32/2.11  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.32/2.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.32/2.11  tff('#skF_5', type, '#skF_5': $i).
% 4.32/2.11  tff('#skF_3', type, '#skF_3': $i).
% 4.32/2.11  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.32/2.11  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.32/2.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.32/2.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.32/2.11  tff('#skF_4', type, '#skF_4': $i).
% 4.32/2.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.32/2.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.32/2.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.32/2.11  
% 4.32/2.13  tff(f_89, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, B) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_funct_1)).
% 4.32/2.13  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 4.32/2.13  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.32/2.13  tff(f_80, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_funct_1)).
% 4.32/2.13  tff(f_72, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 4.32/2.13  tff(f_38, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 4.32/2.13  tff(f_46, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 4.32/2.13  tff(c_44, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.32/2.13  tff(c_48, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.32/2.13  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.32/2.13  tff(c_34, plain, (![A_12, B_15]: (k1_funct_1(A_12, B_15)=k1_xboole_0 | r2_hidden(B_15, k1_relat_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.32/2.13  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k3_xboole_0(A_1, B_2)) | ~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.32/2.13  tff(c_276, plain, (![C_64, B_65, A_66]: (k1_funct_1(k7_relat_1(C_64, B_65), A_66)=k1_funct_1(C_64, A_66) | ~r2_hidden(A_66, k3_xboole_0(k1_relat_1(C_64), B_65)) | ~v1_funct_1(C_64) | ~v1_relat_1(C_64))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.32/2.13  tff(c_712, plain, (![C_105, B_106, D_107]: (k1_funct_1(k7_relat_1(C_105, B_106), D_107)=k1_funct_1(C_105, D_107) | ~v1_funct_1(C_105) | ~v1_relat_1(C_105) | ~r2_hidden(D_107, B_106) | ~r2_hidden(D_107, k1_relat_1(C_105)))), inference(resolution, [status(thm)], [c_2, c_276])).
% 4.32/2.13  tff(c_771, plain, (![A_108, B_109, B_110]: (k1_funct_1(k7_relat_1(A_108, B_109), B_110)=k1_funct_1(A_108, B_110) | ~r2_hidden(B_110, B_109) | k1_funct_1(A_108, B_110)=k1_xboole_0 | ~v1_funct_1(A_108) | ~v1_relat_1(A_108))), inference(resolution, [status(thm)], [c_34, c_712])).
% 4.32/2.13  tff(c_42, plain, (k1_funct_1(k7_relat_1('#skF_5', '#skF_4'), '#skF_3')!=k1_funct_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.32/2.13  tff(c_787, plain, (~r2_hidden('#skF_3', '#skF_4') | k1_funct_1('#skF_5', '#skF_3')=k1_xboole_0 | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_771, c_42])).
% 4.32/2.13  tff(c_801, plain, (k1_funct_1('#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_787])).
% 4.32/2.13  tff(c_36, plain, (![A_17, B_18]: (v1_funct_1(k7_relat_1(A_17, B_18)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.32/2.13  tff(c_20, plain, (![A_7, B_8]: (v1_relat_1(k7_relat_1(A_7, B_8)) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.32/2.13  tff(c_69, plain, (![A_40, C_41, B_42]: (r2_hidden(A_40, k1_relat_1(C_41)) | ~r2_hidden(A_40, k1_relat_1(k7_relat_1(C_41, B_42))) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.32/2.13  tff(c_826, plain, (![B_111, C_112, B_113]: (r2_hidden(B_111, k1_relat_1(C_112)) | ~v1_relat_1(C_112) | k1_funct_1(k7_relat_1(C_112, B_113), B_111)=k1_xboole_0 | ~v1_funct_1(k7_relat_1(C_112, B_113)) | ~v1_relat_1(k7_relat_1(C_112, B_113)))), inference(resolution, [status(thm)], [c_34, c_69])).
% 4.32/2.13  tff(c_836, plain, (![B_114, A_115, B_116]: (r2_hidden(B_114, k1_relat_1(A_115)) | k1_funct_1(k7_relat_1(A_115, B_116), B_114)=k1_xboole_0 | ~v1_funct_1(k7_relat_1(A_115, B_116)) | ~v1_relat_1(A_115))), inference(resolution, [status(thm)], [c_20, c_826])).
% 4.32/2.13  tff(c_840, plain, (![B_117, A_118, B_119]: (r2_hidden(B_117, k1_relat_1(A_118)) | k1_funct_1(k7_relat_1(A_118, B_119), B_117)=k1_xboole_0 | ~v1_funct_1(A_118) | ~v1_relat_1(A_118))), inference(resolution, [status(thm)], [c_36, c_836])).
% 4.32/2.13  tff(c_30, plain, (![B_15, A_12]: (r2_hidden(k4_tarski(B_15, k1_funct_1(A_12, B_15)), A_12) | ~r2_hidden(B_15, k1_relat_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.32/2.13  tff(c_808, plain, (r2_hidden(k4_tarski('#skF_3', k1_xboole_0), '#skF_5') | ~r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_801, c_30])).
% 4.32/2.13  tff(c_812, plain, (r2_hidden(k4_tarski('#skF_3', k1_xboole_0), '#skF_5') | ~r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_808])).
% 4.32/2.13  tff(c_825, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_812])).
% 4.32/2.13  tff(c_843, plain, (![B_119]: (k1_funct_1(k7_relat_1('#skF_5', B_119), '#skF_3')=k1_xboole_0 | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_840, c_825])).
% 4.32/2.13  tff(c_902, plain, (![B_119]: (k1_funct_1(k7_relat_1('#skF_5', B_119), '#skF_3')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_843])).
% 4.32/2.13  tff(c_804, plain, (k1_funct_1(k7_relat_1('#skF_5', '#skF_4'), '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_801, c_42])).
% 4.32/2.13  tff(c_917, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_902, c_804])).
% 4.32/2.13  tff(c_919, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_812])).
% 4.32/2.13  tff(c_316, plain, (![C_64, B_2, D_6]: (k1_funct_1(k7_relat_1(C_64, B_2), D_6)=k1_funct_1(C_64, D_6) | ~v1_funct_1(C_64) | ~v1_relat_1(C_64) | ~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k1_relat_1(C_64)))), inference(resolution, [status(thm)], [c_2, c_276])).
% 4.32/2.13  tff(c_921, plain, (![B_2]: (k1_funct_1(k7_relat_1('#skF_5', B_2), '#skF_3')=k1_funct_1('#skF_5', '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r2_hidden('#skF_3', B_2))), inference(resolution, [status(thm)], [c_919, c_316])).
% 4.32/2.13  tff(c_931, plain, (![B_120]: (k1_funct_1(k7_relat_1('#skF_5', B_120), '#skF_3')=k1_xboole_0 | ~r2_hidden('#skF_3', B_120))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_801, c_921])).
% 4.32/2.13  tff(c_937, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_931, c_804])).
% 4.32/2.13  tff(c_970, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_937])).
% 4.32/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.32/2.13  
% 4.32/2.13  Inference rules
% 4.32/2.13  ----------------------
% 4.32/2.13  #Ref     : 0
% 4.32/2.13  #Sup     : 197
% 4.32/2.13  #Fact    : 0
% 4.32/2.13  #Define  : 0
% 4.32/2.13  #Split   : 1
% 4.32/2.13  #Chain   : 0
% 4.32/2.13  #Close   : 0
% 4.32/2.13  
% 4.32/2.13  Ordering : KBO
% 4.53/2.13  
% 4.53/2.13  Simplification rules
% 4.53/2.13  ----------------------
% 4.53/2.13  #Subsume      : 25
% 4.53/2.13  #Demod        : 61
% 4.53/2.13  #Tautology    : 38
% 4.53/2.13  #SimpNegUnit  : 0
% 4.53/2.13  #BackRed      : 2
% 4.53/2.13  
% 4.53/2.13  #Partial instantiations: 0
% 4.53/2.13  #Strategies tried      : 1
% 4.53/2.13  
% 4.53/2.13  Timing (in seconds)
% 4.53/2.13  ----------------------
% 4.53/2.13  Preprocessing        : 0.47
% 4.53/2.13  Parsing              : 0.25
% 4.53/2.13  CNF conversion       : 0.04
% 4.53/2.13  Main loop            : 0.74
% 4.53/2.13  Inferencing          : 0.27
% 4.53/2.13  Reduction            : 0.17
% 4.53/2.13  Demodulation         : 0.12
% 4.53/2.13  BG Simplification    : 0.05
% 4.53/2.13  Subsumption          : 0.17
% 4.53/2.13  Abstraction          : 0.05
% 4.53/2.13  MUC search           : 0.00
% 4.53/2.13  Cooper               : 0.00
% 4.53/2.13  Total                : 1.26
% 4.53/2.13  Index Insertion      : 0.00
% 4.53/2.13  Index Deletion       : 0.00
% 4.53/2.13  Index Matching       : 0.00
% 4.53/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
