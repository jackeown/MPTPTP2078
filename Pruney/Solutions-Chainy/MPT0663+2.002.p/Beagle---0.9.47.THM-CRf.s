%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:11 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 106 expanded)
%              Number of leaves         :   36 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :  110 ( 177 expanded)
%              Number of equality atoms :   27 (  43 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_34,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_50,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_125,plain,(
    ! [A_62,B_63] : k1_setfam_1(k2_tarski(A_62,B_63)) = k3_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_140,plain,(
    ! [B_64,A_65] : k1_setfam_1(k2_tarski(B_64,A_65)) = k3_xboole_0(A_65,B_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_125])).

tff(c_24,plain,(
    ! [A_37,B_38] : k1_setfam_1(k2_tarski(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_146,plain,(
    ! [B_64,A_65] : k3_xboole_0(B_64,A_65) = k3_xboole_0(A_65,B_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_24])).

tff(c_48,plain,(
    r2_hidden('#skF_3',k3_xboole_0(k1_relat_1('#skF_5'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_163,plain,(
    r2_hidden('#skF_3',k3_xboole_0('#skF_4',k1_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_48])).

tff(c_231,plain,(
    ! [C_77,B_78,A_79] :
      ( r2_hidden(C_77,B_78)
      | ~ r2_hidden(C_77,A_79)
      | ~ r1_tarski(A_79,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_256,plain,(
    ! [B_85] :
      ( r2_hidden('#skF_3',B_85)
      | ~ r1_tarski(k3_xboole_0('#skF_4',k1_relat_1('#skF_5')),B_85) ) ),
    inference(resolution,[status(thm)],[c_163,c_231])).

tff(c_272,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_256])).

tff(c_52,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_214,plain,(
    ! [A_72,B_73] :
      ( r2_hidden('#skF_1'(A_72,B_73),A_72)
      | r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_219,plain,(
    ! [A_72] : r1_tarski(A_72,A_72) ),
    inference(resolution,[status(thm)],[c_214,c_4])).

tff(c_50,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_32,plain,(
    ! [A_42] : v1_relat_1(k6_relat_1(A_42)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_34,plain,(
    ! [A_42] : v1_funct_1(k6_relat_1(A_42)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_42,plain,(
    ! [A_47,C_51] :
      ( k1_funct_1(k6_relat_1(A_47),C_51) = C_51
      | ~ r2_hidden(C_51,A_47)
      | ~ v1_funct_1(k6_relat_1(A_47))
      | ~ v1_relat_1(k6_relat_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_56,plain,(
    ! [A_47,C_51] :
      ( k1_funct_1(k6_relat_1(A_47),C_51) = C_51
      | ~ r2_hidden(C_51,A_47)
      | ~ v1_relat_1(k6_relat_1(A_47)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_42])).

tff(c_58,plain,(
    ! [A_47,C_51] :
      ( k1_funct_1(k6_relat_1(A_47),C_51) = C_51
      | ~ r2_hidden(C_51,A_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_56])).

tff(c_30,plain,(
    ! [A_40,B_41] :
      ( k5_relat_1(k6_relat_1(A_40),B_41) = k7_relat_1(B_41,A_40)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_44,plain,(
    ! [A_47] :
      ( k1_relat_1(k6_relat_1(A_47)) = A_47
      | ~ v1_funct_1(k6_relat_1(A_47))
      | ~ v1_relat_1(k6_relat_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_54,plain,(
    ! [A_47] :
      ( k1_relat_1(k6_relat_1(A_47)) = A_47
      | ~ v1_relat_1(k6_relat_1(A_47)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_44])).

tff(c_60,plain,(
    ! [A_47] : k1_relat_1(k6_relat_1(A_47)) = A_47 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_54])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_275,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_3',B_2)
      | ~ r1_tarski('#skF_4',B_2) ) ),
    inference(resolution,[status(thm)],[c_272,c_2])).

tff(c_586,plain,(
    ! [B_165,C_166,A_167] :
      ( k1_funct_1(k5_relat_1(B_165,C_166),A_167) = k1_funct_1(C_166,k1_funct_1(B_165,A_167))
      | ~ r2_hidden(A_167,k1_relat_1(B_165))
      | ~ v1_funct_1(C_166)
      | ~ v1_relat_1(C_166)
      | ~ v1_funct_1(B_165)
      | ~ v1_relat_1(B_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_682,plain,(
    ! [B_177,C_178] :
      ( k1_funct_1(k5_relat_1(B_177,C_178),'#skF_3') = k1_funct_1(C_178,k1_funct_1(B_177,'#skF_3'))
      | ~ v1_funct_1(C_178)
      | ~ v1_relat_1(C_178)
      | ~ v1_funct_1(B_177)
      | ~ v1_relat_1(B_177)
      | ~ r1_tarski('#skF_4',k1_relat_1(B_177)) ) ),
    inference(resolution,[status(thm)],[c_275,c_586])).

tff(c_684,plain,(
    ! [A_47,C_178] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_47),C_178),'#skF_3') = k1_funct_1(C_178,k1_funct_1(k6_relat_1(A_47),'#skF_3'))
      | ~ v1_funct_1(C_178)
      | ~ v1_relat_1(C_178)
      | ~ v1_funct_1(k6_relat_1(A_47))
      | ~ v1_relat_1(k6_relat_1(A_47))
      | ~ r1_tarski('#skF_4',A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_682])).

tff(c_1057,plain,(
    ! [A_224,C_225] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_224),C_225),'#skF_3') = k1_funct_1(C_225,k1_funct_1(k6_relat_1(A_224),'#skF_3'))
      | ~ v1_funct_1(C_225)
      | ~ v1_relat_1(C_225)
      | ~ r1_tarski('#skF_4',A_224) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_684])).

tff(c_1203,plain,(
    ! [B_239,A_240] :
      ( k1_funct_1(B_239,k1_funct_1(k6_relat_1(A_240),'#skF_3')) = k1_funct_1(k7_relat_1(B_239,A_240),'#skF_3')
      | ~ v1_funct_1(B_239)
      | ~ v1_relat_1(B_239)
      | ~ r1_tarski('#skF_4',A_240)
      | ~ v1_relat_1(B_239) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1057])).

tff(c_1463,plain,(
    ! [B_268,A_269] :
      ( k1_funct_1(k7_relat_1(B_268,A_269),'#skF_3') = k1_funct_1(B_268,'#skF_3')
      | ~ v1_funct_1(B_268)
      | ~ v1_relat_1(B_268)
      | ~ r1_tarski('#skF_4',A_269)
      | ~ v1_relat_1(B_268)
      | ~ r2_hidden('#skF_3',A_269) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_1203])).

tff(c_46,plain,(
    k1_funct_1(k7_relat_1('#skF_5','#skF_4'),'#skF_3') != k1_funct_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1469,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ r1_tarski('#skF_4','#skF_4')
    | ~ v1_relat_1('#skF_5')
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1463,c_46])).

tff(c_1477,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_52,c_219,c_50,c_1469])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:55:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.74/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/1.78  
% 3.74/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/1.79  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.74/1.79  
% 3.74/1.79  %Foreground sorts:
% 3.74/1.79  
% 3.74/1.79  
% 3.74/1.79  %Background operators:
% 3.74/1.79  
% 3.74/1.79  
% 3.74/1.79  %Foreground operators:
% 3.74/1.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.74/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.74/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.74/1.79  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.74/1.79  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.74/1.79  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.74/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.74/1.79  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.74/1.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.74/1.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.74/1.79  tff('#skF_5', type, '#skF_5': $i).
% 3.74/1.79  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.74/1.79  tff('#skF_3', type, '#skF_3': $i).
% 3.74/1.79  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.74/1.79  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.74/1.79  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.74/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.74/1.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.74/1.79  tff('#skF_4', type, '#skF_4': $i).
% 3.74/1.79  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.74/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.74/1.79  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.74/1.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.74/1.79  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.74/1.79  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.74/1.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.74/1.79  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.74/1.79  
% 3.74/1.80  tff(f_34, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.74/1.80  tff(f_36, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.74/1.80  tff(f_50, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.74/1.80  tff(f_97, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_funct_1)).
% 3.74/1.80  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.74/1.80  tff(f_62, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.74/1.80  tff(f_88, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 3.74/1.80  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 3.74/1.80  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 3.74/1.80  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.74/1.80  tff(c_10, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.74/1.80  tff(c_125, plain, (![A_62, B_63]: (k1_setfam_1(k2_tarski(A_62, B_63))=k3_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.74/1.80  tff(c_140, plain, (![B_64, A_65]: (k1_setfam_1(k2_tarski(B_64, A_65))=k3_xboole_0(A_65, B_64))), inference(superposition, [status(thm), theory('equality')], [c_10, c_125])).
% 3.74/1.80  tff(c_24, plain, (![A_37, B_38]: (k1_setfam_1(k2_tarski(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.74/1.80  tff(c_146, plain, (![B_64, A_65]: (k3_xboole_0(B_64, A_65)=k3_xboole_0(A_65, B_64))), inference(superposition, [status(thm), theory('equality')], [c_140, c_24])).
% 3.74/1.80  tff(c_48, plain, (r2_hidden('#skF_3', k3_xboole_0(k1_relat_1('#skF_5'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.74/1.80  tff(c_163, plain, (r2_hidden('#skF_3', k3_xboole_0('#skF_4', k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_48])).
% 3.74/1.80  tff(c_231, plain, (![C_77, B_78, A_79]: (r2_hidden(C_77, B_78) | ~r2_hidden(C_77, A_79) | ~r1_tarski(A_79, B_78))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.74/1.80  tff(c_256, plain, (![B_85]: (r2_hidden('#skF_3', B_85) | ~r1_tarski(k3_xboole_0('#skF_4', k1_relat_1('#skF_5')), B_85))), inference(resolution, [status(thm)], [c_163, c_231])).
% 3.74/1.80  tff(c_272, plain, (r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_8, c_256])).
% 3.74/1.80  tff(c_52, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.74/1.80  tff(c_214, plain, (![A_72, B_73]: (r2_hidden('#skF_1'(A_72, B_73), A_72) | r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.74/1.80  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.74/1.80  tff(c_219, plain, (![A_72]: (r1_tarski(A_72, A_72))), inference(resolution, [status(thm)], [c_214, c_4])).
% 3.74/1.80  tff(c_50, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.74/1.80  tff(c_32, plain, (![A_42]: (v1_relat_1(k6_relat_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.74/1.80  tff(c_34, plain, (![A_42]: (v1_funct_1(k6_relat_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.74/1.80  tff(c_42, plain, (![A_47, C_51]: (k1_funct_1(k6_relat_1(A_47), C_51)=C_51 | ~r2_hidden(C_51, A_47) | ~v1_funct_1(k6_relat_1(A_47)) | ~v1_relat_1(k6_relat_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.74/1.80  tff(c_56, plain, (![A_47, C_51]: (k1_funct_1(k6_relat_1(A_47), C_51)=C_51 | ~r2_hidden(C_51, A_47) | ~v1_relat_1(k6_relat_1(A_47)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_42])).
% 3.74/1.80  tff(c_58, plain, (![A_47, C_51]: (k1_funct_1(k6_relat_1(A_47), C_51)=C_51 | ~r2_hidden(C_51, A_47))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_56])).
% 3.74/1.80  tff(c_30, plain, (![A_40, B_41]: (k5_relat_1(k6_relat_1(A_40), B_41)=k7_relat_1(B_41, A_40) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.74/1.80  tff(c_44, plain, (![A_47]: (k1_relat_1(k6_relat_1(A_47))=A_47 | ~v1_funct_1(k6_relat_1(A_47)) | ~v1_relat_1(k6_relat_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.74/1.80  tff(c_54, plain, (![A_47]: (k1_relat_1(k6_relat_1(A_47))=A_47 | ~v1_relat_1(k6_relat_1(A_47)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_44])).
% 3.74/1.80  tff(c_60, plain, (![A_47]: (k1_relat_1(k6_relat_1(A_47))=A_47)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_54])).
% 3.74/1.80  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.74/1.80  tff(c_275, plain, (![B_2]: (r2_hidden('#skF_3', B_2) | ~r1_tarski('#skF_4', B_2))), inference(resolution, [status(thm)], [c_272, c_2])).
% 3.74/1.80  tff(c_586, plain, (![B_165, C_166, A_167]: (k1_funct_1(k5_relat_1(B_165, C_166), A_167)=k1_funct_1(C_166, k1_funct_1(B_165, A_167)) | ~r2_hidden(A_167, k1_relat_1(B_165)) | ~v1_funct_1(C_166) | ~v1_relat_1(C_166) | ~v1_funct_1(B_165) | ~v1_relat_1(B_165))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.74/1.80  tff(c_682, plain, (![B_177, C_178]: (k1_funct_1(k5_relat_1(B_177, C_178), '#skF_3')=k1_funct_1(C_178, k1_funct_1(B_177, '#skF_3')) | ~v1_funct_1(C_178) | ~v1_relat_1(C_178) | ~v1_funct_1(B_177) | ~v1_relat_1(B_177) | ~r1_tarski('#skF_4', k1_relat_1(B_177)))), inference(resolution, [status(thm)], [c_275, c_586])).
% 3.74/1.80  tff(c_684, plain, (![A_47, C_178]: (k1_funct_1(k5_relat_1(k6_relat_1(A_47), C_178), '#skF_3')=k1_funct_1(C_178, k1_funct_1(k6_relat_1(A_47), '#skF_3')) | ~v1_funct_1(C_178) | ~v1_relat_1(C_178) | ~v1_funct_1(k6_relat_1(A_47)) | ~v1_relat_1(k6_relat_1(A_47)) | ~r1_tarski('#skF_4', A_47))), inference(superposition, [status(thm), theory('equality')], [c_60, c_682])).
% 3.74/1.80  tff(c_1057, plain, (![A_224, C_225]: (k1_funct_1(k5_relat_1(k6_relat_1(A_224), C_225), '#skF_3')=k1_funct_1(C_225, k1_funct_1(k6_relat_1(A_224), '#skF_3')) | ~v1_funct_1(C_225) | ~v1_relat_1(C_225) | ~r1_tarski('#skF_4', A_224))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_684])).
% 3.74/1.80  tff(c_1203, plain, (![B_239, A_240]: (k1_funct_1(B_239, k1_funct_1(k6_relat_1(A_240), '#skF_3'))=k1_funct_1(k7_relat_1(B_239, A_240), '#skF_3') | ~v1_funct_1(B_239) | ~v1_relat_1(B_239) | ~r1_tarski('#skF_4', A_240) | ~v1_relat_1(B_239))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1057])).
% 3.74/1.80  tff(c_1463, plain, (![B_268, A_269]: (k1_funct_1(k7_relat_1(B_268, A_269), '#skF_3')=k1_funct_1(B_268, '#skF_3') | ~v1_funct_1(B_268) | ~v1_relat_1(B_268) | ~r1_tarski('#skF_4', A_269) | ~v1_relat_1(B_268) | ~r2_hidden('#skF_3', A_269))), inference(superposition, [status(thm), theory('equality')], [c_58, c_1203])).
% 3.74/1.80  tff(c_46, plain, (k1_funct_1(k7_relat_1('#skF_5', '#skF_4'), '#skF_3')!=k1_funct_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.74/1.80  tff(c_1469, plain, (~v1_funct_1('#skF_5') | ~r1_tarski('#skF_4', '#skF_4') | ~v1_relat_1('#skF_5') | ~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1463, c_46])).
% 3.74/1.80  tff(c_1477, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_272, c_52, c_219, c_50, c_1469])).
% 3.74/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/1.80  
% 3.74/1.80  Inference rules
% 3.74/1.80  ----------------------
% 3.74/1.80  #Ref     : 0
% 3.74/1.80  #Sup     : 349
% 3.74/1.80  #Fact    : 0
% 3.74/1.80  #Define  : 0
% 3.74/1.80  #Split   : 0
% 3.74/1.80  #Chain   : 0
% 3.74/1.80  #Close   : 0
% 3.74/1.80  
% 3.74/1.80  Ordering : KBO
% 3.74/1.80  
% 3.74/1.80  Simplification rules
% 3.74/1.80  ----------------------
% 3.74/1.80  #Subsume      : 78
% 3.74/1.80  #Demod        : 136
% 3.74/1.80  #Tautology    : 103
% 3.74/1.80  #SimpNegUnit  : 0
% 3.74/1.80  #BackRed      : 1
% 3.74/1.80  
% 3.74/1.80  #Partial instantiations: 0
% 3.74/1.80  #Strategies tried      : 1
% 3.74/1.80  
% 3.74/1.80  Timing (in seconds)
% 3.74/1.80  ----------------------
% 3.74/1.80  Preprocessing        : 0.32
% 3.74/1.80  Parsing              : 0.15
% 3.74/1.80  CNF conversion       : 0.02
% 3.74/1.80  Main loop            : 0.53
% 3.74/1.80  Inferencing          : 0.18
% 3.74/1.80  Reduction            : 0.18
% 3.74/1.80  Demodulation         : 0.15
% 3.74/1.80  BG Simplification    : 0.03
% 3.74/1.80  Subsumption          : 0.11
% 3.74/1.80  Abstraction          : 0.03
% 3.74/1.80  MUC search           : 0.00
% 3.74/1.80  Cooper               : 0.00
% 3.74/1.80  Total                : 0.89
% 3.74/1.80  Index Insertion      : 0.00
% 3.74/1.80  Index Deletion       : 0.00
% 3.74/1.80  Index Matching       : 0.00
% 3.74/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
