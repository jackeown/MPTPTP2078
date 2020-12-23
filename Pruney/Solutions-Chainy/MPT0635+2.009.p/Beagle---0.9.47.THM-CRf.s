%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:21 EST 2020

% Result     : Theorem 22.04s
% Output     : CNFRefutation 22.04s
% Verified   : 
% Statistics : Number of formulae       :   51 (  64 expanded)
%              Number of leaves         :   26 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :  102 ( 136 expanded)
%              Number of equality atoms :   13 (  21 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(C,A) = k1_funct_1(k5_relat_1(k6_relat_1(B),C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( v1_relat_1(D)
     => ( r2_hidden(k4_tarski(A,B),k5_relat_1(k6_relat_1(C),D))
      <=> ( r2_hidden(A,C)
          & r2_hidden(k4_tarski(A,B),D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_relat_1)).

tff(c_52,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_50,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_48,plain,(
    r2_hidden('#skF_3',k3_xboole_0(k1_relat_1('#skF_5'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_53,plain,(
    r2_hidden('#skF_3',k3_xboole_0('#skF_4',k1_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_48])).

tff(c_104,plain,(
    ! [D_29,B_30,A_31] :
      ( r2_hidden(D_29,B_30)
      | ~ r2_hidden(D_29,k3_xboole_0(A_31,B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_114,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_53,c_104])).

tff(c_115,plain,(
    ! [D_32,A_33,B_34] :
      ( r2_hidden(D_32,A_33)
      | ~ r2_hidden(D_32,k3_xboole_0(A_33,B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_125,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_53,c_115])).

tff(c_40,plain,(
    ! [A_20,C_22] :
      ( r2_hidden(k4_tarski(A_20,k1_funct_1(C_22,A_20)),C_22)
      | ~ r2_hidden(A_20,k1_relat_1(C_22))
      | ~ v1_funct_1(C_22)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_36,plain,(
    ! [A_19] : v1_relat_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_38,plain,(
    ! [A_19] : v1_funct_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_32,plain,(
    ! [A_17,B_18] :
      ( v1_funct_1(k5_relat_1(A_17,B_18))
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( v1_relat_1(k5_relat_1(A_11,B_12))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1211,plain,(
    ! [A_109,B_110,C_111,D_112] :
      ( r2_hidden(k4_tarski(A_109,B_110),k5_relat_1(k6_relat_1(C_111),D_112))
      | ~ r2_hidden(k4_tarski(A_109,B_110),D_112)
      | ~ r2_hidden(A_109,C_111)
      | ~ v1_relat_1(D_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_42,plain,(
    ! [C_22,A_20,B_21] :
      ( k1_funct_1(C_22,A_20) = B_21
      | ~ r2_hidden(k4_tarski(A_20,B_21),C_22)
      | ~ v1_funct_1(C_22)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12301,plain,(
    ! [C_336,D_337,A_338,B_339] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(C_336),D_337),A_338) = B_339
      | ~ v1_funct_1(k5_relat_1(k6_relat_1(C_336),D_337))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(C_336),D_337))
      | ~ r2_hidden(k4_tarski(A_338,B_339),D_337)
      | ~ r2_hidden(A_338,C_336)
      | ~ v1_relat_1(D_337) ) ),
    inference(resolution,[status(thm)],[c_1211,c_42])).

tff(c_12304,plain,(
    ! [C_336,B_12,A_338,B_339] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(C_336),B_12),A_338) = B_339
      | ~ v1_funct_1(k5_relat_1(k6_relat_1(C_336),B_12))
      | ~ r2_hidden(k4_tarski(A_338,B_339),B_12)
      | ~ r2_hidden(A_338,C_336)
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(k6_relat_1(C_336)) ) ),
    inference(resolution,[status(thm)],[c_24,c_12301])).

tff(c_39361,plain,(
    ! [C_522,B_523,A_524,B_525] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(C_522),B_523),A_524) = B_525
      | ~ v1_funct_1(k5_relat_1(k6_relat_1(C_522),B_523))
      | ~ r2_hidden(k4_tarski(A_524,B_525),B_523)
      | ~ r2_hidden(A_524,C_522)
      | ~ v1_relat_1(B_523) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_12304])).

tff(c_39364,plain,(
    ! [C_522,B_18,A_524,B_525] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(C_522),B_18),A_524) = B_525
      | ~ r2_hidden(k4_tarski(A_524,B_525),B_18)
      | ~ r2_hidden(A_524,C_522)
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_funct_1(k6_relat_1(C_522))
      | ~ v1_relat_1(k6_relat_1(C_522)) ) ),
    inference(resolution,[status(thm)],[c_32,c_39361])).

tff(c_39368,plain,(
    ! [C_526,B_527,A_528,B_529] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(C_526),B_527),A_528) = B_529
      | ~ r2_hidden(k4_tarski(A_528,B_529),B_527)
      | ~ r2_hidden(A_528,C_526)
      | ~ v1_funct_1(B_527)
      | ~ v1_relat_1(B_527) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38,c_39364])).

tff(c_39408,plain,(
    ! [C_530,C_531,A_532] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(C_530),C_531),A_532) = k1_funct_1(C_531,A_532)
      | ~ r2_hidden(A_532,C_530)
      | ~ r2_hidden(A_532,k1_relat_1(C_531))
      | ~ v1_funct_1(C_531)
      | ~ v1_relat_1(C_531) ) ),
    inference(resolution,[status(thm)],[c_40,c_39368])).

tff(c_46,plain,(
    k1_funct_1(k5_relat_1(k6_relat_1('#skF_4'),'#skF_5'),'#skF_3') != k1_funct_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_39420,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_39408,c_46])).

tff(c_39428,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_114,c_125,c_39420])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:04:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.04/13.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.04/13.03  
% 22.04/13.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.04/13.03  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 22.04/13.03  
% 22.04/13.03  %Foreground sorts:
% 22.04/13.03  
% 22.04/13.03  
% 22.04/13.03  %Background operators:
% 22.04/13.03  
% 22.04/13.03  
% 22.04/13.03  %Foreground operators:
% 22.04/13.03  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 22.04/13.03  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 22.04/13.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.04/13.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 22.04/13.03  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 22.04/13.03  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 22.04/13.03  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 22.04/13.03  tff('#skF_5', type, '#skF_5': $i).
% 22.04/13.03  tff('#skF_3', type, '#skF_3': $i).
% 22.04/13.03  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 22.04/13.03  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 22.04/13.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.04/13.03  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 22.04/13.03  tff('#skF_4', type, '#skF_4': $i).
% 22.04/13.03  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 22.04/13.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.04/13.03  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 22.04/13.03  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 22.04/13.03  
% 22.04/13.04  tff(f_87, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(C, A) = k1_funct_1(k5_relat_1(k6_relat_1(B), C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_1)).
% 22.04/13.04  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 22.04/13.04  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 22.04/13.04  tff(f_78, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 22.04/13.04  tff(f_68, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 22.04/13.04  tff(f_64, axiom, (![A, B]: ((((v1_relat_1(A) & v1_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v1_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_funct_1)).
% 22.04/13.04  tff(f_44, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 22.04/13.04  tff(f_52, axiom, (![A, B, C, D]: (v1_relat_1(D) => (r2_hidden(k4_tarski(A, B), k5_relat_1(k6_relat_1(C), D)) <=> (r2_hidden(A, C) & r2_hidden(k4_tarski(A, B), D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_relat_1)).
% 22.04/13.04  tff(c_52, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_87])).
% 22.04/13.04  tff(c_50, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_87])).
% 22.04/13.04  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 22.04/13.04  tff(c_48, plain, (r2_hidden('#skF_3', k3_xboole_0(k1_relat_1('#skF_5'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 22.04/13.04  tff(c_53, plain, (r2_hidden('#skF_3', k3_xboole_0('#skF_4', k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_48])).
% 22.04/13.04  tff(c_104, plain, (![D_29, B_30, A_31]: (r2_hidden(D_29, B_30) | ~r2_hidden(D_29, k3_xboole_0(A_31, B_30)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 22.04/13.04  tff(c_114, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_53, c_104])).
% 22.04/13.04  tff(c_115, plain, (![D_32, A_33, B_34]: (r2_hidden(D_32, A_33) | ~r2_hidden(D_32, k3_xboole_0(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 22.04/13.04  tff(c_125, plain, (r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_53, c_115])).
% 22.04/13.04  tff(c_40, plain, (![A_20, C_22]: (r2_hidden(k4_tarski(A_20, k1_funct_1(C_22, A_20)), C_22) | ~r2_hidden(A_20, k1_relat_1(C_22)) | ~v1_funct_1(C_22) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_78])).
% 22.04/13.04  tff(c_36, plain, (![A_19]: (v1_relat_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 22.04/13.04  tff(c_38, plain, (![A_19]: (v1_funct_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 22.04/13.04  tff(c_32, plain, (![A_17, B_18]: (v1_funct_1(k5_relat_1(A_17, B_18)) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 22.04/13.04  tff(c_24, plain, (![A_11, B_12]: (v1_relat_1(k5_relat_1(A_11, B_12)) | ~v1_relat_1(B_12) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 22.04/13.04  tff(c_1211, plain, (![A_109, B_110, C_111, D_112]: (r2_hidden(k4_tarski(A_109, B_110), k5_relat_1(k6_relat_1(C_111), D_112)) | ~r2_hidden(k4_tarski(A_109, B_110), D_112) | ~r2_hidden(A_109, C_111) | ~v1_relat_1(D_112))), inference(cnfTransformation, [status(thm)], [f_52])).
% 22.04/13.04  tff(c_42, plain, (![C_22, A_20, B_21]: (k1_funct_1(C_22, A_20)=B_21 | ~r2_hidden(k4_tarski(A_20, B_21), C_22) | ~v1_funct_1(C_22) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_78])).
% 22.04/13.04  tff(c_12301, plain, (![C_336, D_337, A_338, B_339]: (k1_funct_1(k5_relat_1(k6_relat_1(C_336), D_337), A_338)=B_339 | ~v1_funct_1(k5_relat_1(k6_relat_1(C_336), D_337)) | ~v1_relat_1(k5_relat_1(k6_relat_1(C_336), D_337)) | ~r2_hidden(k4_tarski(A_338, B_339), D_337) | ~r2_hidden(A_338, C_336) | ~v1_relat_1(D_337))), inference(resolution, [status(thm)], [c_1211, c_42])).
% 22.04/13.04  tff(c_12304, plain, (![C_336, B_12, A_338, B_339]: (k1_funct_1(k5_relat_1(k6_relat_1(C_336), B_12), A_338)=B_339 | ~v1_funct_1(k5_relat_1(k6_relat_1(C_336), B_12)) | ~r2_hidden(k4_tarski(A_338, B_339), B_12) | ~r2_hidden(A_338, C_336) | ~v1_relat_1(B_12) | ~v1_relat_1(k6_relat_1(C_336)))), inference(resolution, [status(thm)], [c_24, c_12301])).
% 22.04/13.04  tff(c_39361, plain, (![C_522, B_523, A_524, B_525]: (k1_funct_1(k5_relat_1(k6_relat_1(C_522), B_523), A_524)=B_525 | ~v1_funct_1(k5_relat_1(k6_relat_1(C_522), B_523)) | ~r2_hidden(k4_tarski(A_524, B_525), B_523) | ~r2_hidden(A_524, C_522) | ~v1_relat_1(B_523))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_12304])).
% 22.04/13.04  tff(c_39364, plain, (![C_522, B_18, A_524, B_525]: (k1_funct_1(k5_relat_1(k6_relat_1(C_522), B_18), A_524)=B_525 | ~r2_hidden(k4_tarski(A_524, B_525), B_18) | ~r2_hidden(A_524, C_522) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v1_funct_1(k6_relat_1(C_522)) | ~v1_relat_1(k6_relat_1(C_522)))), inference(resolution, [status(thm)], [c_32, c_39361])).
% 22.04/13.04  tff(c_39368, plain, (![C_526, B_527, A_528, B_529]: (k1_funct_1(k5_relat_1(k6_relat_1(C_526), B_527), A_528)=B_529 | ~r2_hidden(k4_tarski(A_528, B_529), B_527) | ~r2_hidden(A_528, C_526) | ~v1_funct_1(B_527) | ~v1_relat_1(B_527))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38, c_39364])).
% 22.04/13.04  tff(c_39408, plain, (![C_530, C_531, A_532]: (k1_funct_1(k5_relat_1(k6_relat_1(C_530), C_531), A_532)=k1_funct_1(C_531, A_532) | ~r2_hidden(A_532, C_530) | ~r2_hidden(A_532, k1_relat_1(C_531)) | ~v1_funct_1(C_531) | ~v1_relat_1(C_531))), inference(resolution, [status(thm)], [c_40, c_39368])).
% 22.04/13.04  tff(c_46, plain, (k1_funct_1(k5_relat_1(k6_relat_1('#skF_4'), '#skF_5'), '#skF_3')!=k1_funct_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 22.04/13.04  tff(c_39420, plain, (~r2_hidden('#skF_3', '#skF_4') | ~r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_39408, c_46])).
% 22.04/13.04  tff(c_39428, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_114, c_125, c_39420])).
% 22.04/13.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.04/13.04  
% 22.04/13.04  Inference rules
% 22.04/13.04  ----------------------
% 22.04/13.04  #Ref     : 0
% 22.04/13.04  #Sup     : 9501
% 22.04/13.04  #Fact    : 0
% 22.04/13.04  #Define  : 0
% 22.04/13.04  #Split   : 0
% 22.04/13.04  #Chain   : 0
% 22.04/13.04  #Close   : 0
% 22.04/13.04  
% 22.04/13.04  Ordering : KBO
% 22.04/13.04  
% 22.04/13.04  Simplification rules
% 22.04/13.04  ----------------------
% 22.04/13.04  #Subsume      : 991
% 22.04/13.04  #Demod        : 6272
% 22.04/13.04  #Tautology    : 607
% 22.04/13.04  #SimpNegUnit  : 0
% 22.04/13.04  #BackRed      : 0
% 22.04/13.04  
% 22.04/13.04  #Partial instantiations: 0
% 22.04/13.04  #Strategies tried      : 1
% 22.04/13.04  
% 22.04/13.04  Timing (in seconds)
% 22.04/13.04  ----------------------
% 22.04/13.05  Preprocessing        : 0.31
% 22.04/13.05  Parsing              : 0.17
% 22.04/13.05  CNF conversion       : 0.02
% 22.04/13.05  Main loop            : 11.92
% 22.04/13.05  Inferencing          : 1.35
% 22.04/13.05  Reduction            : 6.68
% 22.04/13.05  Demodulation         : 6.31
% 22.04/13.05  BG Simplification    : 0.26
% 22.04/13.05  Subsumption          : 3.21
% 22.04/13.05  Abstraction          : 0.45
% 22.04/13.05  MUC search           : 0.00
% 22.04/13.05  Cooper               : 0.00
% 22.04/13.05  Total                : 12.26
% 22.04/13.05  Index Insertion      : 0.00
% 22.04/13.05  Index Deletion       : 0.00
% 22.04/13.05  Index Matching       : 0.00
% 22.04/13.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
