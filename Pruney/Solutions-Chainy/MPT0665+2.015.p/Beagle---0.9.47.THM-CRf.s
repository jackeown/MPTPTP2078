%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:16 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 116 expanded)
%              Number of leaves         :   25 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :   92 ( 306 expanded)
%              Number of equality atoms :    8 (  21 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r2_hidden(A,k1_relat_1(C))
            & r2_hidden(A,B) )
         => r2_hidden(k1_funct_1(C,A),k2_relat_1(k7_relat_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_44,axiom,(
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

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_funct_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( v1_funct_1(k7_relat_1(A_13,B_14))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_38,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_36,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_24,plain,(
    ! [B_12,A_11] :
      ( k3_xboole_0(k1_relat_1(B_12),A_11) = k1_relat_1(k7_relat_1(B_12,A_11))
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_71,plain,(
    ! [D_34,A_35,B_36] :
      ( r2_hidden(D_34,k3_xboole_0(A_35,B_36))
      | ~ r2_hidden(D_34,B_36)
      | ~ r2_hidden(D_34,A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_80,plain,(
    ! [D_34,B_12,A_11] :
      ( r2_hidden(D_34,k1_relat_1(k7_relat_1(B_12,A_11)))
      | ~ r2_hidden(D_34,A_11)
      | ~ r2_hidden(D_34,k1_relat_1(B_12))
      | ~ v1_relat_1(B_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_71])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( v1_relat_1(k7_relat_1(A_9,B_10))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k3_xboole_0(A_1,B_2))
      | ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_240,plain,(
    ! [C_61,B_62,A_63] :
      ( k1_funct_1(k7_relat_1(C_61,B_62),A_63) = k1_funct_1(C_61,A_63)
      | ~ r2_hidden(A_63,k3_xboole_0(k1_relat_1(C_61),B_62))
      | ~ v1_funct_1(C_61)
      | ~ v1_relat_1(C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_736,plain,(
    ! [C_96,B_97,D_98] :
      ( k1_funct_1(k7_relat_1(C_96,B_97),D_98) = k1_funct_1(C_96,D_98)
      | ~ v1_funct_1(C_96)
      | ~ v1_relat_1(C_96)
      | ~ r2_hidden(D_98,B_97)
      | ~ r2_hidden(D_98,k1_relat_1(C_96)) ) ),
    inference(resolution,[status(thm)],[c_2,c_240])).

tff(c_780,plain,(
    ! [B_97] :
      ( k1_funct_1(k7_relat_1('#skF_5',B_97),'#skF_3') = k1_funct_1('#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ r2_hidden('#skF_3',B_97) ) ),
    inference(resolution,[status(thm)],[c_38,c_736])).

tff(c_797,plain,(
    ! [B_99] :
      ( k1_funct_1(k7_relat_1('#skF_5',B_99),'#skF_3') = k1_funct_1('#skF_5','#skF_3')
      | ~ r2_hidden('#skF_3',B_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_780])).

tff(c_30,plain,(
    ! [B_16,A_15] :
      ( r2_hidden(k1_funct_1(B_16,A_15),k2_relat_1(B_16))
      | ~ r2_hidden(A_15,k1_relat_1(B_16))
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1160,plain,(
    ! [B_114] :
      ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),k2_relat_1(k7_relat_1('#skF_5',B_114)))
      | ~ r2_hidden('#skF_3',k1_relat_1(k7_relat_1('#skF_5',B_114)))
      | ~ v1_funct_1(k7_relat_1('#skF_5',B_114))
      | ~ v1_relat_1(k7_relat_1('#skF_5',B_114))
      | ~ r2_hidden('#skF_3',B_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_797,c_30])).

tff(c_34,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),k2_relat_1(k7_relat_1('#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1163,plain,
    ( ~ r2_hidden('#skF_3',k1_relat_1(k7_relat_1('#skF_5','#skF_4')))
    | ~ v1_funct_1(k7_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_1160,c_34])).

tff(c_1166,plain,
    ( ~ r2_hidden('#skF_3',k1_relat_1(k7_relat_1('#skF_5','#skF_4')))
    | ~ v1_funct_1(k7_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1163])).

tff(c_1167,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1166])).

tff(c_1170,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_1167])).

tff(c_1174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1170])).

tff(c_1175,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_5','#skF_4'))
    | ~ r2_hidden('#skF_3',k1_relat_1(k7_relat_1('#skF_5','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1166])).

tff(c_1177,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1(k7_relat_1('#skF_5','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1175])).

tff(c_1180,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_1177])).

tff(c_1184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_36,c_1180])).

tff(c_1185,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_5','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1175])).

tff(c_1286,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_1185])).

tff(c_1290,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1286])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:51:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.24/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.62  
% 3.24/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.62  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 3.24/1.62  
% 3.24/1.62  %Foreground sorts:
% 3.24/1.62  
% 3.24/1.62  
% 3.24/1.62  %Background operators:
% 3.24/1.62  
% 3.24/1.62  
% 3.24/1.62  %Foreground operators:
% 3.24/1.62  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.24/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.24/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.24/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.24/1.62  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.24/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.24/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.24/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.24/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.24/1.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.24/1.62  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.24/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.24/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.24/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.24/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.24/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.24/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.24/1.62  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.24/1.62  
% 3.66/1.63  tff(f_79, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(A, B)) => r2_hidden(k1_funct_1(C, A), k2_relat_1(k7_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_funct_1)).
% 3.66/1.63  tff(f_52, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 3.66/1.63  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 3.66/1.63  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.66/1.63  tff(f_40, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.66/1.63  tff(f_68, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_funct_1)).
% 3.66/1.63  tff(f_60, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 3.66/1.63  tff(c_42, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.66/1.63  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.66/1.63  tff(c_26, plain, (![A_13, B_14]: (v1_funct_1(k7_relat_1(A_13, B_14)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.66/1.63  tff(c_38, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.66/1.63  tff(c_36, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.66/1.63  tff(c_24, plain, (![B_12, A_11]: (k3_xboole_0(k1_relat_1(B_12), A_11)=k1_relat_1(k7_relat_1(B_12, A_11)) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.66/1.63  tff(c_71, plain, (![D_34, A_35, B_36]: (r2_hidden(D_34, k3_xboole_0(A_35, B_36)) | ~r2_hidden(D_34, B_36) | ~r2_hidden(D_34, A_35))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.66/1.63  tff(c_80, plain, (![D_34, B_12, A_11]: (r2_hidden(D_34, k1_relat_1(k7_relat_1(B_12, A_11))) | ~r2_hidden(D_34, A_11) | ~r2_hidden(D_34, k1_relat_1(B_12)) | ~v1_relat_1(B_12))), inference(superposition, [status(thm), theory('equality')], [c_24, c_71])).
% 3.66/1.63  tff(c_22, plain, (![A_9, B_10]: (v1_relat_1(k7_relat_1(A_9, B_10)) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.66/1.63  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k3_xboole_0(A_1, B_2)) | ~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.66/1.63  tff(c_240, plain, (![C_61, B_62, A_63]: (k1_funct_1(k7_relat_1(C_61, B_62), A_63)=k1_funct_1(C_61, A_63) | ~r2_hidden(A_63, k3_xboole_0(k1_relat_1(C_61), B_62)) | ~v1_funct_1(C_61) | ~v1_relat_1(C_61))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.66/1.63  tff(c_736, plain, (![C_96, B_97, D_98]: (k1_funct_1(k7_relat_1(C_96, B_97), D_98)=k1_funct_1(C_96, D_98) | ~v1_funct_1(C_96) | ~v1_relat_1(C_96) | ~r2_hidden(D_98, B_97) | ~r2_hidden(D_98, k1_relat_1(C_96)))), inference(resolution, [status(thm)], [c_2, c_240])).
% 3.66/1.63  tff(c_780, plain, (![B_97]: (k1_funct_1(k7_relat_1('#skF_5', B_97), '#skF_3')=k1_funct_1('#skF_5', '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r2_hidden('#skF_3', B_97))), inference(resolution, [status(thm)], [c_38, c_736])).
% 3.66/1.63  tff(c_797, plain, (![B_99]: (k1_funct_1(k7_relat_1('#skF_5', B_99), '#skF_3')=k1_funct_1('#skF_5', '#skF_3') | ~r2_hidden('#skF_3', B_99))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_780])).
% 3.66/1.63  tff(c_30, plain, (![B_16, A_15]: (r2_hidden(k1_funct_1(B_16, A_15), k2_relat_1(B_16)) | ~r2_hidden(A_15, k1_relat_1(B_16)) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.66/1.63  tff(c_1160, plain, (![B_114]: (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), k2_relat_1(k7_relat_1('#skF_5', B_114))) | ~r2_hidden('#skF_3', k1_relat_1(k7_relat_1('#skF_5', B_114))) | ~v1_funct_1(k7_relat_1('#skF_5', B_114)) | ~v1_relat_1(k7_relat_1('#skF_5', B_114)) | ~r2_hidden('#skF_3', B_114))), inference(superposition, [status(thm), theory('equality')], [c_797, c_30])).
% 3.66/1.63  tff(c_34, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), k2_relat_1(k7_relat_1('#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.66/1.63  tff(c_1163, plain, (~r2_hidden('#skF_3', k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))) | ~v1_funct_1(k7_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_4')) | ~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_1160, c_34])).
% 3.66/1.63  tff(c_1166, plain, (~r2_hidden('#skF_3', k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))) | ~v1_funct_1(k7_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1163])).
% 3.66/1.63  tff(c_1167, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_1166])).
% 3.66/1.63  tff(c_1170, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_1167])).
% 3.66/1.63  tff(c_1174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_1170])).
% 3.66/1.63  tff(c_1175, plain, (~v1_funct_1(k7_relat_1('#skF_5', '#skF_4')) | ~r2_hidden('#skF_3', k1_relat_1(k7_relat_1('#skF_5', '#skF_4')))), inference(splitRight, [status(thm)], [c_1166])).
% 3.66/1.63  tff(c_1177, plain, (~r2_hidden('#skF_3', k1_relat_1(k7_relat_1('#skF_5', '#skF_4')))), inference(splitLeft, [status(thm)], [c_1175])).
% 3.66/1.63  tff(c_1180, plain, (~r2_hidden('#skF_3', '#skF_4') | ~r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_80, c_1177])).
% 3.66/1.63  tff(c_1184, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_36, c_1180])).
% 3.66/1.63  tff(c_1185, plain, (~v1_funct_1(k7_relat_1('#skF_5', '#skF_4'))), inference(splitRight, [status(thm)], [c_1175])).
% 3.66/1.63  tff(c_1286, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_26, c_1185])).
% 3.66/1.63  tff(c_1290, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1286])).
% 3.66/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.63  
% 3.66/1.63  Inference rules
% 3.66/1.63  ----------------------
% 3.66/1.63  #Ref     : 0
% 3.66/1.63  #Sup     : 280
% 3.66/1.63  #Fact    : 0
% 3.66/1.63  #Define  : 0
% 3.66/1.63  #Split   : 2
% 3.66/1.63  #Chain   : 0
% 3.66/1.63  #Close   : 0
% 3.66/1.63  
% 3.66/1.63  Ordering : KBO
% 3.66/1.63  
% 3.66/1.63  Simplification rules
% 3.66/1.63  ----------------------
% 3.66/1.63  #Subsume      : 36
% 3.66/1.63  #Demod        : 58
% 3.66/1.63  #Tautology    : 35
% 3.66/1.63  #SimpNegUnit  : 0
% 3.66/1.63  #BackRed      : 0
% 3.66/1.63  
% 3.66/1.63  #Partial instantiations: 0
% 3.66/1.63  #Strategies tried      : 1
% 3.66/1.63  
% 3.66/1.63  Timing (in seconds)
% 3.66/1.63  ----------------------
% 3.66/1.64  Preprocessing        : 0.32
% 3.66/1.64  Parsing              : 0.17
% 3.66/1.64  CNF conversion       : 0.02
% 3.66/1.64  Main loop            : 0.49
% 3.66/1.64  Inferencing          : 0.18
% 3.66/1.64  Reduction            : 0.11
% 3.66/1.64  Demodulation         : 0.08
% 3.66/1.64  BG Simplification    : 0.03
% 3.66/1.64  Subsumption          : 0.12
% 3.66/1.64  Abstraction          : 0.04
% 3.66/1.64  MUC search           : 0.00
% 3.66/1.64  Cooper               : 0.00
% 3.66/1.64  Total                : 0.84
% 3.66/1.64  Index Insertion      : 0.00
% 3.66/1.64  Index Deletion       : 0.00
% 3.66/1.64  Index Matching       : 0.00
% 3.66/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
