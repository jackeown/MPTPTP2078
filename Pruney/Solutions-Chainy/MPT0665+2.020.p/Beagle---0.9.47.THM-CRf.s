%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:16 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 118 expanded)
%              Number of leaves         :   21 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :   91 ( 329 expanded)
%              Number of equality atoms :    8 (  24 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r2_hidden(A,k1_relat_1(C))
            & r2_hidden(A,B) )
         => r2_hidden(k1_funct_1(C,A),k2_relat_1(k7_relat_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_26,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( v1_funct_1(k7_relat_1(A_8,B_9))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_24,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r2_hidden(A_3,k1_relat_1(k7_relat_1(C_5,B_4)))
      | ~ r2_hidden(A_3,k1_relat_1(C_5))
      | ~ r2_hidden(A_3,B_4)
      | ~ v1_relat_1(C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k7_relat_1(A_1,B_2))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( k3_xboole_0(k1_relat_1(B_7),A_6) = k1_relat_1(k7_relat_1(B_7,A_6))
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_52,plain,(
    ! [C_32,B_33,A_34] :
      ( k1_funct_1(k7_relat_1(C_32,B_33),A_34) = k1_funct_1(C_32,A_34)
      | ~ r2_hidden(A_34,k3_xboole_0(k1_relat_1(C_32),B_33))
      | ~ v1_funct_1(C_32)
      | ~ v1_relat_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_56,plain,(
    ! [B_35,A_36,A_37] :
      ( k1_funct_1(k7_relat_1(B_35,A_36),A_37) = k1_funct_1(B_35,A_37)
      | ~ r2_hidden(A_37,k1_relat_1(k7_relat_1(B_35,A_36)))
      | ~ v1_funct_1(B_35)
      | ~ v1_relat_1(B_35)
      | ~ v1_relat_1(B_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_52])).

tff(c_61,plain,(
    ! [C_38,B_39,A_40] :
      ( k1_funct_1(k7_relat_1(C_38,B_39),A_40) = k1_funct_1(C_38,A_40)
      | ~ v1_funct_1(C_38)
      | ~ r2_hidden(A_40,k1_relat_1(C_38))
      | ~ r2_hidden(A_40,B_39)
      | ~ v1_relat_1(C_38) ) ),
    inference(resolution,[status(thm)],[c_4,c_56])).

tff(c_65,plain,(
    ! [B_39] :
      ( k1_funct_1(k7_relat_1('#skF_3',B_39),'#skF_1') = k1_funct_1('#skF_3','#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ r2_hidden('#skF_1',B_39)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_61])).

tff(c_70,plain,(
    ! [B_41] :
      ( k1_funct_1(k7_relat_1('#skF_3',B_41),'#skF_1') = k1_funct_1('#skF_3','#skF_1')
      | ~ r2_hidden('#skF_1',B_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_65])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( r2_hidden(k1_funct_1(B_11,A_10),k2_relat_1(B_11))
      | ~ r2_hidden(A_10,k1_relat_1(B_11))
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_82,plain,(
    ! [B_42] :
      ( r2_hidden(k1_funct_1('#skF_3','#skF_1'),k2_relat_1(k7_relat_1('#skF_3',B_42)))
      | ~ r2_hidden('#skF_1',k1_relat_1(k7_relat_1('#skF_3',B_42)))
      | ~ v1_funct_1(k7_relat_1('#skF_3',B_42))
      | ~ v1_relat_1(k7_relat_1('#skF_3',B_42))
      | ~ r2_hidden('#skF_1',B_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_16])).

tff(c_20,plain,(
    ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),k2_relat_1(k7_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_85,plain,
    ( ~ r2_hidden('#skF_1',k1_relat_1(k7_relat_1('#skF_3','#skF_2')))
    | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_20])).

tff(c_88,plain,
    ( ~ r2_hidden('#skF_1',k1_relat_1(k7_relat_1('#skF_3','#skF_2')))
    | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_85])).

tff(c_89,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_92,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_89])).

tff(c_96,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_92])).

tff(c_97,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ r2_hidden('#skF_1',k1_relat_1(k7_relat_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_99,plain,(
    ~ r2_hidden('#skF_1',k1_relat_1(k7_relat_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_102,plain,
    ( ~ r2_hidden('#skF_1',k1_relat_1('#skF_3'))
    | ~ r2_hidden('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_99])).

tff(c_106,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_22,c_24,c_102])).

tff(c_107,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_111,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_107])).

tff(c_115,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_111])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:17:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.57  
% 2.40/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.58  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.40/1.58  
% 2.40/1.58  %Foreground sorts:
% 2.40/1.58  
% 2.40/1.58  
% 2.40/1.58  %Background operators:
% 2.40/1.58  
% 2.40/1.58  
% 2.40/1.58  %Foreground operators:
% 2.40/1.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.40/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.40/1.58  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.40/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.40/1.58  tff('#skF_2', type, '#skF_2': $i).
% 2.40/1.58  tff('#skF_3', type, '#skF_3': $i).
% 2.40/1.58  tff('#skF_1', type, '#skF_1': $i).
% 2.40/1.58  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.40/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.40/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.40/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.40/1.58  
% 2.40/1.60  tff(f_76, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(A, B)) => r2_hidden(k1_funct_1(C, A), k2_relat_1(k7_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_funct_1)).
% 2.40/1.60  tff(f_49, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 2.40/1.60  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 2.40/1.60  tff(f_29, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.40/1.60  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.40/1.60  tff(f_65, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_funct_1)).
% 2.40/1.60  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 2.40/1.60  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.40/1.60  tff(c_26, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.40/1.60  tff(c_12, plain, (![A_8, B_9]: (v1_funct_1(k7_relat_1(A_8, B_9)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.40/1.60  tff(c_22, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.40/1.60  tff(c_24, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.40/1.60  tff(c_4, plain, (![A_3, C_5, B_4]: (r2_hidden(A_3, k1_relat_1(k7_relat_1(C_5, B_4))) | ~r2_hidden(A_3, k1_relat_1(C_5)) | ~r2_hidden(A_3, B_4) | ~v1_relat_1(C_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.40/1.60  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k7_relat_1(A_1, B_2)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.40/1.60  tff(c_10, plain, (![B_7, A_6]: (k3_xboole_0(k1_relat_1(B_7), A_6)=k1_relat_1(k7_relat_1(B_7, A_6)) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.40/1.60  tff(c_52, plain, (![C_32, B_33, A_34]: (k1_funct_1(k7_relat_1(C_32, B_33), A_34)=k1_funct_1(C_32, A_34) | ~r2_hidden(A_34, k3_xboole_0(k1_relat_1(C_32), B_33)) | ~v1_funct_1(C_32) | ~v1_relat_1(C_32))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.40/1.60  tff(c_56, plain, (![B_35, A_36, A_37]: (k1_funct_1(k7_relat_1(B_35, A_36), A_37)=k1_funct_1(B_35, A_37) | ~r2_hidden(A_37, k1_relat_1(k7_relat_1(B_35, A_36))) | ~v1_funct_1(B_35) | ~v1_relat_1(B_35) | ~v1_relat_1(B_35))), inference(superposition, [status(thm), theory('equality')], [c_10, c_52])).
% 2.40/1.60  tff(c_61, plain, (![C_38, B_39, A_40]: (k1_funct_1(k7_relat_1(C_38, B_39), A_40)=k1_funct_1(C_38, A_40) | ~v1_funct_1(C_38) | ~r2_hidden(A_40, k1_relat_1(C_38)) | ~r2_hidden(A_40, B_39) | ~v1_relat_1(C_38))), inference(resolution, [status(thm)], [c_4, c_56])).
% 2.40/1.60  tff(c_65, plain, (![B_39]: (k1_funct_1(k7_relat_1('#skF_3', B_39), '#skF_1')=k1_funct_1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3') | ~r2_hidden('#skF_1', B_39) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_61])).
% 2.40/1.60  tff(c_70, plain, (![B_41]: (k1_funct_1(k7_relat_1('#skF_3', B_41), '#skF_1')=k1_funct_1('#skF_3', '#skF_1') | ~r2_hidden('#skF_1', B_41))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_65])).
% 2.40/1.60  tff(c_16, plain, (![B_11, A_10]: (r2_hidden(k1_funct_1(B_11, A_10), k2_relat_1(B_11)) | ~r2_hidden(A_10, k1_relat_1(B_11)) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.40/1.60  tff(c_82, plain, (![B_42]: (r2_hidden(k1_funct_1('#skF_3', '#skF_1'), k2_relat_1(k7_relat_1('#skF_3', B_42))) | ~r2_hidden('#skF_1', k1_relat_1(k7_relat_1('#skF_3', B_42))) | ~v1_funct_1(k7_relat_1('#skF_3', B_42)) | ~v1_relat_1(k7_relat_1('#skF_3', B_42)) | ~r2_hidden('#skF_1', B_42))), inference(superposition, [status(thm), theory('equality')], [c_70, c_16])).
% 2.40/1.60  tff(c_20, plain, (~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), k2_relat_1(k7_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.40/1.60  tff(c_85, plain, (~r2_hidden('#skF_1', k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))) | ~v1_funct_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_82, c_20])).
% 2.40/1.60  tff(c_88, plain, (~r2_hidden('#skF_1', k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))) | ~v1_funct_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_85])).
% 2.40/1.60  tff(c_89, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_88])).
% 2.40/1.60  tff(c_92, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2, c_89])).
% 2.40/1.60  tff(c_96, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_92])).
% 2.40/1.60  tff(c_97, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_2')) | ~r2_hidden('#skF_1', k1_relat_1(k7_relat_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_88])).
% 2.40/1.60  tff(c_99, plain, (~r2_hidden('#skF_1', k1_relat_1(k7_relat_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_97])).
% 2.40/1.60  tff(c_102, plain, (~r2_hidden('#skF_1', k1_relat_1('#skF_3')) | ~r2_hidden('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4, c_99])).
% 2.40/1.60  tff(c_106, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_22, c_24, c_102])).
% 2.40/1.60  tff(c_107, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_97])).
% 2.40/1.60  tff(c_111, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_107])).
% 2.40/1.60  tff(c_115, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_111])).
% 2.40/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.60  
% 2.40/1.60  Inference rules
% 2.40/1.60  ----------------------
% 2.40/1.60  #Ref     : 0
% 2.40/1.60  #Sup     : 15
% 2.40/1.60  #Fact    : 0
% 2.40/1.60  #Define  : 0
% 2.40/1.60  #Split   : 2
% 2.40/1.60  #Chain   : 0
% 2.40/1.60  #Close   : 0
% 2.40/1.60  
% 2.40/1.60  Ordering : KBO
% 2.40/1.60  
% 2.40/1.60  Simplification rules
% 2.40/1.60  ----------------------
% 2.40/1.60  #Subsume      : 1
% 2.40/1.60  #Demod        : 9
% 2.40/1.60  #Tautology    : 6
% 2.40/1.60  #SimpNegUnit  : 0
% 2.40/1.60  #BackRed      : 0
% 2.40/1.60  
% 2.40/1.60  #Partial instantiations: 0
% 2.40/1.60  #Strategies tried      : 1
% 2.40/1.60  
% 2.40/1.60  Timing (in seconds)
% 2.40/1.60  ----------------------
% 2.40/1.60  Preprocessing        : 0.49
% 2.40/1.60  Parsing              : 0.26
% 2.40/1.60  CNF conversion       : 0.03
% 2.40/1.60  Main loop            : 0.25
% 2.40/1.60  Inferencing          : 0.10
% 2.40/1.60  Reduction            : 0.06
% 2.40/1.60  Demodulation         : 0.05
% 2.40/1.60  BG Simplification    : 0.02
% 2.40/1.60  Subsumption          : 0.05
% 2.40/1.60  Abstraction          : 0.01
% 2.40/1.60  MUC search           : 0.00
% 2.40/1.60  Cooper               : 0.00
% 2.40/1.60  Total                : 0.78
% 2.40/1.60  Index Insertion      : 0.00
% 2.40/1.60  Index Deletion       : 0.00
% 2.40/1.60  Index Matching       : 0.00
% 2.40/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
