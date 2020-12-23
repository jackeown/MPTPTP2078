%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:23 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 172 expanded)
%              Number of leaves         :   25 (  68 expanded)
%              Depth                    :    9
%              Number of atoms          :   94 ( 310 expanded)
%              Number of equality atoms :    4 (  34 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_73,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k4_xboole_0(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_30,B_31] :
      ( v1_relat_1(k4_xboole_0(A_30,B_31))
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_91,plain,(
    ! [A_44,B_45] :
      ( v1_relat_1(k3_xboole_0(A_44,B_45))
      | ~ v1_relat_1(A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_18])).

tff(c_94,plain,(
    ! [B_2,A_1] :
      ( v1_relat_1(k3_xboole_0(B_2,A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_91])).

tff(c_20,plain,(
    ! [A_32,B_34] :
      ( r1_tarski(k2_relat_1(A_32),k2_relat_1(B_34))
      | ~ r1_tarski(A_32,B_34)
      | ~ v1_relat_1(B_34)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_141,plain,(
    ! [A_56,B_57,C_58] :
      ( r1_tarski(A_56,k3_xboole_0(B_57,C_58))
      | ~ r1_tarski(A_56,C_58)
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_xboole_0(k2_relat_1('#skF_3'),k2_relat_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_29,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_4','#skF_3')),k3_xboole_0(k2_relat_1('#skF_4'),k2_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_24])).

tff(c_159,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_4','#skF_3')),k2_relat_1('#skF_3'))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_4','#skF_3')),k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_141,c_29])).

tff(c_195,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_4','#skF_3')),k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_198,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_3'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_195])).

tff(c_201,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_3'),'#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_198])).

tff(c_202,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_201])).

tff(c_205,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_202])).

tff(c_212,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_205])).

tff(c_214,plain,(
    v1_relat_1(k3_xboole_0('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_16,plain,(
    ! [A_13,B_23] :
      ( r2_hidden(k4_tarski('#skF_1'(A_13,B_23),'#skF_2'(A_13,B_23)),A_13)
      | r1_tarski(A_13,B_23)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_426,plain,(
    ! [A_77,B_78] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_77,B_78),'#skF_2'(A_77,B_78)),B_78)
      | r1_tarski(A_77,B_78)
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_432,plain,(
    ! [A_79] :
      ( r1_tarski(A_79,A_79)
      | ~ v1_relat_1(A_79) ) ),
    inference(resolution,[status(thm)],[c_16,c_426])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_tarski(A_3,B_4)
      | ~ r1_tarski(A_3,k3_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_466,plain,(
    ! [B_82,C_83] :
      ( r1_tarski(k3_xboole_0(B_82,C_83),B_82)
      | ~ v1_relat_1(k3_xboole_0(B_82,C_83)) ) ),
    inference(resolution,[status(thm)],[c_432,c_4])).

tff(c_213,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_469,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_466,c_213])).

tff(c_493,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_469])).

tff(c_494,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_4','#skF_3')),k2_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_498,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_3'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_494])).

tff(c_501,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_3'),'#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_498])).

tff(c_502,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_501])).

tff(c_505,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_502])).

tff(c_512,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_505])).

tff(c_514,plain,(
    v1_relat_1(k3_xboole_0('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_501])).

tff(c_726,plain,(
    ! [A_98,B_99] :
      ( r2_hidden(k4_tarski('#skF_1'(A_98,B_99),'#skF_2'(A_98,B_99)),A_98)
      | r1_tarski(A_98,B_99)
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ! [A_13,B_23] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_13,B_23),'#skF_2'(A_13,B_23)),B_23)
      | r1_tarski(A_13,B_23)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_732,plain,(
    ! [A_100] :
      ( r1_tarski(A_100,A_100)
      | ~ v1_relat_1(A_100) ) ),
    inference(resolution,[status(thm)],[c_726,c_14])).

tff(c_105,plain,(
    ! [A_48,B_49,C_50] :
      ( r1_tarski(A_48,B_49)
      | ~ r1_tarski(A_48,k3_xboole_0(B_49,C_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_108,plain,(
    ! [A_48,A_1,B_2] :
      ( r1_tarski(A_48,A_1)
      | ~ r1_tarski(A_48,k3_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_105])).

tff(c_743,plain,(
    ! [B_101,A_102] :
      ( r1_tarski(k3_xboole_0(B_101,A_102),A_102)
      | ~ v1_relat_1(k3_xboole_0(B_101,A_102)) ) ),
    inference(resolution,[status(thm)],[c_732,c_108])).

tff(c_513,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_501])).

tff(c_746,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_743,c_513])).

tff(c_770,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_746])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:19:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.52  
% 2.97/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.52  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.97/1.52  
% 2.97/1.52  %Foreground sorts:
% 2.97/1.52  
% 2.97/1.52  
% 2.97/1.52  %Background operators:
% 2.97/1.52  
% 2.97/1.52  
% 2.97/1.52  %Foreground operators:
% 2.97/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.97/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.97/1.52  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.97/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.97/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.97/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.97/1.52  tff('#skF_3', type, '#skF_3': $i).
% 2.97/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.97/1.52  tff('#skF_4', type, '#skF_4': $i).
% 2.97/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.97/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.97/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.97/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.97/1.52  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.97/1.52  
% 3.30/1.54  tff(f_74, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_relat_1)).
% 3.30/1.54  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.30/1.54  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.30/1.54  tff(f_55, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_relat_1)).
% 3.30/1.54  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 3.30/1.54  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.30/1.54  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 3.30/1.54  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 3.30/1.54  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.30/1.54  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.30/1.54  tff(c_73, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k4_xboole_0(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.30/1.54  tff(c_18, plain, (![A_30, B_31]: (v1_relat_1(k4_xboole_0(A_30, B_31)) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.30/1.54  tff(c_91, plain, (![A_44, B_45]: (v1_relat_1(k3_xboole_0(A_44, B_45)) | ~v1_relat_1(A_44))), inference(superposition, [status(thm), theory('equality')], [c_73, c_18])).
% 3.30/1.54  tff(c_94, plain, (![B_2, A_1]: (v1_relat_1(k3_xboole_0(B_2, A_1)) | ~v1_relat_1(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_91])).
% 3.30/1.54  tff(c_20, plain, (![A_32, B_34]: (r1_tarski(k2_relat_1(A_32), k2_relat_1(B_34)) | ~r1_tarski(A_32, B_34) | ~v1_relat_1(B_34) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.30/1.54  tff(c_26, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.30/1.54  tff(c_141, plain, (![A_56, B_57, C_58]: (r1_tarski(A_56, k3_xboole_0(B_57, C_58)) | ~r1_tarski(A_56, C_58) | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.30/1.54  tff(c_24, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_xboole_0(k2_relat_1('#skF_3'), k2_relat_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.30/1.54  tff(c_29, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_4', '#skF_3')), k3_xboole_0(k2_relat_1('#skF_4'), k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_24])).
% 3.30/1.54  tff(c_159, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_4', '#skF_3')), k2_relat_1('#skF_3')) | ~r1_tarski(k2_relat_1(k3_xboole_0('#skF_4', '#skF_3')), k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_141, c_29])).
% 3.30/1.54  tff(c_195, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_4', '#skF_3')), k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_159])).
% 3.30/1.54  tff(c_198, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_195])).
% 3.30/1.54  tff(c_201, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), '#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_198])).
% 3.30/1.54  tff(c_202, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_201])).
% 3.30/1.54  tff(c_205, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_202])).
% 3.30/1.54  tff(c_212, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_205])).
% 3.30/1.54  tff(c_214, plain, (v1_relat_1(k3_xboole_0('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_201])).
% 3.30/1.54  tff(c_16, plain, (![A_13, B_23]: (r2_hidden(k4_tarski('#skF_1'(A_13, B_23), '#skF_2'(A_13, B_23)), A_13) | r1_tarski(A_13, B_23) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.30/1.54  tff(c_426, plain, (![A_77, B_78]: (~r2_hidden(k4_tarski('#skF_1'(A_77, B_78), '#skF_2'(A_77, B_78)), B_78) | r1_tarski(A_77, B_78) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.30/1.54  tff(c_432, plain, (![A_79]: (r1_tarski(A_79, A_79) | ~v1_relat_1(A_79))), inference(resolution, [status(thm)], [c_16, c_426])).
% 3.30/1.54  tff(c_4, plain, (![A_3, B_4, C_5]: (r1_tarski(A_3, B_4) | ~r1_tarski(A_3, k3_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.30/1.54  tff(c_466, plain, (![B_82, C_83]: (r1_tarski(k3_xboole_0(B_82, C_83), B_82) | ~v1_relat_1(k3_xboole_0(B_82, C_83)))), inference(resolution, [status(thm)], [c_432, c_4])).
% 3.30/1.54  tff(c_213, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_201])).
% 3.30/1.54  tff(c_469, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_466, c_213])).
% 3.30/1.54  tff(c_493, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_214, c_469])).
% 3.30/1.54  tff(c_494, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_4', '#skF_3')), k2_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_159])).
% 3.30/1.54  tff(c_498, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_494])).
% 3.30/1.54  tff(c_501, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), '#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_498])).
% 3.30/1.54  tff(c_502, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_501])).
% 3.30/1.54  tff(c_505, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_502])).
% 3.30/1.54  tff(c_512, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_505])).
% 3.30/1.54  tff(c_514, plain, (v1_relat_1(k3_xboole_0('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_501])).
% 3.30/1.54  tff(c_726, plain, (![A_98, B_99]: (r2_hidden(k4_tarski('#skF_1'(A_98, B_99), '#skF_2'(A_98, B_99)), A_98) | r1_tarski(A_98, B_99) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.30/1.54  tff(c_14, plain, (![A_13, B_23]: (~r2_hidden(k4_tarski('#skF_1'(A_13, B_23), '#skF_2'(A_13, B_23)), B_23) | r1_tarski(A_13, B_23) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.30/1.54  tff(c_732, plain, (![A_100]: (r1_tarski(A_100, A_100) | ~v1_relat_1(A_100))), inference(resolution, [status(thm)], [c_726, c_14])).
% 3.30/1.54  tff(c_105, plain, (![A_48, B_49, C_50]: (r1_tarski(A_48, B_49) | ~r1_tarski(A_48, k3_xboole_0(B_49, C_50)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.30/1.54  tff(c_108, plain, (![A_48, A_1, B_2]: (r1_tarski(A_48, A_1) | ~r1_tarski(A_48, k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_105])).
% 3.30/1.54  tff(c_743, plain, (![B_101, A_102]: (r1_tarski(k3_xboole_0(B_101, A_102), A_102) | ~v1_relat_1(k3_xboole_0(B_101, A_102)))), inference(resolution, [status(thm)], [c_732, c_108])).
% 3.30/1.54  tff(c_513, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_501])).
% 3.30/1.54  tff(c_746, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_743, c_513])).
% 3.30/1.54  tff(c_770, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_514, c_746])).
% 3.30/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.54  
% 3.30/1.54  Inference rules
% 3.30/1.54  ----------------------
% 3.30/1.54  #Ref     : 0
% 3.30/1.54  #Sup     : 190
% 3.30/1.54  #Fact    : 0
% 3.30/1.54  #Define  : 0
% 3.30/1.54  #Split   : 3
% 3.30/1.54  #Chain   : 0
% 3.30/1.54  #Close   : 0
% 3.30/1.54  
% 3.30/1.54  Ordering : KBO
% 3.30/1.54  
% 3.30/1.54  Simplification rules
% 3.30/1.54  ----------------------
% 3.30/1.54  #Subsume      : 40
% 3.30/1.54  #Demod        : 44
% 3.30/1.54  #Tautology    : 52
% 3.30/1.54  #SimpNegUnit  : 0
% 3.30/1.54  #BackRed      : 0
% 3.30/1.54  
% 3.30/1.54  #Partial instantiations: 0
% 3.30/1.54  #Strategies tried      : 1
% 3.30/1.54  
% 3.30/1.54  Timing (in seconds)
% 3.30/1.54  ----------------------
% 3.30/1.54  Preprocessing        : 0.32
% 3.30/1.54  Parsing              : 0.17
% 3.30/1.54  CNF conversion       : 0.02
% 3.30/1.55  Main loop            : 0.41
% 3.30/1.55  Inferencing          : 0.14
% 3.30/1.55  Reduction            : 0.16
% 3.30/1.55  Demodulation         : 0.14
% 3.30/1.55  BG Simplification    : 0.02
% 3.30/1.55  Subsumption          : 0.07
% 3.30/1.55  Abstraction          : 0.02
% 3.30/1.55  MUC search           : 0.00
% 3.30/1.55  Cooper               : 0.00
% 3.30/1.55  Total                : 0.76
% 3.30/1.55  Index Insertion      : 0.00
% 3.30/1.55  Index Deletion       : 0.00
% 3.30/1.55  Index Matching       : 0.00
% 3.30/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
