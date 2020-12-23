%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:49 EST 2020

% Result     : Theorem 5.41s
% Output     : CNFRefutation 5.41s
% Verified   : 
% Statistics : Number of formulae       :   52 (  93 expanded)
%              Number of leaves         :   25 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :  128 ( 388 expanded)
%              Number of equality atoms :    6 (  11 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_wellord1 > r4_wellord1 > r2_hidden > r1_tarski > v2_wellord1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(r4_wellord1,type,(
    r4_wellord1: ( $i * $i ) > $o )).

tff(r3_wellord1,type,(
    r3_wellord1: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v1_funct_1(C) )
               => ( ( v2_wellord1(A)
                    & r3_wellord1(A,B,C) )
                 => ! [D] :
                      ~ ( r2_hidden(D,k3_relat_1(A))
                        & ! [E] :
                            ~ ( r2_hidden(E,k3_relat_1(B))
                              & r4_wellord1(k2_wellord1(A,k1_wellord1(A,D)),k2_wellord1(B,k1_wellord1(B,E))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_wellord1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ( r3_wellord1(A,B,C)
               => ! [D] :
                    ~ ( r2_hidden(D,k3_relat_1(A))
                      & ! [E] :
                          ~ ( r2_hidden(E,k3_relat_1(B))
                            & k9_relat_1(C,k1_wellord1(A,D)) = k1_wellord1(B,E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_wellord1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v2_wellord1(B)
       => k3_relat_1(k2_wellord1(B,k1_wellord1(B,A))) = k1_wellord1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_wellord1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k3_relat_1(k2_wellord1(B,A)),k3_relat_1(B))
        & r1_tarski(k3_relat_1(k2_wellord1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_wellord1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ! [D] :
              ( ( v1_relat_1(D)
                & v1_funct_1(D) )
             => ( ( v2_wellord1(B)
                  & r1_tarski(A,k3_relat_1(B))
                  & r3_wellord1(B,C,D) )
               => ( r3_wellord1(k2_wellord1(B,A),k2_wellord1(C,k9_relat_1(D,A)),k7_relat_1(D,A))
                  & r4_wellord1(k2_wellord1(B,A),k2_wellord1(C,k9_relat_1(D,A))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_wellord1)).

tff(c_26,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_24,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_20,plain,(
    r3_wellord1('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_18,plain,(
    r2_hidden('#skF_5',k3_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_14,plain,(
    ! [A_13,B_29,C_37,D_41] :
      ( r2_hidden('#skF_1'(A_13,B_29,C_37,D_41),k3_relat_1(B_29))
      | ~ r2_hidden(D_41,k3_relat_1(A_13))
      | ~ r3_wellord1(A_13,B_29,C_37)
      | ~ v1_funct_1(C_37)
      | ~ v1_relat_1(C_37)
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_22,plain,(
    v2_wellord1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_34,plain,(
    ! [B_75,A_76] :
      ( k3_relat_1(k2_wellord1(B_75,k1_wellord1(B_75,A_76))) = k1_wellord1(B_75,A_76)
      | ~ v2_wellord1(B_75)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k3_relat_1(k2_wellord1(B_2,A_1)),k3_relat_1(B_2))
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    ! [B_75,A_76] :
      ( r1_tarski(k1_wellord1(B_75,A_76),k3_relat_1(B_75))
      | ~ v1_relat_1(B_75)
      | ~ v2_wellord1(B_75)
      | ~ v1_relat_1(B_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_4])).

tff(c_67,plain,(
    ! [C_92,A_93,D_94,B_95] :
      ( k9_relat_1(C_92,k1_wellord1(A_93,D_94)) = k1_wellord1(B_95,'#skF_1'(A_93,B_95,C_92,D_94))
      | ~ r2_hidden(D_94,k3_relat_1(A_93))
      | ~ r3_wellord1(A_93,B_95,C_92)
      | ~ v1_funct_1(C_92)
      | ~ v1_relat_1(C_92)
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_73,plain,(
    ! [C_92,B_95] :
      ( k9_relat_1(C_92,k1_wellord1('#skF_2','#skF_5')) = k1_wellord1(B_95,'#skF_1'('#skF_2',B_95,C_92,'#skF_5'))
      | ~ r3_wellord1('#skF_2',B_95,C_92)
      | ~ v1_funct_1(C_92)
      | ~ v1_relat_1(C_92)
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_67])).

tff(c_78,plain,(
    ! [C_96,B_97] :
      ( k9_relat_1(C_96,k1_wellord1('#skF_2','#skF_5')) = k1_wellord1(B_97,'#skF_1'('#skF_2',B_97,C_96,'#skF_5'))
      | ~ r3_wellord1('#skF_2',B_97,C_96)
      | ~ v1_funct_1(C_96)
      | ~ v1_relat_1(C_96)
      | ~ v1_relat_1(B_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_73])).

tff(c_8,plain,(
    ! [B_6,A_5,C_10,D_12] :
      ( r4_wellord1(k2_wellord1(B_6,A_5),k2_wellord1(C_10,k9_relat_1(D_12,A_5)))
      | ~ r3_wellord1(B_6,C_10,D_12)
      | ~ r1_tarski(A_5,k3_relat_1(B_6))
      | ~ v2_wellord1(B_6)
      | ~ v1_funct_1(D_12)
      | ~ v1_relat_1(D_12)
      | ~ v1_relat_1(C_10)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2695,plain,(
    ! [B_249,C_250,B_251,C_252] :
      ( r4_wellord1(k2_wellord1(B_249,k1_wellord1('#skF_2','#skF_5')),k2_wellord1(C_250,k1_wellord1(B_251,'#skF_1'('#skF_2',B_251,C_252,'#skF_5'))))
      | ~ r3_wellord1(B_249,C_250,C_252)
      | ~ r1_tarski(k1_wellord1('#skF_2','#skF_5'),k3_relat_1(B_249))
      | ~ v2_wellord1(B_249)
      | ~ v1_funct_1(C_252)
      | ~ v1_relat_1(C_252)
      | ~ v1_relat_1(C_250)
      | ~ v1_relat_1(B_249)
      | ~ r3_wellord1('#skF_2',B_251,C_252)
      | ~ v1_funct_1(C_252)
      | ~ v1_relat_1(C_252)
      | ~ v1_relat_1(B_251) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_8])).

tff(c_16,plain,(
    ! [E_69] :
      ( ~ r4_wellord1(k2_wellord1('#skF_2',k1_wellord1('#skF_2','#skF_5')),k2_wellord1('#skF_3',k1_wellord1('#skF_3',E_69)))
      | ~ r2_hidden(E_69,k3_relat_1('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2703,plain,(
    ! [C_252] :
      ( ~ r2_hidden('#skF_1'('#skF_2','#skF_3',C_252,'#skF_5'),k3_relat_1('#skF_3'))
      | ~ r1_tarski(k1_wellord1('#skF_2','#skF_5'),k3_relat_1('#skF_2'))
      | ~ v2_wellord1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ r3_wellord1('#skF_2','#skF_3',C_252)
      | ~ v1_funct_1(C_252)
      | ~ v1_relat_1(C_252)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2695,c_16])).

tff(c_2724,plain,(
    ! [C_252] :
      ( ~ r2_hidden('#skF_1'('#skF_2','#skF_3',C_252,'#skF_5'),k3_relat_1('#skF_3'))
      | ~ r1_tarski(k1_wellord1('#skF_2','#skF_5'),k3_relat_1('#skF_2'))
      | ~ r3_wellord1('#skF_2','#skF_3',C_252)
      | ~ v1_funct_1(C_252)
      | ~ v1_relat_1(C_252) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_22,c_2703])).

tff(c_2725,plain,(
    ~ r1_tarski(k1_wellord1('#skF_2','#skF_5'),k3_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2724])).

tff(c_2728,plain,
    ( ~ v2_wellord1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_2725])).

tff(c_2732,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_22,c_2728])).

tff(c_2735,plain,(
    ! [C_253] :
      ( ~ r2_hidden('#skF_1'('#skF_2','#skF_3',C_253,'#skF_5'),k3_relat_1('#skF_3'))
      | ~ r3_wellord1('#skF_2','#skF_3',C_253)
      | ~ v1_funct_1(C_253)
      | ~ v1_relat_1(C_253) ) ),
    inference(splitRight,[status(thm)],[c_2724])).

tff(c_2739,plain,(
    ! [C_37] :
      ( ~ r2_hidden('#skF_5',k3_relat_1('#skF_2'))
      | ~ r3_wellord1('#skF_2','#skF_3',C_37)
      | ~ v1_funct_1(C_37)
      | ~ v1_relat_1(C_37)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14,c_2735])).

tff(c_2743,plain,(
    ! [C_254] :
      ( ~ r3_wellord1('#skF_2','#skF_3',C_254)
      | ~ v1_funct_1(C_254)
      | ~ v1_relat_1(C_254) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_18,c_2739])).

tff(c_2746,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_2743])).

tff(c_2750,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_2746])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:46:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.41/2.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.41/2.04  
% 5.41/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.41/2.04  %$ r3_wellord1 > r4_wellord1 > r2_hidden > r1_tarski > v2_wellord1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.41/2.04  
% 5.41/2.04  %Foreground sorts:
% 5.41/2.04  
% 5.41/2.04  
% 5.41/2.04  %Background operators:
% 5.41/2.04  
% 5.41/2.04  
% 5.41/2.04  %Foreground operators:
% 5.41/2.04  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.41/2.04  tff(r4_wellord1, type, r4_wellord1: ($i * $i) > $o).
% 5.41/2.04  tff(r3_wellord1, type, r3_wellord1: ($i * $i * $i) > $o).
% 5.41/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.41/2.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.41/2.04  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.41/2.04  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 5.41/2.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.41/2.04  tff('#skF_5', type, '#skF_5': $i).
% 5.41/2.04  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 5.41/2.04  tff('#skF_2', type, '#skF_2': $i).
% 5.41/2.04  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.41/2.04  tff('#skF_3', type, '#skF_3': $i).
% 5.41/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.41/2.04  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.41/2.04  tff('#skF_4', type, '#skF_4': $i).
% 5.41/2.04  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 5.41/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.41/2.04  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 5.41/2.04  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 5.41/2.04  
% 5.41/2.05  tff(f_104, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((v2_wellord1(A) & r3_wellord1(A, B, C)) => (![D]: ~(r2_hidden(D, k3_relat_1(A)) & (![E]: ~(r2_hidden(E, k3_relat_1(B)) & r4_wellord1(k2_wellord1(A, k1_wellord1(A, D)), k2_wellord1(B, k1_wellord1(B, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_wellord1)).
% 5.41/2.05  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r3_wellord1(A, B, C) => (![D]: ~(r2_hidden(D, k3_relat_1(A)) & (![E]: ~(r2_hidden(E, k3_relat_1(B)) & (k9_relat_1(C, k1_wellord1(A, D)) = k1_wellord1(B, E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_wellord1)).
% 5.41/2.05  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v2_wellord1(B) => (k3_relat_1(k2_wellord1(B, k1_wellord1(B, A))) = k1_wellord1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_wellord1)).
% 5.41/2.05  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k3_relat_1(k2_wellord1(B, A)), k3_relat_1(B)) & r1_tarski(k3_relat_1(k2_wellord1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_wellord1)).
% 5.41/2.05  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (![D]: ((v1_relat_1(D) & v1_funct_1(D)) => (((v2_wellord1(B) & r1_tarski(A, k3_relat_1(B))) & r3_wellord1(B, C, D)) => (r3_wellord1(k2_wellord1(B, A), k2_wellord1(C, k9_relat_1(D, A)), k7_relat_1(D, A)) & r4_wellord1(k2_wellord1(B, A), k2_wellord1(C, k9_relat_1(D, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_wellord1)).
% 5.41/2.05  tff(c_26, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.41/2.05  tff(c_24, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.41/2.05  tff(c_20, plain, (r3_wellord1('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.41/2.05  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.41/2.05  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.41/2.05  tff(c_18, plain, (r2_hidden('#skF_5', k3_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.41/2.05  tff(c_14, plain, (![A_13, B_29, C_37, D_41]: (r2_hidden('#skF_1'(A_13, B_29, C_37, D_41), k3_relat_1(B_29)) | ~r2_hidden(D_41, k3_relat_1(A_13)) | ~r3_wellord1(A_13, B_29, C_37) | ~v1_funct_1(C_37) | ~v1_relat_1(C_37) | ~v1_relat_1(B_29) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.41/2.05  tff(c_22, plain, (v2_wellord1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.41/2.05  tff(c_34, plain, (![B_75, A_76]: (k3_relat_1(k2_wellord1(B_75, k1_wellord1(B_75, A_76)))=k1_wellord1(B_75, A_76) | ~v2_wellord1(B_75) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.41/2.05  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k3_relat_1(k2_wellord1(B_2, A_1)), k3_relat_1(B_2)) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.41/2.05  tff(c_40, plain, (![B_75, A_76]: (r1_tarski(k1_wellord1(B_75, A_76), k3_relat_1(B_75)) | ~v1_relat_1(B_75) | ~v2_wellord1(B_75) | ~v1_relat_1(B_75))), inference(superposition, [status(thm), theory('equality')], [c_34, c_4])).
% 5.41/2.05  tff(c_67, plain, (![C_92, A_93, D_94, B_95]: (k9_relat_1(C_92, k1_wellord1(A_93, D_94))=k1_wellord1(B_95, '#skF_1'(A_93, B_95, C_92, D_94)) | ~r2_hidden(D_94, k3_relat_1(A_93)) | ~r3_wellord1(A_93, B_95, C_92) | ~v1_funct_1(C_92) | ~v1_relat_1(C_92) | ~v1_relat_1(B_95) | ~v1_relat_1(A_93))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.41/2.05  tff(c_73, plain, (![C_92, B_95]: (k9_relat_1(C_92, k1_wellord1('#skF_2', '#skF_5'))=k1_wellord1(B_95, '#skF_1'('#skF_2', B_95, C_92, '#skF_5')) | ~r3_wellord1('#skF_2', B_95, C_92) | ~v1_funct_1(C_92) | ~v1_relat_1(C_92) | ~v1_relat_1(B_95) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_18, c_67])).
% 5.41/2.05  tff(c_78, plain, (![C_96, B_97]: (k9_relat_1(C_96, k1_wellord1('#skF_2', '#skF_5'))=k1_wellord1(B_97, '#skF_1'('#skF_2', B_97, C_96, '#skF_5')) | ~r3_wellord1('#skF_2', B_97, C_96) | ~v1_funct_1(C_96) | ~v1_relat_1(C_96) | ~v1_relat_1(B_97))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_73])).
% 5.41/2.05  tff(c_8, plain, (![B_6, A_5, C_10, D_12]: (r4_wellord1(k2_wellord1(B_6, A_5), k2_wellord1(C_10, k9_relat_1(D_12, A_5))) | ~r3_wellord1(B_6, C_10, D_12) | ~r1_tarski(A_5, k3_relat_1(B_6)) | ~v2_wellord1(B_6) | ~v1_funct_1(D_12) | ~v1_relat_1(D_12) | ~v1_relat_1(C_10) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.41/2.05  tff(c_2695, plain, (![B_249, C_250, B_251, C_252]: (r4_wellord1(k2_wellord1(B_249, k1_wellord1('#skF_2', '#skF_5')), k2_wellord1(C_250, k1_wellord1(B_251, '#skF_1'('#skF_2', B_251, C_252, '#skF_5')))) | ~r3_wellord1(B_249, C_250, C_252) | ~r1_tarski(k1_wellord1('#skF_2', '#skF_5'), k3_relat_1(B_249)) | ~v2_wellord1(B_249) | ~v1_funct_1(C_252) | ~v1_relat_1(C_252) | ~v1_relat_1(C_250) | ~v1_relat_1(B_249) | ~r3_wellord1('#skF_2', B_251, C_252) | ~v1_funct_1(C_252) | ~v1_relat_1(C_252) | ~v1_relat_1(B_251))), inference(superposition, [status(thm), theory('equality')], [c_78, c_8])).
% 5.41/2.05  tff(c_16, plain, (![E_69]: (~r4_wellord1(k2_wellord1('#skF_2', k1_wellord1('#skF_2', '#skF_5')), k2_wellord1('#skF_3', k1_wellord1('#skF_3', E_69))) | ~r2_hidden(E_69, k3_relat_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.41/2.05  tff(c_2703, plain, (![C_252]: (~r2_hidden('#skF_1'('#skF_2', '#skF_3', C_252, '#skF_5'), k3_relat_1('#skF_3')) | ~r1_tarski(k1_wellord1('#skF_2', '#skF_5'), k3_relat_1('#skF_2')) | ~v2_wellord1('#skF_2') | ~v1_relat_1('#skF_2') | ~r3_wellord1('#skF_2', '#skF_3', C_252) | ~v1_funct_1(C_252) | ~v1_relat_1(C_252) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_2695, c_16])).
% 5.41/2.05  tff(c_2724, plain, (![C_252]: (~r2_hidden('#skF_1'('#skF_2', '#skF_3', C_252, '#skF_5'), k3_relat_1('#skF_3')) | ~r1_tarski(k1_wellord1('#skF_2', '#skF_5'), k3_relat_1('#skF_2')) | ~r3_wellord1('#skF_2', '#skF_3', C_252) | ~v1_funct_1(C_252) | ~v1_relat_1(C_252))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_22, c_2703])).
% 5.41/2.05  tff(c_2725, plain, (~r1_tarski(k1_wellord1('#skF_2', '#skF_5'), k3_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_2724])).
% 5.41/2.05  tff(c_2728, plain, (~v2_wellord1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_40, c_2725])).
% 5.41/2.05  tff(c_2732, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_22, c_2728])).
% 5.41/2.05  tff(c_2735, plain, (![C_253]: (~r2_hidden('#skF_1'('#skF_2', '#skF_3', C_253, '#skF_5'), k3_relat_1('#skF_3')) | ~r3_wellord1('#skF_2', '#skF_3', C_253) | ~v1_funct_1(C_253) | ~v1_relat_1(C_253))), inference(splitRight, [status(thm)], [c_2724])).
% 5.41/2.05  tff(c_2739, plain, (![C_37]: (~r2_hidden('#skF_5', k3_relat_1('#skF_2')) | ~r3_wellord1('#skF_2', '#skF_3', C_37) | ~v1_funct_1(C_37) | ~v1_relat_1(C_37) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_14, c_2735])).
% 5.41/2.05  tff(c_2743, plain, (![C_254]: (~r3_wellord1('#skF_2', '#skF_3', C_254) | ~v1_funct_1(C_254) | ~v1_relat_1(C_254))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_18, c_2739])).
% 5.41/2.05  tff(c_2746, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_2743])).
% 5.41/2.05  tff(c_2750, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_2746])).
% 5.41/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.41/2.05  
% 5.41/2.05  Inference rules
% 5.41/2.05  ----------------------
% 5.41/2.05  #Ref     : 0
% 5.41/2.05  #Sup     : 720
% 5.41/2.05  #Fact    : 0
% 5.41/2.05  #Define  : 0
% 5.41/2.05  #Split   : 4
% 5.41/2.05  #Chain   : 0
% 5.41/2.05  #Close   : 0
% 5.41/2.05  
% 5.41/2.05  Ordering : KBO
% 5.41/2.05  
% 5.41/2.05  Simplification rules
% 5.41/2.05  ----------------------
% 5.41/2.05  #Subsume      : 191
% 5.41/2.05  #Demod        : 394
% 5.41/2.05  #Tautology    : 34
% 5.41/2.05  #SimpNegUnit  : 0
% 5.41/2.05  #BackRed      : 0
% 5.41/2.05  
% 5.41/2.05  #Partial instantiations: 0
% 5.41/2.05  #Strategies tried      : 1
% 5.41/2.05  
% 5.41/2.05  Timing (in seconds)
% 5.41/2.05  ----------------------
% 5.41/2.05  Preprocessing        : 0.32
% 5.41/2.06  Parsing              : 0.18
% 5.41/2.06  CNF conversion       : 0.02
% 5.41/2.06  Main loop            : 0.94
% 5.41/2.06  Inferencing          : 0.37
% 5.41/2.06  Reduction            : 0.25
% 5.41/2.06  Demodulation         : 0.19
% 5.41/2.06  BG Simplification    : 0.05
% 5.41/2.06  Subsumption          : 0.22
% 5.41/2.06  Abstraction          : 0.06
% 5.41/2.06  MUC search           : 0.00
% 5.41/2.06  Cooper               : 0.00
% 5.41/2.06  Total                : 1.29
% 5.41/2.06  Index Insertion      : 0.00
% 5.41/2.06  Index Deletion       : 0.00
% 5.41/2.06  Index Matching       : 0.00
% 5.41/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
