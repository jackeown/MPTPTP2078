%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:56 EST 2020

% Result     : Theorem 11.91s
% Output     : CNFRefutation 11.91s
% Verified   : 
% Statistics : Number of formulae       :   55 (  67 expanded)
%              Number of leaves         :   26 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :  116 ( 152 expanded)
%              Number of equality atoms :   13 (  21 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_5 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_44,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_42,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_32,plain,(
    ! [A_50,B_51] :
      ( v1_relat_1(k5_relat_1(A_50,B_51))
      | ~ v1_relat_1(B_51)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_36,plain,(
    ! [A_54] :
      ( k10_relat_1(A_54,k2_relat_1(A_54)) = k1_relat_1(A_54)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_99,plain,(
    ! [B_80,C_81,A_82] :
      ( k10_relat_1(k5_relat_1(B_80,C_81),A_82) = k10_relat_1(B_80,k10_relat_1(C_81,A_82))
      | ~ v1_relat_1(C_81)
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_119,plain,(
    ! [B_80,C_81] :
      ( k10_relat_1(B_80,k10_relat_1(C_81,k2_relat_1(k5_relat_1(B_80,C_81)))) = k1_relat_1(k5_relat_1(B_80,C_81))
      | ~ v1_relat_1(C_81)
      | ~ v1_relat_1(B_80)
      | ~ v1_relat_1(k5_relat_1(B_80,C_81)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_99])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_34,plain,(
    ! [B_53,A_52] :
      ( r1_tarski(k10_relat_1(B_53,A_52),k1_relat_1(B_53))
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    ! [D_46,A_8,B_31] :
      ( r2_hidden(k4_tarski(D_46,'#skF_5'(A_8,B_31,k10_relat_1(A_8,B_31),D_46)),A_8)
      | ~ r2_hidden(D_46,k10_relat_1(A_8,B_31))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_136,plain,(
    ! [A_91,B_92,D_93] :
      ( r2_hidden('#skF_5'(A_91,B_92,k10_relat_1(A_91,B_92),D_93),B_92)
      | ~ r2_hidden(D_93,k10_relat_1(A_91,B_92))
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_365,plain,(
    ! [A_143,B_144,D_145,B_146] :
      ( r2_hidden('#skF_5'(A_143,B_144,k10_relat_1(A_143,B_144),D_145),B_146)
      | ~ r1_tarski(B_144,B_146)
      | ~ r2_hidden(D_145,k10_relat_1(A_143,B_144))
      | ~ v1_relat_1(A_143) ) ),
    inference(resolution,[status(thm)],[c_136,c_2])).

tff(c_14,plain,(
    ! [D_46,A_8,B_31,E_49] :
      ( r2_hidden(D_46,k10_relat_1(A_8,B_31))
      | ~ r2_hidden(E_49,B_31)
      | ~ r2_hidden(k4_tarski(D_46,E_49),A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14209,plain,(
    ! [A_7691,D_7690,B_7689,D_7693,A_7688,B_7692] :
      ( r2_hidden(D_7690,k10_relat_1(A_7691,B_7692))
      | ~ r2_hidden(k4_tarski(D_7690,'#skF_5'(A_7688,B_7689,k10_relat_1(A_7688,B_7689),D_7693)),A_7691)
      | ~ v1_relat_1(A_7691)
      | ~ r1_tarski(B_7689,B_7692)
      | ~ r2_hidden(D_7693,k10_relat_1(A_7688,B_7689))
      | ~ v1_relat_1(A_7688) ) ),
    inference(resolution,[status(thm)],[c_365,c_14])).

tff(c_14245,plain,(
    ! [D_7717,A_7718,B_7719,B_7720] :
      ( r2_hidden(D_7717,k10_relat_1(A_7718,B_7719))
      | ~ r1_tarski(B_7720,B_7719)
      | ~ r2_hidden(D_7717,k10_relat_1(A_7718,B_7720))
      | ~ v1_relat_1(A_7718) ) ),
    inference(resolution,[status(thm)],[c_18,c_14209])).

tff(c_14303,plain,(
    ! [D_7744,A_7745,B_7746,A_7747] :
      ( r2_hidden(D_7744,k10_relat_1(A_7745,k1_relat_1(B_7746)))
      | ~ r2_hidden(D_7744,k10_relat_1(A_7745,k10_relat_1(B_7746,A_7747)))
      | ~ v1_relat_1(A_7745)
      | ~ v1_relat_1(B_7746) ) ),
    inference(resolution,[status(thm)],[c_34,c_14245])).

tff(c_15138,plain,(
    ! [A_7883,B_7884,A_7885,B_7886] :
      ( r2_hidden('#skF_1'(k10_relat_1(A_7883,k10_relat_1(B_7884,A_7885)),B_7886),k10_relat_1(A_7883,k1_relat_1(B_7884)))
      | ~ v1_relat_1(A_7883)
      | ~ v1_relat_1(B_7884)
      | r1_tarski(k10_relat_1(A_7883,k10_relat_1(B_7884,A_7885)),B_7886) ) ),
    inference(resolution,[status(thm)],[c_6,c_14303])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_15306,plain,(
    ! [A_7910,B_7911,A_7912] :
      ( ~ v1_relat_1(A_7910)
      | ~ v1_relat_1(B_7911)
      | r1_tarski(k10_relat_1(A_7910,k10_relat_1(B_7911,A_7912)),k10_relat_1(A_7910,k1_relat_1(B_7911))) ) ),
    inference(resolution,[status(thm)],[c_15138,c_4])).

tff(c_15619,plain,(
    ! [B_7964,C_7965] :
      ( ~ v1_relat_1(B_7964)
      | ~ v1_relat_1(C_7965)
      | r1_tarski(k1_relat_1(k5_relat_1(B_7964,C_7965)),k10_relat_1(B_7964,k1_relat_1(C_7965)))
      | ~ v1_relat_1(C_7965)
      | ~ v1_relat_1(B_7964)
      | ~ v1_relat_1(k5_relat_1(B_7964,C_7965)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_15306])).

tff(c_223,plain,(
    ! [B_116,C_117,A_118] :
      ( r1_tarski(k10_relat_1(B_116,k10_relat_1(C_117,A_118)),k1_relat_1(k5_relat_1(B_116,C_117)))
      | ~ v1_relat_1(k5_relat_1(B_116,C_117))
      | ~ v1_relat_1(C_117)
      | ~ v1_relat_1(B_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_34])).

tff(c_378,plain,(
    ! [B_147,A_148] :
      ( r1_tarski(k10_relat_1(B_147,k1_relat_1(A_148)),k1_relat_1(k5_relat_1(B_147,A_148)))
      | ~ v1_relat_1(k5_relat_1(B_147,A_148))
      | ~ v1_relat_1(A_148)
      | ~ v1_relat_1(B_147)
      | ~ v1_relat_1(A_148) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_223])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_391,plain,(
    ! [B_147,A_148] :
      ( k10_relat_1(B_147,k1_relat_1(A_148)) = k1_relat_1(k5_relat_1(B_147,A_148))
      | ~ r1_tarski(k1_relat_1(k5_relat_1(B_147,A_148)),k10_relat_1(B_147,k1_relat_1(A_148)))
      | ~ v1_relat_1(k5_relat_1(B_147,A_148))
      | ~ v1_relat_1(B_147)
      | ~ v1_relat_1(A_148) ) ),
    inference(resolution,[status(thm)],[c_378,c_8])).

tff(c_15822,plain,(
    ! [B_7989,C_7990] :
      ( k10_relat_1(B_7989,k1_relat_1(C_7990)) = k1_relat_1(k5_relat_1(B_7989,C_7990))
      | ~ v1_relat_1(C_7990)
      | ~ v1_relat_1(B_7989)
      | ~ v1_relat_1(k5_relat_1(B_7989,C_7990)) ) ),
    inference(resolution,[status(thm)],[c_15619,c_391])).

tff(c_15842,plain,(
    ! [A_8014,B_8015] :
      ( k10_relat_1(A_8014,k1_relat_1(B_8015)) = k1_relat_1(k5_relat_1(A_8014,B_8015))
      | ~ v1_relat_1(B_8015)
      | ~ v1_relat_1(A_8014) ) ),
    inference(resolution,[status(thm)],[c_32,c_15822])).

tff(c_40,plain,(
    k10_relat_1('#skF_6',k1_relat_1('#skF_7')) != k1_relat_1(k5_relat_1('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_16094,plain,
    ( ~ v1_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_15842,c_40])).

tff(c_16133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_16094])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:33:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.91/4.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.91/4.71  
% 11.91/4.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.91/4.71  %$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_5 > #skF_3 > #skF_1
% 11.91/4.71  
% 11.91/4.71  %Foreground sorts:
% 11.91/4.71  
% 11.91/4.71  
% 11.91/4.71  %Background operators:
% 11.91/4.71  
% 11.91/4.71  
% 11.91/4.71  %Foreground operators:
% 11.91/4.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.91/4.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.91/4.71  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 11.91/4.71  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 11.91/4.71  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 11.91/4.71  tff('#skF_7', type, '#skF_7': $i).
% 11.91/4.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.91/4.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.91/4.71  tff('#skF_6', type, '#skF_6': $i).
% 11.91/4.71  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.91/4.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.91/4.71  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 11.91/4.71  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 11.91/4.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.91/4.71  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 11.91/4.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.91/4.71  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.91/4.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.91/4.71  
% 11.91/4.72  tff(f_80, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 11.91/4.72  tff(f_57, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 11.91/4.72  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 11.91/4.72  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t181_relat_1)).
% 11.91/4.72  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 11.91/4.72  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 11.91/4.72  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 11.91/4.72  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.91/4.72  tff(c_44, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.91/4.72  tff(c_42, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.91/4.72  tff(c_32, plain, (![A_50, B_51]: (v1_relat_1(k5_relat_1(A_50, B_51)) | ~v1_relat_1(B_51) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.91/4.72  tff(c_36, plain, (![A_54]: (k10_relat_1(A_54, k2_relat_1(A_54))=k1_relat_1(A_54) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.91/4.72  tff(c_99, plain, (![B_80, C_81, A_82]: (k10_relat_1(k5_relat_1(B_80, C_81), A_82)=k10_relat_1(B_80, k10_relat_1(C_81, A_82)) | ~v1_relat_1(C_81) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.91/4.72  tff(c_119, plain, (![B_80, C_81]: (k10_relat_1(B_80, k10_relat_1(C_81, k2_relat_1(k5_relat_1(B_80, C_81))))=k1_relat_1(k5_relat_1(B_80, C_81)) | ~v1_relat_1(C_81) | ~v1_relat_1(B_80) | ~v1_relat_1(k5_relat_1(B_80, C_81)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_99])).
% 11.91/4.72  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.91/4.72  tff(c_34, plain, (![B_53, A_52]: (r1_tarski(k10_relat_1(B_53, A_52), k1_relat_1(B_53)) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.91/4.72  tff(c_18, plain, (![D_46, A_8, B_31]: (r2_hidden(k4_tarski(D_46, '#skF_5'(A_8, B_31, k10_relat_1(A_8, B_31), D_46)), A_8) | ~r2_hidden(D_46, k10_relat_1(A_8, B_31)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.91/4.72  tff(c_136, plain, (![A_91, B_92, D_93]: (r2_hidden('#skF_5'(A_91, B_92, k10_relat_1(A_91, B_92), D_93), B_92) | ~r2_hidden(D_93, k10_relat_1(A_91, B_92)) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.91/4.72  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.91/4.72  tff(c_365, plain, (![A_143, B_144, D_145, B_146]: (r2_hidden('#skF_5'(A_143, B_144, k10_relat_1(A_143, B_144), D_145), B_146) | ~r1_tarski(B_144, B_146) | ~r2_hidden(D_145, k10_relat_1(A_143, B_144)) | ~v1_relat_1(A_143))), inference(resolution, [status(thm)], [c_136, c_2])).
% 11.91/4.72  tff(c_14, plain, (![D_46, A_8, B_31, E_49]: (r2_hidden(D_46, k10_relat_1(A_8, B_31)) | ~r2_hidden(E_49, B_31) | ~r2_hidden(k4_tarski(D_46, E_49), A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.91/4.72  tff(c_14209, plain, (![A_7691, D_7690, B_7689, D_7693, A_7688, B_7692]: (r2_hidden(D_7690, k10_relat_1(A_7691, B_7692)) | ~r2_hidden(k4_tarski(D_7690, '#skF_5'(A_7688, B_7689, k10_relat_1(A_7688, B_7689), D_7693)), A_7691) | ~v1_relat_1(A_7691) | ~r1_tarski(B_7689, B_7692) | ~r2_hidden(D_7693, k10_relat_1(A_7688, B_7689)) | ~v1_relat_1(A_7688))), inference(resolution, [status(thm)], [c_365, c_14])).
% 11.91/4.72  tff(c_14245, plain, (![D_7717, A_7718, B_7719, B_7720]: (r2_hidden(D_7717, k10_relat_1(A_7718, B_7719)) | ~r1_tarski(B_7720, B_7719) | ~r2_hidden(D_7717, k10_relat_1(A_7718, B_7720)) | ~v1_relat_1(A_7718))), inference(resolution, [status(thm)], [c_18, c_14209])).
% 11.91/4.72  tff(c_14303, plain, (![D_7744, A_7745, B_7746, A_7747]: (r2_hidden(D_7744, k10_relat_1(A_7745, k1_relat_1(B_7746))) | ~r2_hidden(D_7744, k10_relat_1(A_7745, k10_relat_1(B_7746, A_7747))) | ~v1_relat_1(A_7745) | ~v1_relat_1(B_7746))), inference(resolution, [status(thm)], [c_34, c_14245])).
% 11.91/4.72  tff(c_15138, plain, (![A_7883, B_7884, A_7885, B_7886]: (r2_hidden('#skF_1'(k10_relat_1(A_7883, k10_relat_1(B_7884, A_7885)), B_7886), k10_relat_1(A_7883, k1_relat_1(B_7884))) | ~v1_relat_1(A_7883) | ~v1_relat_1(B_7884) | r1_tarski(k10_relat_1(A_7883, k10_relat_1(B_7884, A_7885)), B_7886))), inference(resolution, [status(thm)], [c_6, c_14303])).
% 11.91/4.72  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.91/4.72  tff(c_15306, plain, (![A_7910, B_7911, A_7912]: (~v1_relat_1(A_7910) | ~v1_relat_1(B_7911) | r1_tarski(k10_relat_1(A_7910, k10_relat_1(B_7911, A_7912)), k10_relat_1(A_7910, k1_relat_1(B_7911))))), inference(resolution, [status(thm)], [c_15138, c_4])).
% 11.91/4.72  tff(c_15619, plain, (![B_7964, C_7965]: (~v1_relat_1(B_7964) | ~v1_relat_1(C_7965) | r1_tarski(k1_relat_1(k5_relat_1(B_7964, C_7965)), k10_relat_1(B_7964, k1_relat_1(C_7965))) | ~v1_relat_1(C_7965) | ~v1_relat_1(B_7964) | ~v1_relat_1(k5_relat_1(B_7964, C_7965)))), inference(superposition, [status(thm), theory('equality')], [c_119, c_15306])).
% 11.91/4.72  tff(c_223, plain, (![B_116, C_117, A_118]: (r1_tarski(k10_relat_1(B_116, k10_relat_1(C_117, A_118)), k1_relat_1(k5_relat_1(B_116, C_117))) | ~v1_relat_1(k5_relat_1(B_116, C_117)) | ~v1_relat_1(C_117) | ~v1_relat_1(B_116))), inference(superposition, [status(thm), theory('equality')], [c_99, c_34])).
% 11.91/4.72  tff(c_378, plain, (![B_147, A_148]: (r1_tarski(k10_relat_1(B_147, k1_relat_1(A_148)), k1_relat_1(k5_relat_1(B_147, A_148))) | ~v1_relat_1(k5_relat_1(B_147, A_148)) | ~v1_relat_1(A_148) | ~v1_relat_1(B_147) | ~v1_relat_1(A_148))), inference(superposition, [status(thm), theory('equality')], [c_36, c_223])).
% 11.91/4.72  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.91/4.72  tff(c_391, plain, (![B_147, A_148]: (k10_relat_1(B_147, k1_relat_1(A_148))=k1_relat_1(k5_relat_1(B_147, A_148)) | ~r1_tarski(k1_relat_1(k5_relat_1(B_147, A_148)), k10_relat_1(B_147, k1_relat_1(A_148))) | ~v1_relat_1(k5_relat_1(B_147, A_148)) | ~v1_relat_1(B_147) | ~v1_relat_1(A_148))), inference(resolution, [status(thm)], [c_378, c_8])).
% 11.91/4.72  tff(c_15822, plain, (![B_7989, C_7990]: (k10_relat_1(B_7989, k1_relat_1(C_7990))=k1_relat_1(k5_relat_1(B_7989, C_7990)) | ~v1_relat_1(C_7990) | ~v1_relat_1(B_7989) | ~v1_relat_1(k5_relat_1(B_7989, C_7990)))), inference(resolution, [status(thm)], [c_15619, c_391])).
% 11.91/4.72  tff(c_15842, plain, (![A_8014, B_8015]: (k10_relat_1(A_8014, k1_relat_1(B_8015))=k1_relat_1(k5_relat_1(A_8014, B_8015)) | ~v1_relat_1(B_8015) | ~v1_relat_1(A_8014))), inference(resolution, [status(thm)], [c_32, c_15822])).
% 11.91/4.72  tff(c_40, plain, (k10_relat_1('#skF_6', k1_relat_1('#skF_7'))!=k1_relat_1(k5_relat_1('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.91/4.72  tff(c_16094, plain, (~v1_relat_1('#skF_7') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_15842, c_40])).
% 11.91/4.72  tff(c_16133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_16094])).
% 11.91/4.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.91/4.72  
% 11.91/4.72  Inference rules
% 11.91/4.72  ----------------------
% 11.91/4.72  #Ref     : 0
% 11.91/4.72  #Sup     : 3424
% 11.91/4.72  #Fact    : 10
% 11.91/4.72  #Define  : 0
% 11.91/4.72  #Split   : 0
% 11.91/4.72  #Chain   : 0
% 11.91/4.72  #Close   : 0
% 11.91/4.72  
% 11.91/4.72  Ordering : KBO
% 11.91/4.72  
% 11.91/4.72  Simplification rules
% 11.91/4.72  ----------------------
% 11.91/4.72  #Subsume      : 241
% 11.91/4.72  #Demod        : 26
% 11.91/4.72  #Tautology    : 79
% 11.91/4.72  #SimpNegUnit  : 0
% 11.91/4.72  #BackRed      : 0
% 11.91/4.72  
% 11.91/4.72  #Partial instantiations: 3732
% 11.91/4.72  #Strategies tried      : 1
% 11.91/4.72  
% 11.91/4.72  Timing (in seconds)
% 11.91/4.72  ----------------------
% 11.91/4.72  Preprocessing        : 0.32
% 11.91/4.72  Parsing              : 0.16
% 11.91/4.72  CNF conversion       : 0.03
% 11.91/4.72  Main loop            : 3.64
% 11.91/4.72  Inferencing          : 0.85
% 11.91/4.72  Reduction            : 0.51
% 11.91/4.72  Demodulation         : 0.33
% 11.91/4.72  BG Simplification    : 0.11
% 11.91/4.72  Subsumption          : 1.98
% 11.91/4.72  Abstraction          : 0.13
% 11.91/4.72  MUC search           : 0.00
% 11.91/4.73  Cooper               : 0.00
% 11.91/4.73  Total                : 3.99
% 11.91/4.73  Index Insertion      : 0.00
% 11.91/4.73  Index Deletion       : 0.00
% 11.91/4.73  Index Matching       : 0.00
% 11.91/4.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
