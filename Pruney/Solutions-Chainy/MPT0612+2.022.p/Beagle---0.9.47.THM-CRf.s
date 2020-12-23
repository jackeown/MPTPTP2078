%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:44 EST 2020

% Result     : Theorem 4.10s
% Output     : CNFRefutation 4.52s
% Verified   : 
% Statistics : Number of formulae       :   75 (  84 expanded)
%              Number of leaves         :   38 (  44 expanded)
%              Depth                    :   14
%              Number of atoms          :   90 ( 103 expanded)
%              Number of equality atoms :   29 (  36 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_65,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_55,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_41,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(A,C)
        & r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_22,plain,(
    ! [A_21,B_22] : r1_xboole_0(k4_xboole_0(A_21,B_22),B_22) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_18,plain,(
    ! [A_18] : r1_xboole_0(A_18,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    ! [A_16,B_17] : r1_tarski(k4_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_38,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_86,plain,(
    ! [A_55,B_56] :
      ( k3_xboole_0(A_55,B_56) = A_55
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_98,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_86])).

tff(c_10,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_114,plain,(
    k5_xboole_0('#skF_3','#skF_3') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_10])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_99,plain,(
    ! [A_57,B_58] : k5_xboole_0(A_57,k3_xboole_0(A_57,B_58)) = k4_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_108,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_99])).

tff(c_142,plain,(
    k4_xboole_0('#skF_3','#skF_3') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_108])).

tff(c_155,plain,(
    r1_xboole_0(k4_xboole_0('#skF_3','#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_22])).

tff(c_161,plain,(
    ! [B_62,A_63] :
      ( ~ r1_xboole_0(B_62,A_63)
      | ~ r1_tarski(B_62,A_63)
      | v1_xboole_0(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_164,plain,
    ( ~ r1_tarski(k4_xboole_0('#skF_3','#skF_4'),'#skF_3')
    | v1_xboole_0(k4_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_155,c_161])).

tff(c_173,plain,(
    v1_xboole_0(k4_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_164])).

tff(c_66,plain,(
    ! [A_50] :
      ( r2_hidden('#skF_2'(A_50),A_50)
      | k1_xboole_0 = A_50 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    ! [A_50] :
      ( ~ v1_xboole_0(A_50)
      | k1_xboole_0 = A_50 ) ),
    inference(resolution,[status(thm)],[c_66,c_2])).

tff(c_179,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_173,c_70])).

tff(c_243,plain,(
    ! [A_67,B_68,C_69] :
      ( ~ r1_xboole_0(A_67,k4_xboole_0(B_68,C_69))
      | ~ r1_xboole_0(A_67,C_69)
      | r1_xboole_0(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_249,plain,(
    ! [A_67] :
      ( ~ r1_xboole_0(A_67,k1_xboole_0)
      | ~ r1_xboole_0(A_67,'#skF_4')
      | r1_xboole_0(A_67,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_243])).

tff(c_257,plain,(
    ! [A_67] :
      ( ~ r1_xboole_0(A_67,'#skF_4')
      | r1_xboole_0(A_67,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_249])).

tff(c_24,plain,(
    ! [A_23,B_24] : r1_tarski(A_23,k2_xboole_0(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_28,plain,(
    ! [A_28,B_29] : k6_subset_1(A_28,B_29) = k4_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_34,plain,(
    ! [C_37,A_35,B_36] :
      ( k7_relat_1(C_37,k6_subset_1(A_35,B_36)) = k6_subset_1(C_37,k7_relat_1(C_37,B_36))
      | ~ r1_tarski(k1_relat_1(C_37),A_35)
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_553,plain,(
    ! [C_96,A_97,B_98] :
      ( k7_relat_1(C_96,k4_xboole_0(A_97,B_98)) = k4_xboole_0(C_96,k7_relat_1(C_96,B_98))
      | ~ r1_tarski(k1_relat_1(C_96),A_97)
      | ~ v1_relat_1(C_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_34])).

tff(c_1060,plain,(
    ! [C_148,B_149,B_150] :
      ( k7_relat_1(C_148,k4_xboole_0(k2_xboole_0(k1_relat_1(C_148),B_149),B_150)) = k4_xboole_0(C_148,k7_relat_1(C_148,B_150))
      | ~ v1_relat_1(C_148) ) ),
    inference(resolution,[status(thm)],[c_24,c_553])).

tff(c_32,plain,(
    ! [C_34,A_32,B_33] :
      ( k7_relat_1(k7_relat_1(C_34,A_32),B_33) = k1_xboole_0
      | ~ r1_xboole_0(A_32,B_33)
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2685,plain,(
    ! [C_265,B_266,B_267,B_268] :
      ( k7_relat_1(k4_xboole_0(C_265,k7_relat_1(C_265,B_266)),B_267) = k1_xboole_0
      | ~ r1_xboole_0(k4_xboole_0(k2_xboole_0(k1_relat_1(C_265),B_268),B_266),B_267)
      | ~ v1_relat_1(C_265)
      | ~ v1_relat_1(C_265) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1060,c_32])).

tff(c_3040,plain,(
    ! [C_273,B_274,B_275] :
      ( k7_relat_1(k4_xboole_0(C_273,k7_relat_1(C_273,B_274)),'#skF_3') = k1_xboole_0
      | ~ v1_relat_1(C_273)
      | ~ r1_xboole_0(k4_xboole_0(k2_xboole_0(k1_relat_1(C_273),B_275),B_274),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_257,c_2685])).

tff(c_3401,plain,(
    ! [C_285] :
      ( k7_relat_1(k4_xboole_0(C_285,k7_relat_1(C_285,'#skF_4')),'#skF_3') = k1_xboole_0
      | ~ v1_relat_1(C_285) ) ),
    inference(resolution,[status(thm)],[c_22,c_3040])).

tff(c_36,plain,(
    k7_relat_1(k6_subset_1('#skF_5',k7_relat_1('#skF_5','#skF_4')),'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_42,plain,(
    k7_relat_1(k4_xboole_0('#skF_5',k7_relat_1('#skF_5','#skF_4')),'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_36])).

tff(c_3422,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3401,c_42])).

tff(c_3442,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3422])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.10/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.10/1.78  
% 4.10/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.10/1.78  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 4.10/1.78  
% 4.10/1.78  %Foreground sorts:
% 4.10/1.78  
% 4.10/1.78  
% 4.10/1.78  %Background operators:
% 4.10/1.78  
% 4.10/1.78  
% 4.10/1.78  %Foreground operators:
% 4.10/1.78  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.10/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.10/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.10/1.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.10/1.78  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.10/1.78  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.10/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.10/1.78  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.10/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.10/1.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.10/1.78  tff('#skF_5', type, '#skF_5': $i).
% 4.10/1.78  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.10/1.78  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 4.10/1.78  tff('#skF_3', type, '#skF_3': $i).
% 4.10/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.10/1.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.10/1.78  tff('#skF_4', type, '#skF_4': $i).
% 4.10/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.10/1.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.10/1.78  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.10/1.78  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.10/1.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.10/1.78  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.10/1.78  
% 4.52/1.79  tff(f_98, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t216_relat_1)).
% 4.52/1.79  tff(f_65, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.52/1.79  tff(f_55, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.52/1.79  tff(f_53, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.52/1.79  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.52/1.79  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.52/1.79  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.52/1.79  tff(f_63, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 4.52/1.79  tff(f_41, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.52/1.79  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.52/1.79  tff(f_75, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_xboole_1)).
% 4.52/1.79  tff(f_67, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.52/1.79  tff(f_77, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 4.52/1.79  tff(f_91, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t211_relat_1)).
% 4.52/1.79  tff(f_85, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 4.52/1.79  tff(c_40, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.52/1.79  tff(c_22, plain, (![A_21, B_22]: (r1_xboole_0(k4_xboole_0(A_21, B_22), B_22))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.52/1.79  tff(c_18, plain, (![A_18]: (r1_xboole_0(A_18, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.52/1.79  tff(c_16, plain, (![A_16, B_17]: (r1_tarski(k4_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.52/1.79  tff(c_38, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.52/1.79  tff(c_86, plain, (![A_55, B_56]: (k3_xboole_0(A_55, B_56)=A_55 | ~r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.52/1.79  tff(c_98, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_38, c_86])).
% 4.52/1.79  tff(c_10, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.52/1.79  tff(c_114, plain, (k5_xboole_0('#skF_3', '#skF_3')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_98, c_10])).
% 4.52/1.79  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.52/1.79  tff(c_99, plain, (![A_57, B_58]: (k5_xboole_0(A_57, k3_xboole_0(A_57, B_58))=k4_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.52/1.79  tff(c_108, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_99])).
% 4.52/1.79  tff(c_142, plain, (k4_xboole_0('#skF_3', '#skF_3')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_114, c_108])).
% 4.52/1.79  tff(c_155, plain, (r1_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_142, c_22])).
% 4.52/1.79  tff(c_161, plain, (![B_62, A_63]: (~r1_xboole_0(B_62, A_63) | ~r1_tarski(B_62, A_63) | v1_xboole_0(B_62))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.52/1.79  tff(c_164, plain, (~r1_tarski(k4_xboole_0('#skF_3', '#skF_4'), '#skF_3') | v1_xboole_0(k4_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_155, c_161])).
% 4.52/1.79  tff(c_173, plain, (v1_xboole_0(k4_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_164])).
% 4.52/1.79  tff(c_66, plain, (![A_50]: (r2_hidden('#skF_2'(A_50), A_50) | k1_xboole_0=A_50)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.52/1.79  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.52/1.79  tff(c_70, plain, (![A_50]: (~v1_xboole_0(A_50) | k1_xboole_0=A_50)), inference(resolution, [status(thm)], [c_66, c_2])).
% 4.52/1.79  tff(c_179, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_173, c_70])).
% 4.52/1.79  tff(c_243, plain, (![A_67, B_68, C_69]: (~r1_xboole_0(A_67, k4_xboole_0(B_68, C_69)) | ~r1_xboole_0(A_67, C_69) | r1_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.52/1.79  tff(c_249, plain, (![A_67]: (~r1_xboole_0(A_67, k1_xboole_0) | ~r1_xboole_0(A_67, '#skF_4') | r1_xboole_0(A_67, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_179, c_243])).
% 4.52/1.79  tff(c_257, plain, (![A_67]: (~r1_xboole_0(A_67, '#skF_4') | r1_xboole_0(A_67, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_249])).
% 4.52/1.79  tff(c_24, plain, (![A_23, B_24]: (r1_tarski(A_23, k2_xboole_0(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.52/1.79  tff(c_28, plain, (![A_28, B_29]: (k6_subset_1(A_28, B_29)=k4_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.52/1.79  tff(c_34, plain, (![C_37, A_35, B_36]: (k7_relat_1(C_37, k6_subset_1(A_35, B_36))=k6_subset_1(C_37, k7_relat_1(C_37, B_36)) | ~r1_tarski(k1_relat_1(C_37), A_35) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.52/1.79  tff(c_553, plain, (![C_96, A_97, B_98]: (k7_relat_1(C_96, k4_xboole_0(A_97, B_98))=k4_xboole_0(C_96, k7_relat_1(C_96, B_98)) | ~r1_tarski(k1_relat_1(C_96), A_97) | ~v1_relat_1(C_96))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_34])).
% 4.52/1.79  tff(c_1060, plain, (![C_148, B_149, B_150]: (k7_relat_1(C_148, k4_xboole_0(k2_xboole_0(k1_relat_1(C_148), B_149), B_150))=k4_xboole_0(C_148, k7_relat_1(C_148, B_150)) | ~v1_relat_1(C_148))), inference(resolution, [status(thm)], [c_24, c_553])).
% 4.52/1.79  tff(c_32, plain, (![C_34, A_32, B_33]: (k7_relat_1(k7_relat_1(C_34, A_32), B_33)=k1_xboole_0 | ~r1_xboole_0(A_32, B_33) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.52/1.79  tff(c_2685, plain, (![C_265, B_266, B_267, B_268]: (k7_relat_1(k4_xboole_0(C_265, k7_relat_1(C_265, B_266)), B_267)=k1_xboole_0 | ~r1_xboole_0(k4_xboole_0(k2_xboole_0(k1_relat_1(C_265), B_268), B_266), B_267) | ~v1_relat_1(C_265) | ~v1_relat_1(C_265))), inference(superposition, [status(thm), theory('equality')], [c_1060, c_32])).
% 4.52/1.79  tff(c_3040, plain, (![C_273, B_274, B_275]: (k7_relat_1(k4_xboole_0(C_273, k7_relat_1(C_273, B_274)), '#skF_3')=k1_xboole_0 | ~v1_relat_1(C_273) | ~r1_xboole_0(k4_xboole_0(k2_xboole_0(k1_relat_1(C_273), B_275), B_274), '#skF_4'))), inference(resolution, [status(thm)], [c_257, c_2685])).
% 4.52/1.79  tff(c_3401, plain, (![C_285]: (k7_relat_1(k4_xboole_0(C_285, k7_relat_1(C_285, '#skF_4')), '#skF_3')=k1_xboole_0 | ~v1_relat_1(C_285))), inference(resolution, [status(thm)], [c_22, c_3040])).
% 4.52/1.79  tff(c_36, plain, (k7_relat_1(k6_subset_1('#skF_5', k7_relat_1('#skF_5', '#skF_4')), '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.52/1.79  tff(c_42, plain, (k7_relat_1(k4_xboole_0('#skF_5', k7_relat_1('#skF_5', '#skF_4')), '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_36])).
% 4.52/1.79  tff(c_3422, plain, (~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3401, c_42])).
% 4.52/1.79  tff(c_3442, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_3422])).
% 4.52/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.52/1.79  
% 4.52/1.79  Inference rules
% 4.52/1.79  ----------------------
% 4.52/1.79  #Ref     : 0
% 4.52/1.79  #Sup     : 769
% 4.52/1.79  #Fact    : 0
% 4.52/1.79  #Define  : 0
% 4.52/1.79  #Split   : 2
% 4.52/1.79  #Chain   : 0
% 4.52/1.79  #Close   : 0
% 4.52/1.79  
% 4.52/1.79  Ordering : KBO
% 4.52/1.79  
% 4.52/1.79  Simplification rules
% 4.52/1.79  ----------------------
% 4.52/1.79  #Subsume      : 46
% 4.52/1.79  #Demod        : 590
% 4.52/1.79  #Tautology    : 455
% 4.52/1.79  #SimpNegUnit  : 0
% 4.52/1.79  #BackRed      : 15
% 4.52/1.79  
% 4.52/1.79  #Partial instantiations: 0
% 4.52/1.79  #Strategies tried      : 1
% 4.52/1.79  
% 4.52/1.79  Timing (in seconds)
% 4.52/1.79  ----------------------
% 4.52/1.80  Preprocessing        : 0.31
% 4.52/1.80  Parsing              : 0.17
% 4.52/1.80  CNF conversion       : 0.02
% 4.52/1.80  Main loop            : 0.72
% 4.52/1.80  Inferencing          : 0.26
% 4.52/1.80  Reduction            : 0.25
% 4.52/1.80  Demodulation         : 0.19
% 4.52/1.80  BG Simplification    : 0.03
% 4.52/1.80  Subsumption          : 0.13
% 4.52/1.80  Abstraction          : 0.03
% 4.52/1.80  MUC search           : 0.00
% 4.52/1.80  Cooper               : 0.00
% 4.52/1.80  Total                : 1.07
% 4.52/1.80  Index Insertion      : 0.00
% 4.52/1.80  Index Deletion       : 0.00
% 4.52/1.80  Index Matching       : 0.00
% 4.52/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
