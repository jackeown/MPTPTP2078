%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:18 EST 2020

% Result     : Theorem 8.05s
% Output     : CNFRefutation 8.05s
% Verified   : 
% Statistics : Number of formulae       :   64 (  83 expanded)
%              Number of leaves         :   30 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  104 ( 166 expanded)
%              Number of equality atoms :   14 (  19 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k8_relat_1(A,C),k8_relat_1(B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k8_relat_1(A,B),k8_relat_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_relat_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_44,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_34,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(k8_relat_1(A_34,B_35),B_35)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_51,plain,(
    ! [A_47,B_48] :
      ( k2_xboole_0(A_47,B_48) = B_48
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_138,plain,(
    ! [A_69,B_70] :
      ( k2_xboole_0(k8_relat_1(A_69,B_70),B_70) = B_70
      | ~ v1_relat_1(B_70) ) ),
    inference(resolution,[status(thm)],[c_34,c_51])).

tff(c_20,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(A_7,C_9)
      | ~ r1_tarski(k2_xboole_0(A_7,B_8),C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_144,plain,(
    ! [A_69,B_70,C_9] :
      ( r1_tarski(k8_relat_1(A_69,B_70),C_9)
      | ~ r1_tarski(B_70,C_9)
      | ~ v1_relat_1(B_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_20])).

tff(c_42,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_32,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_3'(A_16),A_16)
      | v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_72,plain,(
    ! [A_49,B_50] :
      ( k3_xboole_0(A_49,B_50) = A_49
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_185,plain,(
    ! [A_76,B_77] :
      ( k3_xboole_0(k8_relat_1(A_76,B_77),B_77) = k8_relat_1(A_76,B_77)
      | ~ v1_relat_1(B_77) ) ),
    inference(resolution,[status(thm)],[c_34,c_72])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_270,plain,(
    ! [D_86,B_87,A_88] :
      ( r2_hidden(D_86,B_87)
      | ~ r2_hidden(D_86,k8_relat_1(A_88,B_87))
      | ~ v1_relat_1(B_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_4])).

tff(c_288,plain,(
    ! [A_88,B_87] :
      ( r2_hidden('#skF_3'(k8_relat_1(A_88,B_87)),B_87)
      | ~ v1_relat_1(B_87)
      | v1_relat_1(k8_relat_1(A_88,B_87)) ) ),
    inference(resolution,[status(thm)],[c_32,c_270])).

tff(c_46,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_83,plain,(
    k3_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_44,c_72])).

tff(c_124,plain,(
    ! [D_64,B_65,A_66] :
      ( r2_hidden(D_64,B_65)
      | ~ r2_hidden(D_64,k3_xboole_0(A_66,B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_130,plain,(
    ! [D_64] :
      ( r2_hidden(D_64,'#skF_9')
      | ~ r2_hidden(D_64,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_124])).

tff(c_332,plain,(
    ! [A_94,B_95] :
      ( k4_tarski('#skF_4'(A_94,B_95),'#skF_5'(A_94,B_95)) = B_95
      | ~ r2_hidden(B_95,A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_30,plain,(
    ! [C_29,D_30,A_16] :
      ( k4_tarski(C_29,D_30) != '#skF_3'(A_16)
      | v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_336,plain,(
    ! [B_95,A_16,A_94] :
      ( B_95 != '#skF_3'(A_16)
      | v1_relat_1(A_16)
      | ~ r2_hidden(B_95,A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_30])).

tff(c_347,plain,(
    ! [A_99,A_100] :
      ( v1_relat_1(A_99)
      | ~ r2_hidden('#skF_3'(A_99),A_100)
      | ~ v1_relat_1(A_100) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_336])).

tff(c_364,plain,(
    ! [A_99] :
      ( v1_relat_1(A_99)
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden('#skF_3'(A_99),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_130,c_347])).

tff(c_396,plain,(
    ! [A_103] :
      ( v1_relat_1(A_103)
      | ~ r2_hidden('#skF_3'(A_103),'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_364])).

tff(c_400,plain,(
    ! [A_88] :
      ( ~ v1_relat_1('#skF_8')
      | v1_relat_1(k8_relat_1(A_88,'#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_288,c_396])).

tff(c_415,plain,(
    ! [A_88] : v1_relat_1(k8_relat_1(A_88,'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_400])).

tff(c_36,plain,(
    ! [B_37,A_36,C_38] :
      ( k8_relat_1(B_37,k8_relat_1(A_36,C_38)) = k8_relat_1(A_36,C_38)
      | ~ r1_tarski(A_36,B_37)
      | ~ v1_relat_1(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_432,plain,(
    ! [A_107,B_108,C_109] :
      ( r1_tarski(k8_relat_1(A_107,B_108),k8_relat_1(A_107,C_109))
      | ~ r1_tarski(B_108,C_109)
      | ~ v1_relat_1(C_109)
      | ~ v1_relat_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_7877,plain,(
    ! [A_502,C_503,B_504,C_505] :
      ( r1_tarski(k8_relat_1(A_502,C_503),k8_relat_1(B_504,C_505))
      | ~ r1_tarski(k8_relat_1(A_502,C_503),C_505)
      | ~ v1_relat_1(C_505)
      | ~ v1_relat_1(k8_relat_1(A_502,C_503))
      | ~ r1_tarski(A_502,B_504)
      | ~ v1_relat_1(C_503) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_432])).

tff(c_40,plain,(
    ~ r1_tarski(k8_relat_1('#skF_6','#skF_8'),k8_relat_1('#skF_7','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_7901,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_6','#skF_8'),'#skF_9')
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1(k8_relat_1('#skF_6','#skF_8'))
    | ~ r1_tarski('#skF_6','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_7877,c_40])).

tff(c_7935,plain,(
    ~ r1_tarski(k8_relat_1('#skF_6','#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_415,c_46,c_7901])).

tff(c_7954,plain,
    ( ~ r1_tarski('#skF_8','#skF_9')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_144,c_7935])).

tff(c_7971,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_7954])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:58:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.05/2.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.05/2.74  
% 8.05/2.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.05/2.74  %$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 8.05/2.74  
% 8.05/2.74  %Foreground sorts:
% 8.05/2.74  
% 8.05/2.74  
% 8.05/2.74  %Background operators:
% 8.05/2.74  
% 8.05/2.74  
% 8.05/2.74  %Foreground operators:
% 8.05/2.74  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 8.05/2.74  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.05/2.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.05/2.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.05/2.74  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.05/2.74  tff('#skF_7', type, '#skF_7': $i).
% 8.05/2.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.05/2.74  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.05/2.74  tff('#skF_6', type, '#skF_6': $i).
% 8.05/2.74  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.05/2.74  tff('#skF_9', type, '#skF_9': $i).
% 8.05/2.74  tff('#skF_8', type, '#skF_8': $i).
% 8.05/2.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.05/2.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.05/2.74  tff('#skF_3', type, '#skF_3': $i > $i).
% 8.05/2.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.05/2.74  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.05/2.74  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.05/2.74  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 8.05/2.74  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.05/2.74  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.05/2.74  
% 8.05/2.75  tff(f_89, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k8_relat_1(A, C), k8_relat_1(B, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t133_relat_1)).
% 8.05/2.75  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_relat_1)).
% 8.05/2.75  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 8.05/2.75  tff(f_38, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 8.05/2.75  tff(f_58, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 8.05/2.75  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.05/2.75  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 8.05/2.75  tff(f_68, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_relat_1)).
% 8.05/2.75  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k8_relat_1(A, B), k8_relat_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_relat_1)).
% 8.05/2.75  tff(c_48, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.05/2.75  tff(c_44, plain, (r1_tarski('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.05/2.75  tff(c_34, plain, (![A_34, B_35]: (r1_tarski(k8_relat_1(A_34, B_35), B_35) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.05/2.75  tff(c_51, plain, (![A_47, B_48]: (k2_xboole_0(A_47, B_48)=B_48 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.05/2.75  tff(c_138, plain, (![A_69, B_70]: (k2_xboole_0(k8_relat_1(A_69, B_70), B_70)=B_70 | ~v1_relat_1(B_70))), inference(resolution, [status(thm)], [c_34, c_51])).
% 8.05/2.75  tff(c_20, plain, (![A_7, C_9, B_8]: (r1_tarski(A_7, C_9) | ~r1_tarski(k2_xboole_0(A_7, B_8), C_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.05/2.75  tff(c_144, plain, (![A_69, B_70, C_9]: (r1_tarski(k8_relat_1(A_69, B_70), C_9) | ~r1_tarski(B_70, C_9) | ~v1_relat_1(B_70))), inference(superposition, [status(thm), theory('equality')], [c_138, c_20])).
% 8.05/2.75  tff(c_42, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.05/2.75  tff(c_32, plain, (![A_16]: (r2_hidden('#skF_3'(A_16), A_16) | v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.05/2.75  tff(c_72, plain, (![A_49, B_50]: (k3_xboole_0(A_49, B_50)=A_49 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.05/2.75  tff(c_185, plain, (![A_76, B_77]: (k3_xboole_0(k8_relat_1(A_76, B_77), B_77)=k8_relat_1(A_76, B_77) | ~v1_relat_1(B_77))), inference(resolution, [status(thm)], [c_34, c_72])).
% 8.05/2.75  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.05/2.75  tff(c_270, plain, (![D_86, B_87, A_88]: (r2_hidden(D_86, B_87) | ~r2_hidden(D_86, k8_relat_1(A_88, B_87)) | ~v1_relat_1(B_87))), inference(superposition, [status(thm), theory('equality')], [c_185, c_4])).
% 8.05/2.75  tff(c_288, plain, (![A_88, B_87]: (r2_hidden('#skF_3'(k8_relat_1(A_88, B_87)), B_87) | ~v1_relat_1(B_87) | v1_relat_1(k8_relat_1(A_88, B_87)))), inference(resolution, [status(thm)], [c_32, c_270])).
% 8.05/2.75  tff(c_46, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.05/2.75  tff(c_83, plain, (k3_xboole_0('#skF_8', '#skF_9')='#skF_8'), inference(resolution, [status(thm)], [c_44, c_72])).
% 8.05/2.75  tff(c_124, plain, (![D_64, B_65, A_66]: (r2_hidden(D_64, B_65) | ~r2_hidden(D_64, k3_xboole_0(A_66, B_65)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.05/2.75  tff(c_130, plain, (![D_64]: (r2_hidden(D_64, '#skF_9') | ~r2_hidden(D_64, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_83, c_124])).
% 8.05/2.75  tff(c_332, plain, (![A_94, B_95]: (k4_tarski('#skF_4'(A_94, B_95), '#skF_5'(A_94, B_95))=B_95 | ~r2_hidden(B_95, A_94) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.05/2.75  tff(c_30, plain, (![C_29, D_30, A_16]: (k4_tarski(C_29, D_30)!='#skF_3'(A_16) | v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.05/2.75  tff(c_336, plain, (![B_95, A_16, A_94]: (B_95!='#skF_3'(A_16) | v1_relat_1(A_16) | ~r2_hidden(B_95, A_94) | ~v1_relat_1(A_94))), inference(superposition, [status(thm), theory('equality')], [c_332, c_30])).
% 8.05/2.75  tff(c_347, plain, (![A_99, A_100]: (v1_relat_1(A_99) | ~r2_hidden('#skF_3'(A_99), A_100) | ~v1_relat_1(A_100))), inference(reflexivity, [status(thm), theory('equality')], [c_336])).
% 8.05/2.75  tff(c_364, plain, (![A_99]: (v1_relat_1(A_99) | ~v1_relat_1('#skF_9') | ~r2_hidden('#skF_3'(A_99), '#skF_8'))), inference(resolution, [status(thm)], [c_130, c_347])).
% 8.05/2.75  tff(c_396, plain, (![A_103]: (v1_relat_1(A_103) | ~r2_hidden('#skF_3'(A_103), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_364])).
% 8.05/2.75  tff(c_400, plain, (![A_88]: (~v1_relat_1('#skF_8') | v1_relat_1(k8_relat_1(A_88, '#skF_8')))), inference(resolution, [status(thm)], [c_288, c_396])).
% 8.05/2.75  tff(c_415, plain, (![A_88]: (v1_relat_1(k8_relat_1(A_88, '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_400])).
% 8.05/2.75  tff(c_36, plain, (![B_37, A_36, C_38]: (k8_relat_1(B_37, k8_relat_1(A_36, C_38))=k8_relat_1(A_36, C_38) | ~r1_tarski(A_36, B_37) | ~v1_relat_1(C_38))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.05/2.75  tff(c_432, plain, (![A_107, B_108, C_109]: (r1_tarski(k8_relat_1(A_107, B_108), k8_relat_1(A_107, C_109)) | ~r1_tarski(B_108, C_109) | ~v1_relat_1(C_109) | ~v1_relat_1(B_108))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.05/2.75  tff(c_7877, plain, (![A_502, C_503, B_504, C_505]: (r1_tarski(k8_relat_1(A_502, C_503), k8_relat_1(B_504, C_505)) | ~r1_tarski(k8_relat_1(A_502, C_503), C_505) | ~v1_relat_1(C_505) | ~v1_relat_1(k8_relat_1(A_502, C_503)) | ~r1_tarski(A_502, B_504) | ~v1_relat_1(C_503))), inference(superposition, [status(thm), theory('equality')], [c_36, c_432])).
% 8.05/2.75  tff(c_40, plain, (~r1_tarski(k8_relat_1('#skF_6', '#skF_8'), k8_relat_1('#skF_7', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.05/2.75  tff(c_7901, plain, (~r1_tarski(k8_relat_1('#skF_6', '#skF_8'), '#skF_9') | ~v1_relat_1('#skF_9') | ~v1_relat_1(k8_relat_1('#skF_6', '#skF_8')) | ~r1_tarski('#skF_6', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_7877, c_40])).
% 8.05/2.75  tff(c_7935, plain, (~r1_tarski(k8_relat_1('#skF_6', '#skF_8'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_415, c_46, c_7901])).
% 8.05/2.75  tff(c_7954, plain, (~r1_tarski('#skF_8', '#skF_9') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_144, c_7935])).
% 8.05/2.75  tff(c_7971, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_7954])).
% 8.05/2.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.05/2.75  
% 8.05/2.75  Inference rules
% 8.05/2.75  ----------------------
% 8.05/2.75  #Ref     : 1
% 8.05/2.75  #Sup     : 1830
% 8.05/2.75  #Fact    : 0
% 8.05/2.75  #Define  : 0
% 8.05/2.75  #Split   : 8
% 8.05/2.75  #Chain   : 0
% 8.05/2.75  #Close   : 0
% 8.05/2.75  
% 8.05/2.75  Ordering : KBO
% 8.05/2.75  
% 8.05/2.75  Simplification rules
% 8.05/2.75  ----------------------
% 8.05/2.75  #Subsume      : 430
% 8.05/2.75  #Demod        : 796
% 8.05/2.75  #Tautology    : 529
% 8.05/2.75  #SimpNegUnit  : 1
% 8.05/2.75  #BackRed      : 0
% 8.05/2.75  
% 8.05/2.75  #Partial instantiations: 0
% 8.05/2.75  #Strategies tried      : 1
% 8.05/2.75  
% 8.05/2.75  Timing (in seconds)
% 8.05/2.75  ----------------------
% 8.05/2.76  Preprocessing        : 0.30
% 8.05/2.76  Parsing              : 0.16
% 8.05/2.76  CNF conversion       : 0.02
% 8.05/2.76  Main loop            : 1.69
% 8.05/2.76  Inferencing          : 0.50
% 8.05/2.76  Reduction            : 0.54
% 8.05/2.76  Demodulation         : 0.40
% 8.05/2.76  BG Simplification    : 0.07
% 8.05/2.76  Subsumption          : 0.48
% 8.05/2.76  Abstraction          : 0.06
% 8.05/2.76  MUC search           : 0.00
% 8.05/2.76  Cooper               : 0.00
% 8.05/2.76  Total                : 2.02
% 8.05/2.76  Index Insertion      : 0.00
% 8.05/2.76  Index Deletion       : 0.00
% 8.05/2.76  Index Matching       : 0.00
% 8.05/2.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
