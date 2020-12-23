%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:13 EST 2020

% Result     : Theorem 7.33s
% Output     : CNFRefutation 7.68s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 107 expanded)
%              Number of leaves         :   24 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :   76 ( 180 expanded)
%              Number of equality atoms :   24 (  64 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => ( A = k1_xboole_0
          | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_70,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(B,C) )
     => ( A = k1_xboole_0
        | r1_tarski(B,k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(c_50,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_5'),k1_setfam_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_38,plain,(
    ! [A_21,B_22] : r1_xboole_0(k4_xboole_0(A_21,B_22),B_22) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_87,plain,(
    ! [B_38,A_39] :
      ( r1_xboole_0(B_38,A_39)
      | ~ r1_xboole_0(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_93,plain,(
    ! [B_22,A_21] : r1_xboole_0(B_22,k4_xboole_0(A_21,B_22)) ),
    inference(resolution,[status(thm)],[c_38,c_87])).

tff(c_114,plain,(
    ! [A_43,B_44] :
      ( k4_xboole_0(A_43,B_44) = A_43
      | ~ r1_xboole_0(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_127,plain,(
    ! [B_22,A_21] : k4_xboole_0(B_22,k4_xboole_0(A_21,B_22)) = B_22 ),
    inference(resolution,[status(thm)],[c_93,c_114])).

tff(c_54,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_42,plain,(
    ! [A_23,B_24] :
      ( r1_xboole_0(A_23,B_24)
      | k4_xboole_0(A_23,B_24) != A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_495,plain,(
    ! [A_79,C_80,B_81] :
      ( r1_xboole_0(A_79,C_80)
      | ~ r1_xboole_0(B_81,C_80)
      | ~ r1_tarski(A_79,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2966,plain,(
    ! [A_212,B_213,A_214] :
      ( r1_xboole_0(A_212,B_213)
      | ~ r1_tarski(A_212,A_214)
      | k4_xboole_0(A_214,B_213) != A_214 ) ),
    inference(resolution,[status(thm)],[c_42,c_495])).

tff(c_3001,plain,(
    ! [B_215] :
      ( r1_xboole_0('#skF_4',B_215)
      | k4_xboole_0('#skF_5',B_215) != '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_54,c_2966])).

tff(c_40,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = A_23
      | ~ r1_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_3036,plain,(
    ! [B_217] :
      ( k4_xboole_0('#skF_4',B_217) = '#skF_4'
      | k4_xboole_0('#skF_5',B_217) != '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_3001,c_40])).

tff(c_3061,plain,(
    ! [A_218] : k4_xboole_0('#skF_4',k4_xboole_0(A_218,'#skF_5')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_3036])).

tff(c_30,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3142,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3061,c_30])).

tff(c_742,plain,(
    ! [A_92,B_93] :
      ( r2_hidden('#skF_3'(A_92,B_93),A_92)
      | r1_tarski(B_93,k1_setfam_1(A_92))
      | k1_xboole_0 = A_92 ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6690,plain,(
    ! [A_293,B_294,B_295] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_293,B_294),B_295),B_294)
      | r1_tarski(B_295,k1_setfam_1(k3_xboole_0(A_293,B_294)))
      | k3_xboole_0(A_293,B_294) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_742,c_4])).

tff(c_6729,plain,(
    ! [B_295] :
      ( r2_hidden('#skF_3'('#skF_4',B_295),'#skF_5')
      | r1_tarski(B_295,k1_setfam_1(k3_xboole_0('#skF_4','#skF_5')))
      | k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3142,c_6690])).

tff(c_6757,plain,(
    ! [B_295] :
      ( r2_hidden('#skF_3'('#skF_4',B_295),'#skF_5')
      | r1_tarski(B_295,k1_setfam_1('#skF_4'))
      | k1_xboole_0 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3142,c_3142,c_6729])).

tff(c_6939,plain,(
    ! [B_298] :
      ( r2_hidden('#skF_3'('#skF_4',B_298),'#skF_5')
      | r1_tarski(B_298,k1_setfam_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_6757])).

tff(c_44,plain,(
    ! [B_26,A_25] :
      ( r1_tarski(k1_setfam_1(B_26),A_25)
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_766,plain,(
    ! [B_97,A_98] :
      ( ~ r1_tarski(B_97,'#skF_3'(A_98,B_97))
      | r1_tarski(B_97,k1_setfam_1(A_98))
      | k1_xboole_0 = A_98 ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_770,plain,(
    ! [B_26,A_98] :
      ( r1_tarski(k1_setfam_1(B_26),k1_setfam_1(A_98))
      | k1_xboole_0 = A_98
      | ~ r2_hidden('#skF_3'(A_98,k1_setfam_1(B_26)),B_26) ) ),
    inference(resolution,[status(thm)],[c_44,c_766])).

tff(c_6943,plain,
    ( k1_xboole_0 = '#skF_4'
    | r1_tarski(k1_setfam_1('#skF_5'),k1_setfam_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6939,c_770])).

tff(c_6947,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_52,c_50,c_6943])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:43:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.33/2.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.68/2.97  
% 7.68/2.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.68/2.97  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 7.68/2.97  
% 7.68/2.97  %Foreground sorts:
% 7.68/2.97  
% 7.68/2.97  
% 7.68/2.97  %Background operators:
% 7.68/2.97  
% 7.68/2.97  
% 7.68/2.97  %Foreground operators:
% 7.68/2.97  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.68/2.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.68/2.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.68/2.97  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.68/2.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.68/2.97  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.68/2.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.68/2.97  tff('#skF_5', type, '#skF_5': $i).
% 7.68/2.97  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.68/2.97  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.68/2.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.68/2.97  tff('#skF_4', type, '#skF_4': $i).
% 7.68/2.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.68/2.97  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.68/2.97  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.68/2.97  
% 7.68/2.99  tff(f_94, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 7.68/2.99  tff(f_70, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 7.68/2.99  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 7.68/2.99  tff(f_74, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 7.68/2.99  tff(f_56, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 7.68/2.99  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.68/2.99  tff(f_87, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(B, C))) => ((A = k1_xboole_0) | r1_tarski(B, k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_setfam_1)).
% 7.68/2.99  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 7.68/2.99  tff(f_78, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 7.68/2.99  tff(c_50, plain, (~r1_tarski(k1_setfam_1('#skF_5'), k1_setfam_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.68/2.99  tff(c_52, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.68/2.99  tff(c_38, plain, (![A_21, B_22]: (r1_xboole_0(k4_xboole_0(A_21, B_22), B_22))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.68/2.99  tff(c_87, plain, (![B_38, A_39]: (r1_xboole_0(B_38, A_39) | ~r1_xboole_0(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.68/2.99  tff(c_93, plain, (![B_22, A_21]: (r1_xboole_0(B_22, k4_xboole_0(A_21, B_22)))), inference(resolution, [status(thm)], [c_38, c_87])).
% 7.68/2.99  tff(c_114, plain, (![A_43, B_44]: (k4_xboole_0(A_43, B_44)=A_43 | ~r1_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.68/2.99  tff(c_127, plain, (![B_22, A_21]: (k4_xboole_0(B_22, k4_xboole_0(A_21, B_22))=B_22)), inference(resolution, [status(thm)], [c_93, c_114])).
% 7.68/2.99  tff(c_54, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.68/2.99  tff(c_42, plain, (![A_23, B_24]: (r1_xboole_0(A_23, B_24) | k4_xboole_0(A_23, B_24)!=A_23)), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.68/2.99  tff(c_495, plain, (![A_79, C_80, B_81]: (r1_xboole_0(A_79, C_80) | ~r1_xboole_0(B_81, C_80) | ~r1_tarski(A_79, B_81))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.68/2.99  tff(c_2966, plain, (![A_212, B_213, A_214]: (r1_xboole_0(A_212, B_213) | ~r1_tarski(A_212, A_214) | k4_xboole_0(A_214, B_213)!=A_214)), inference(resolution, [status(thm)], [c_42, c_495])).
% 7.68/2.99  tff(c_3001, plain, (![B_215]: (r1_xboole_0('#skF_4', B_215) | k4_xboole_0('#skF_5', B_215)!='#skF_5')), inference(resolution, [status(thm)], [c_54, c_2966])).
% 7.68/2.99  tff(c_40, plain, (![A_23, B_24]: (k4_xboole_0(A_23, B_24)=A_23 | ~r1_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.68/2.99  tff(c_3036, plain, (![B_217]: (k4_xboole_0('#skF_4', B_217)='#skF_4' | k4_xboole_0('#skF_5', B_217)!='#skF_5')), inference(resolution, [status(thm)], [c_3001, c_40])).
% 7.68/2.99  tff(c_3061, plain, (![A_218]: (k4_xboole_0('#skF_4', k4_xboole_0(A_218, '#skF_5'))='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_127, c_3036])).
% 7.68/2.99  tff(c_30, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.68/2.99  tff(c_3142, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3061, c_30])).
% 7.68/2.99  tff(c_742, plain, (![A_92, B_93]: (r2_hidden('#skF_3'(A_92, B_93), A_92) | r1_tarski(B_93, k1_setfam_1(A_92)) | k1_xboole_0=A_92)), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.68/2.99  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.68/2.99  tff(c_6690, plain, (![A_293, B_294, B_295]: (r2_hidden('#skF_3'(k3_xboole_0(A_293, B_294), B_295), B_294) | r1_tarski(B_295, k1_setfam_1(k3_xboole_0(A_293, B_294))) | k3_xboole_0(A_293, B_294)=k1_xboole_0)), inference(resolution, [status(thm)], [c_742, c_4])).
% 7.68/2.99  tff(c_6729, plain, (![B_295]: (r2_hidden('#skF_3'('#skF_4', B_295), '#skF_5') | r1_tarski(B_295, k1_setfam_1(k3_xboole_0('#skF_4', '#skF_5'))) | k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3142, c_6690])).
% 7.68/2.99  tff(c_6757, plain, (![B_295]: (r2_hidden('#skF_3'('#skF_4', B_295), '#skF_5') | r1_tarski(B_295, k1_setfam_1('#skF_4')) | k1_xboole_0='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3142, c_3142, c_6729])).
% 7.68/2.99  tff(c_6939, plain, (![B_298]: (r2_hidden('#skF_3'('#skF_4', B_298), '#skF_5') | r1_tarski(B_298, k1_setfam_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_52, c_6757])).
% 7.68/2.99  tff(c_44, plain, (![B_26, A_25]: (r1_tarski(k1_setfam_1(B_26), A_25) | ~r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.68/2.99  tff(c_766, plain, (![B_97, A_98]: (~r1_tarski(B_97, '#skF_3'(A_98, B_97)) | r1_tarski(B_97, k1_setfam_1(A_98)) | k1_xboole_0=A_98)), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.68/2.99  tff(c_770, plain, (![B_26, A_98]: (r1_tarski(k1_setfam_1(B_26), k1_setfam_1(A_98)) | k1_xboole_0=A_98 | ~r2_hidden('#skF_3'(A_98, k1_setfam_1(B_26)), B_26))), inference(resolution, [status(thm)], [c_44, c_766])).
% 7.68/2.99  tff(c_6943, plain, (k1_xboole_0='#skF_4' | r1_tarski(k1_setfam_1('#skF_5'), k1_setfam_1('#skF_4'))), inference(resolution, [status(thm)], [c_6939, c_770])).
% 7.68/2.99  tff(c_6947, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_52, c_50, c_6943])).
% 7.68/2.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.68/2.99  
% 7.68/2.99  Inference rules
% 7.68/2.99  ----------------------
% 7.68/2.99  #Ref     : 0
% 7.68/2.99  #Sup     : 1704
% 7.68/2.99  #Fact    : 0
% 7.68/2.99  #Define  : 0
% 7.68/2.99  #Split   : 1
% 7.68/2.99  #Chain   : 0
% 7.68/2.99  #Close   : 0
% 7.68/2.99  
% 7.68/2.99  Ordering : KBO
% 7.68/2.99  
% 7.68/2.99  Simplification rules
% 7.68/2.99  ----------------------
% 7.68/2.99  #Subsume      : 131
% 7.68/2.99  #Demod        : 1249
% 7.68/2.99  #Tautology    : 1061
% 7.68/2.99  #SimpNegUnit  : 13
% 7.68/2.99  #BackRed      : 11
% 7.68/2.99  
% 7.68/2.99  #Partial instantiations: 0
% 7.68/2.99  #Strategies tried      : 1
% 7.68/2.99  
% 7.68/2.99  Timing (in seconds)
% 7.68/2.99  ----------------------
% 7.75/3.00  Preprocessing        : 0.47
% 7.75/3.00  Parsing              : 0.24
% 7.75/3.00  CNF conversion       : 0.04
% 7.75/3.00  Main loop            : 1.62
% 7.75/3.00  Inferencing          : 0.52
% 7.75/3.00  Reduction            : 0.61
% 7.75/3.00  Demodulation         : 0.47
% 7.75/3.00  BG Simplification    : 0.06
% 7.75/3.00  Subsumption          : 0.32
% 7.75/3.00  Abstraction          : 0.07
% 7.75/3.00  MUC search           : 0.00
% 7.75/3.00  Cooper               : 0.00
% 7.75/3.00  Total                : 2.13
% 7.75/3.00  Index Insertion      : 0.00
% 7.75/3.00  Index Deletion       : 0.00
% 7.75/3.00  Index Matching       : 0.00
% 7.75/3.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
