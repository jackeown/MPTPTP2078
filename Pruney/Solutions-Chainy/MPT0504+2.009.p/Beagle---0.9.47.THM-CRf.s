%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:50 EST 2020

% Result     : Theorem 4.56s
% Output     : CNFRefutation 4.56s
% Verified   : 
% Statistics : Number of formulae       :   47 (  52 expanded)
%              Number of leaves         :   24 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :   60 (  75 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_30,plain,(
    ! [A_16,B_17] :
      ( v1_relat_1(k7_relat_1(A_16,B_17))
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_71,plain,(
    ! [B_34,A_35] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_34,A_35)),A_35)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_75,plain,(
    ! [B_34,A_35] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1(B_34,A_35)),A_35) = k1_relat_1(k7_relat_1(B_34,A_35))
      | ~ v1_relat_1(B_34) ) ),
    inference(resolution,[status(thm)],[c_71,c_26])).

tff(c_76,plain,(
    ! [A_36,B_37] :
      ( r2_hidden('#skF_1'(A_36,B_37),A_36)
      | r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_665,plain,(
    ! [A_92,B_93,B_94] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_92,B_93),B_94),B_93)
      | r1_tarski(k3_xboole_0(A_92,B_93),B_94) ) ),
    inference(resolution,[status(thm)],[c_76,c_10])).

tff(c_38,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_42,plain,(
    ! [A_24,B_25] :
      ( k3_xboole_0(A_24,B_25) = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_46,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_42])).

tff(c_61,plain,(
    ! [D_30,B_31,A_32] :
      ( r2_hidden(D_30,B_31)
      | ~ r2_hidden(D_30,k3_xboole_0(A_32,B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_65,plain,(
    ! [D_33] :
      ( r2_hidden(D_33,'#skF_5')
      | ~ r2_hidden(D_33,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_61])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_70,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_1,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_65,c_4])).

tff(c_751,plain,(
    ! [A_97] : r1_tarski(k3_xboole_0(A_97,'#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_665,c_70])).

tff(c_1018,plain,(
    ! [B_106] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_106,'#skF_4')),'#skF_5')
      | ~ v1_relat_1(B_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_751])).

tff(c_34,plain,(
    ! [B_21,A_20] :
      ( k7_relat_1(B_21,A_20) = B_21
      | ~ r1_tarski(k1_relat_1(B_21),A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2357,plain,(
    ! [B_198] :
      ( k7_relat_1(k7_relat_1(B_198,'#skF_4'),'#skF_5') = k7_relat_1(B_198,'#skF_4')
      | ~ v1_relat_1(k7_relat_1(B_198,'#skF_4'))
      | ~ v1_relat_1(B_198) ) ),
    inference(resolution,[status(thm)],[c_1018,c_34])).

tff(c_2424,plain,(
    ! [A_201] :
      ( k7_relat_1(k7_relat_1(A_201,'#skF_4'),'#skF_5') = k7_relat_1(A_201,'#skF_4')
      | ~ v1_relat_1(A_201) ) ),
    inference(resolution,[status(thm)],[c_30,c_2357])).

tff(c_36,plain,(
    k7_relat_1(k7_relat_1('#skF_6','#skF_4'),'#skF_5') != k7_relat_1('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2442,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2424,c_36])).

tff(c_2458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2442])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:03:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.56/1.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.56/1.87  
% 4.56/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.56/1.87  %$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 4.56/1.87  
% 4.56/1.87  %Foreground sorts:
% 4.56/1.87  
% 4.56/1.87  
% 4.56/1.87  %Background operators:
% 4.56/1.87  
% 4.56/1.87  
% 4.56/1.87  %Foreground operators:
% 4.56/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.56/1.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.56/1.87  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.56/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.56/1.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.56/1.87  tff('#skF_5', type, '#skF_5': $i).
% 4.56/1.87  tff('#skF_6', type, '#skF_6': $i).
% 4.56/1.87  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.56/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.56/1.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.56/1.87  tff('#skF_4', type, '#skF_4': $i).
% 4.56/1.87  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.56/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.56/1.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.56/1.87  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.56/1.87  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.56/1.87  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.56/1.87  
% 4.56/1.88  tff(f_68, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_relat_1)).
% 4.56/1.88  tff(f_51, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 4.56/1.88  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 4.56/1.88  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.56/1.88  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.56/1.88  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.56/1.88  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 4.56/1.88  tff(c_40, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.56/1.88  tff(c_30, plain, (![A_16, B_17]: (v1_relat_1(k7_relat_1(A_16, B_17)) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.56/1.88  tff(c_71, plain, (![B_34, A_35]: (r1_tarski(k1_relat_1(k7_relat_1(B_34, A_35)), A_35) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.56/1.88  tff(c_26, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.56/1.88  tff(c_75, plain, (![B_34, A_35]: (k3_xboole_0(k1_relat_1(k7_relat_1(B_34, A_35)), A_35)=k1_relat_1(k7_relat_1(B_34, A_35)) | ~v1_relat_1(B_34))), inference(resolution, [status(thm)], [c_71, c_26])).
% 4.56/1.88  tff(c_76, plain, (![A_36, B_37]: (r2_hidden('#skF_1'(A_36, B_37), A_36) | r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.56/1.88  tff(c_10, plain, (![D_11, B_7, A_6]: (r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.56/1.88  tff(c_665, plain, (![A_92, B_93, B_94]: (r2_hidden('#skF_1'(k3_xboole_0(A_92, B_93), B_94), B_93) | r1_tarski(k3_xboole_0(A_92, B_93), B_94))), inference(resolution, [status(thm)], [c_76, c_10])).
% 4.56/1.88  tff(c_38, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.56/1.88  tff(c_42, plain, (![A_24, B_25]: (k3_xboole_0(A_24, B_25)=A_24 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.56/1.88  tff(c_46, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_38, c_42])).
% 4.56/1.88  tff(c_61, plain, (![D_30, B_31, A_32]: (r2_hidden(D_30, B_31) | ~r2_hidden(D_30, k3_xboole_0(A_32, B_31)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.56/1.88  tff(c_65, plain, (![D_33]: (r2_hidden(D_33, '#skF_5') | ~r2_hidden(D_33, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_61])).
% 4.56/1.88  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.56/1.88  tff(c_70, plain, (![A_1]: (r1_tarski(A_1, '#skF_5') | ~r2_hidden('#skF_1'(A_1, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_65, c_4])).
% 4.56/1.88  tff(c_751, plain, (![A_97]: (r1_tarski(k3_xboole_0(A_97, '#skF_4'), '#skF_5'))), inference(resolution, [status(thm)], [c_665, c_70])).
% 4.56/1.88  tff(c_1018, plain, (![B_106]: (r1_tarski(k1_relat_1(k7_relat_1(B_106, '#skF_4')), '#skF_5') | ~v1_relat_1(B_106))), inference(superposition, [status(thm), theory('equality')], [c_75, c_751])).
% 4.56/1.88  tff(c_34, plain, (![B_21, A_20]: (k7_relat_1(B_21, A_20)=B_21 | ~r1_tarski(k1_relat_1(B_21), A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.56/1.88  tff(c_2357, plain, (![B_198]: (k7_relat_1(k7_relat_1(B_198, '#skF_4'), '#skF_5')=k7_relat_1(B_198, '#skF_4') | ~v1_relat_1(k7_relat_1(B_198, '#skF_4')) | ~v1_relat_1(B_198))), inference(resolution, [status(thm)], [c_1018, c_34])).
% 4.56/1.88  tff(c_2424, plain, (![A_201]: (k7_relat_1(k7_relat_1(A_201, '#skF_4'), '#skF_5')=k7_relat_1(A_201, '#skF_4') | ~v1_relat_1(A_201))), inference(resolution, [status(thm)], [c_30, c_2357])).
% 4.56/1.88  tff(c_36, plain, (k7_relat_1(k7_relat_1('#skF_6', '#skF_4'), '#skF_5')!=k7_relat_1('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.56/1.88  tff(c_2442, plain, (~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2424, c_36])).
% 4.56/1.88  tff(c_2458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_2442])).
% 4.56/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.56/1.88  
% 4.56/1.88  Inference rules
% 4.56/1.88  ----------------------
% 4.56/1.88  #Ref     : 0
% 4.56/1.88  #Sup     : 581
% 4.56/1.88  #Fact    : 0
% 4.56/1.88  #Define  : 0
% 4.56/1.88  #Split   : 2
% 4.56/1.88  #Chain   : 0
% 4.56/1.88  #Close   : 0
% 4.56/1.88  
% 4.56/1.88  Ordering : KBO
% 4.56/1.88  
% 4.56/1.88  Simplification rules
% 4.56/1.88  ----------------------
% 4.56/1.88  #Subsume      : 157
% 4.56/1.88  #Demod        : 128
% 4.56/1.88  #Tautology    : 126
% 4.56/1.88  #SimpNegUnit  : 0
% 4.56/1.88  #BackRed      : 0
% 4.56/1.88  
% 4.56/1.88  #Partial instantiations: 0
% 4.56/1.88  #Strategies tried      : 1
% 4.56/1.88  
% 4.56/1.88  Timing (in seconds)
% 4.56/1.88  ----------------------
% 4.56/1.89  Preprocessing        : 0.30
% 4.56/1.89  Parsing              : 0.16
% 4.56/1.89  CNF conversion       : 0.02
% 4.56/1.89  Main loop            : 0.79
% 4.56/1.89  Inferencing          : 0.27
% 4.56/1.89  Reduction            : 0.20
% 4.56/1.89  Demodulation         : 0.14
% 4.56/1.89  BG Simplification    : 0.03
% 4.56/1.89  Subsumption          : 0.23
% 4.56/1.89  Abstraction          : 0.04
% 4.56/1.89  MUC search           : 0.00
% 4.56/1.89  Cooper               : 0.00
% 4.56/1.89  Total                : 1.12
% 4.56/1.89  Index Insertion      : 0.00
% 4.56/1.89  Index Deletion       : 0.00
% 4.56/1.89  Index Matching       : 0.00
% 4.56/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
