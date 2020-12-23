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
% DateTime   : Thu Dec  3 10:04:13 EST 2020

% Result     : Theorem 4.52s
% Output     : CNFRefutation 4.52s
% Verified   : 
% Statistics : Number of formulae       :   46 (  63 expanded)
%              Number of leaves         :   25 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   61 ( 104 expanded)
%              Number of equality atoms :   10 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_funct_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).

tff(c_38,plain,(
    r2_hidden('#skF_3',k3_xboole_0(k1_relat_1('#skF_5'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_80,plain,(
    ! [D_31,A_32,B_33] :
      ( r2_hidden(D_31,A_32)
      | ~ r2_hidden(D_31,k4_xboole_0(A_32,B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_93,plain,(
    ! [D_37,A_38,B_39] :
      ( r2_hidden(D_37,A_38)
      | ~ r2_hidden(D_37,k3_xboole_0(A_38,B_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_80])).

tff(c_97,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_38,c_93])).

tff(c_124,plain,(
    ! [D_45,A_46,B_47] :
      ( r2_hidden(D_45,k4_xboole_0(A_46,B_47))
      | r2_hidden(D_45,B_47)
      | ~ r2_hidden(D_45,A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_76,plain,(
    ! [D_28,B_29,A_30] :
      ( ~ r2_hidden(D_28,B_29)
      | ~ r2_hidden(D_28,k4_xboole_0(A_30,B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_79,plain,(
    ! [D_28,A_7,B_8] :
      ( ~ r2_hidden(D_28,k4_xboole_0(A_7,B_8))
      | ~ r2_hidden(D_28,k3_xboole_0(A_7,B_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_76])).

tff(c_144,plain,(
    ! [D_51,A_52,B_53] :
      ( ~ r2_hidden(D_51,k3_xboole_0(A_52,B_53))
      | r2_hidden(D_51,B_53)
      | ~ r2_hidden(D_51,A_52) ) ),
    inference(resolution,[status(thm)],[c_124,c_79])).

tff(c_147,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_38,c_144])).

tff(c_150,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_147])).

tff(c_42,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_28,plain,(
    ! [A_16,C_18,B_17] :
      ( r2_hidden(A_16,k1_relat_1(k7_relat_1(C_18,B_17)))
      | ~ r2_hidden(A_16,k1_relat_1(C_18))
      | ~ r2_hidden(A_16,B_17)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_607,plain,(
    ! [C_95,B_96,A_97] :
      ( k1_funct_1(k7_relat_1(C_95,B_96),A_97) = k1_funct_1(C_95,A_97)
      | ~ r2_hidden(A_97,k1_relat_1(k7_relat_1(C_95,B_96)))
      | ~ v1_funct_1(C_95)
      | ~ v1_relat_1(C_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2903,plain,(
    ! [C_156,B_157,A_158] :
      ( k1_funct_1(k7_relat_1(C_156,B_157),A_158) = k1_funct_1(C_156,A_158)
      | ~ v1_funct_1(C_156)
      | ~ r2_hidden(A_158,k1_relat_1(C_156))
      | ~ r2_hidden(A_158,B_157)
      | ~ v1_relat_1(C_156) ) ),
    inference(resolution,[status(thm)],[c_28,c_607])).

tff(c_2931,plain,(
    ! [B_157] :
      ( k1_funct_1(k7_relat_1('#skF_5',B_157),'#skF_3') = k1_funct_1('#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ r2_hidden('#skF_3',B_157)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_97,c_2903])).

tff(c_3157,plain,(
    ! [B_162] :
      ( k1_funct_1(k7_relat_1('#skF_5',B_162),'#skF_3') = k1_funct_1('#skF_5','#skF_3')
      | ~ r2_hidden('#skF_3',B_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_2931])).

tff(c_36,plain,(
    k1_funct_1(k7_relat_1('#skF_5','#skF_4'),'#skF_3') != k1_funct_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3163,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3157,c_36])).

tff(c_3171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_3163])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:02:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.52/1.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.52/1.89  
% 4.52/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.52/1.89  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 4.52/1.89  
% 4.52/1.89  %Foreground sorts:
% 4.52/1.89  
% 4.52/1.89  
% 4.52/1.89  %Background operators:
% 4.52/1.89  
% 4.52/1.89  
% 4.52/1.89  %Foreground operators:
% 4.52/1.89  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.52/1.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.52/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.52/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.52/1.89  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.52/1.89  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.52/1.89  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.52/1.89  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.52/1.89  tff('#skF_5', type, '#skF_5': $i).
% 4.52/1.89  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.52/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.52/1.89  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.52/1.89  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.52/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.52/1.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.52/1.89  tff('#skF_4', type, '#skF_4': $i).
% 4.52/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.52/1.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.52/1.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.52/1.89  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.52/1.89  
% 4.52/1.90  tff(f_68, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_funct_1)).
% 4.52/1.90  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.52/1.90  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.52/1.90  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 4.52/1.90  tff(f_59, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_funct_1)).
% 4.52/1.90  tff(c_38, plain, (r2_hidden('#skF_3', k3_xboole_0(k1_relat_1('#skF_5'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.52/1.90  tff(c_20, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.52/1.90  tff(c_80, plain, (![D_31, A_32, B_33]: (r2_hidden(D_31, A_32) | ~r2_hidden(D_31, k4_xboole_0(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.52/1.90  tff(c_93, plain, (![D_37, A_38, B_39]: (r2_hidden(D_37, A_38) | ~r2_hidden(D_37, k3_xboole_0(A_38, B_39)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_80])).
% 4.52/1.90  tff(c_97, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_93])).
% 4.52/1.90  tff(c_124, plain, (![D_45, A_46, B_47]: (r2_hidden(D_45, k4_xboole_0(A_46, B_47)) | r2_hidden(D_45, B_47) | ~r2_hidden(D_45, A_46))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.52/1.90  tff(c_76, plain, (![D_28, B_29, A_30]: (~r2_hidden(D_28, B_29) | ~r2_hidden(D_28, k4_xboole_0(A_30, B_29)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.52/1.90  tff(c_79, plain, (![D_28, A_7, B_8]: (~r2_hidden(D_28, k4_xboole_0(A_7, B_8)) | ~r2_hidden(D_28, k3_xboole_0(A_7, B_8)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_76])).
% 4.52/1.90  tff(c_144, plain, (![D_51, A_52, B_53]: (~r2_hidden(D_51, k3_xboole_0(A_52, B_53)) | r2_hidden(D_51, B_53) | ~r2_hidden(D_51, A_52))), inference(resolution, [status(thm)], [c_124, c_79])).
% 4.52/1.90  tff(c_147, plain, (r2_hidden('#skF_3', '#skF_4') | ~r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_144])).
% 4.52/1.90  tff(c_150, plain, (r2_hidden('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_147])).
% 4.52/1.90  tff(c_42, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.52/1.90  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.52/1.90  tff(c_28, plain, (![A_16, C_18, B_17]: (r2_hidden(A_16, k1_relat_1(k7_relat_1(C_18, B_17))) | ~r2_hidden(A_16, k1_relat_1(C_18)) | ~r2_hidden(A_16, B_17) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.52/1.90  tff(c_607, plain, (![C_95, B_96, A_97]: (k1_funct_1(k7_relat_1(C_95, B_96), A_97)=k1_funct_1(C_95, A_97) | ~r2_hidden(A_97, k1_relat_1(k7_relat_1(C_95, B_96))) | ~v1_funct_1(C_95) | ~v1_relat_1(C_95))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.52/1.90  tff(c_2903, plain, (![C_156, B_157, A_158]: (k1_funct_1(k7_relat_1(C_156, B_157), A_158)=k1_funct_1(C_156, A_158) | ~v1_funct_1(C_156) | ~r2_hidden(A_158, k1_relat_1(C_156)) | ~r2_hidden(A_158, B_157) | ~v1_relat_1(C_156))), inference(resolution, [status(thm)], [c_28, c_607])).
% 4.52/1.90  tff(c_2931, plain, (![B_157]: (k1_funct_1(k7_relat_1('#skF_5', B_157), '#skF_3')=k1_funct_1('#skF_5', '#skF_3') | ~v1_funct_1('#skF_5') | ~r2_hidden('#skF_3', B_157) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_97, c_2903])).
% 4.52/1.90  tff(c_3157, plain, (![B_162]: (k1_funct_1(k7_relat_1('#skF_5', B_162), '#skF_3')=k1_funct_1('#skF_5', '#skF_3') | ~r2_hidden('#skF_3', B_162))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_2931])).
% 4.52/1.90  tff(c_36, plain, (k1_funct_1(k7_relat_1('#skF_5', '#skF_4'), '#skF_3')!=k1_funct_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.52/1.90  tff(c_3163, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3157, c_36])).
% 4.52/1.90  tff(c_3171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_150, c_3163])).
% 4.52/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.52/1.90  
% 4.52/1.90  Inference rules
% 4.52/1.90  ----------------------
% 4.52/1.90  #Ref     : 0
% 4.52/1.90  #Sup     : 886
% 4.52/1.90  #Fact    : 0
% 4.52/1.90  #Define  : 0
% 4.52/1.90  #Split   : 0
% 4.52/1.90  #Chain   : 0
% 4.52/1.90  #Close   : 0
% 4.52/1.90  
% 4.52/1.90  Ordering : KBO
% 4.52/1.90  
% 4.52/1.90  Simplification rules
% 4.52/1.90  ----------------------
% 4.52/1.90  #Subsume      : 302
% 4.52/1.90  #Demod        : 67
% 4.52/1.90  #Tautology    : 51
% 4.52/1.90  #SimpNegUnit  : 12
% 4.52/1.90  #BackRed      : 0
% 4.52/1.90  
% 4.52/1.90  #Partial instantiations: 0
% 4.52/1.90  #Strategies tried      : 1
% 4.52/1.90  
% 4.52/1.90  Timing (in seconds)
% 4.52/1.90  ----------------------
% 4.52/1.91  Preprocessing        : 0.32
% 4.52/1.91  Parsing              : 0.17
% 4.52/1.91  CNF conversion       : 0.02
% 4.52/1.91  Main loop            : 0.80
% 4.52/1.91  Inferencing          : 0.26
% 4.52/1.91  Reduction            : 0.29
% 4.52/1.91  Demodulation         : 0.23
% 4.52/1.91  BG Simplification    : 0.04
% 4.52/1.91  Subsumption          : 0.17
% 4.52/1.91  Abstraction          : 0.04
% 4.52/1.91  MUC search           : 0.00
% 4.52/1.91  Cooper               : 0.00
% 4.52/1.91  Total                : 1.15
% 4.52/1.91  Index Insertion      : 0.00
% 4.52/1.91  Index Deletion       : 0.00
% 4.52/1.91  Index Matching       : 0.00
% 4.52/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
