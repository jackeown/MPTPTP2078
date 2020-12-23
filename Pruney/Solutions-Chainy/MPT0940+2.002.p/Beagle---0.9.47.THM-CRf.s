%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:31 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   50 (  83 expanded)
%              Number of leaves         :   21 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :  103 ( 187 expanded)
%              Number of equality atoms :   15 (  27 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v4_relat_2 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_wellord2 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_67,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v4_relat_2(A)
      <=> ! [B,C] :
            ( ( r2_hidden(k4_tarski(B,C),A)
              & r2_hidden(k4_tarski(C,B),A) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_wellord1)).

tff(f_70,negated_conjecture,(
    ~ ! [A] : v4_relat_2(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_wellord2)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_38,plain,(
    ! [A_21] : v1_relat_1(k1_wellord2(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_66,plain,(
    ! [A_27] :
      ( '#skF_2'(A_27) != '#skF_1'(A_27)
      | v4_relat_2(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_40,plain,(
    ~ v4_relat_2(k1_wellord2('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_69,plain,
    ( '#skF_2'(k1_wellord2('#skF_5')) != '#skF_1'(k1_wellord2('#skF_5'))
    | ~ v1_relat_1(k1_wellord2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_66,c_40])).

tff(c_72,plain,(
    '#skF_2'(k1_wellord2('#skF_5')) != '#skF_1'(k1_wellord2('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_69])).

tff(c_32,plain,(
    ! [A_13] :
      ( k3_relat_1(k1_wellord2(A_13)) = A_13
      | ~ v1_relat_1(k1_wellord2(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_46,plain,(
    ! [A_13] : k3_relat_1(k1_wellord2(A_13)) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32])).

tff(c_16,plain,(
    ! [A_6] :
      ( r2_hidden(k4_tarski('#skF_2'(A_6),'#skF_1'(A_6)),A_6)
      | v4_relat_2(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_75,plain,(
    ! [B_30,C_31,A_32] :
      ( r2_hidden(B_30,k3_relat_1(C_31))
      | ~ r2_hidden(k4_tarski(A_32,B_30),C_31)
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_91,plain,(
    ! [A_35] :
      ( r2_hidden('#skF_1'(A_35),k3_relat_1(A_35))
      | v4_relat_2(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(resolution,[status(thm)],[c_16,c_75])).

tff(c_94,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_1'(k1_wellord2(A_13)),A_13)
      | v4_relat_2(k1_wellord2(A_13))
      | ~ v1_relat_1(k1_wellord2(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_91])).

tff(c_96,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_1'(k1_wellord2(A_13)),A_13)
      | v4_relat_2(k1_wellord2(A_13)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_94])).

tff(c_18,plain,(
    ! [A_6] :
      ( r2_hidden(k4_tarski('#skF_1'(A_6),'#skF_2'(A_6)),A_6)
      | v4_relat_2(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_84,plain,(
    ! [A_33] :
      ( r2_hidden('#skF_2'(A_33),k3_relat_1(A_33))
      | v4_relat_2(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(resolution,[status(thm)],[c_18,c_75])).

tff(c_87,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_2'(k1_wellord2(A_13)),A_13)
      | v4_relat_2(k1_wellord2(A_13))
      | ~ v1_relat_1(k1_wellord2(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_84])).

tff(c_89,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_2'(k1_wellord2(A_13)),A_13)
      | v4_relat_2(k1_wellord2(A_13)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_87])).

tff(c_36,plain,(
    ! [C_19,D_20,A_13] :
      ( r1_tarski(C_19,D_20)
      | ~ r2_hidden(k4_tarski(C_19,D_20),k1_wellord2(A_13))
      | ~ r2_hidden(D_20,A_13)
      | ~ r2_hidden(C_19,A_13)
      | ~ v1_relat_1(k1_wellord2(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_142,plain,(
    ! [C_45,D_46,A_47] :
      ( r1_tarski(C_45,D_46)
      | ~ r2_hidden(k4_tarski(C_45,D_46),k1_wellord2(A_47))
      | ~ r2_hidden(D_46,A_47)
      | ~ r2_hidden(C_45,A_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36])).

tff(c_149,plain,(
    ! [A_47] :
      ( r1_tarski('#skF_1'(k1_wellord2(A_47)),'#skF_2'(k1_wellord2(A_47)))
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_47)),A_47)
      | ~ r2_hidden('#skF_1'(k1_wellord2(A_47)),A_47)
      | v4_relat_2(k1_wellord2(A_47))
      | ~ v1_relat_1(k1_wellord2(A_47)) ) ),
    inference(resolution,[status(thm)],[c_18,c_142])).

tff(c_157,plain,(
    ! [A_47] :
      ( r1_tarski('#skF_1'(k1_wellord2(A_47)),'#skF_2'(k1_wellord2(A_47)))
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_47)),A_47)
      | ~ r2_hidden('#skF_1'(k1_wellord2(A_47)),A_47)
      | v4_relat_2(k1_wellord2(A_47)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_149])).

tff(c_153,plain,(
    ! [A_47] :
      ( r1_tarski('#skF_2'(k1_wellord2(A_47)),'#skF_1'(k1_wellord2(A_47)))
      | ~ r2_hidden('#skF_1'(k1_wellord2(A_47)),A_47)
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_47)),A_47)
      | v4_relat_2(k1_wellord2(A_47))
      | ~ v1_relat_1(k1_wellord2(A_47)) ) ),
    inference(resolution,[status(thm)],[c_16,c_142])).

tff(c_196,plain,(
    ! [A_55] :
      ( r1_tarski('#skF_2'(k1_wellord2(A_55)),'#skF_1'(k1_wellord2(A_55)))
      | ~ r2_hidden('#skF_1'(k1_wellord2(A_55)),A_55)
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_55)),A_55)
      | v4_relat_2(k1_wellord2(A_55)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_153])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_276,plain,(
    ! [A_59] :
      ( '#skF_2'(k1_wellord2(A_59)) = '#skF_1'(k1_wellord2(A_59))
      | ~ r1_tarski('#skF_1'(k1_wellord2(A_59)),'#skF_2'(k1_wellord2(A_59)))
      | ~ r2_hidden('#skF_1'(k1_wellord2(A_59)),A_59)
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_59)),A_59)
      | v4_relat_2(k1_wellord2(A_59)) ) ),
    inference(resolution,[status(thm)],[c_196,c_2])).

tff(c_281,plain,(
    ! [A_60] :
      ( '#skF_2'(k1_wellord2(A_60)) = '#skF_1'(k1_wellord2(A_60))
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_60)),A_60)
      | ~ r2_hidden('#skF_1'(k1_wellord2(A_60)),A_60)
      | v4_relat_2(k1_wellord2(A_60)) ) ),
    inference(resolution,[status(thm)],[c_157,c_276])).

tff(c_286,plain,(
    ! [A_61] :
      ( '#skF_2'(k1_wellord2(A_61)) = '#skF_1'(k1_wellord2(A_61))
      | ~ r2_hidden('#skF_1'(k1_wellord2(A_61)),A_61)
      | v4_relat_2(k1_wellord2(A_61)) ) ),
    inference(resolution,[status(thm)],[c_89,c_281])).

tff(c_291,plain,(
    ! [A_62] :
      ( '#skF_2'(k1_wellord2(A_62)) = '#skF_1'(k1_wellord2(A_62))
      | v4_relat_2(k1_wellord2(A_62)) ) ),
    inference(resolution,[status(thm)],[c_96,c_286])).

tff(c_294,plain,(
    '#skF_2'(k1_wellord2('#skF_5')) = '#skF_1'(k1_wellord2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_291,c_40])).

tff(c_298,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_294])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:59:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.29  
% 2.08/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.29  %$ r2_hidden > r1_tarski > v4_relat_2 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_wellord2 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4
% 2.08/1.29  
% 2.08/1.29  %Foreground sorts:
% 2.08/1.29  
% 2.08/1.29  
% 2.08/1.29  %Background operators:
% 2.08/1.29  
% 2.08/1.29  
% 2.08/1.29  %Foreground operators:
% 2.08/1.29  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.08/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.29  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.08/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.08/1.29  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.08/1.29  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.08/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.29  tff(v4_relat_2, type, v4_relat_2: $i > $o).
% 2.08/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.08/1.29  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 2.08/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.08/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.29  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.08/1.29  
% 2.08/1.30  tff(f_67, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 2.08/1.30  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (v4_relat_2(A) <=> (![B, C]: ((r2_hidden(k4_tarski(B, C), A) & r2_hidden(k4_tarski(C, B), A)) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_wellord1)).
% 2.08/1.30  tff(f_70, negated_conjecture, ~(![A]: v4_relat_2(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_wellord2)).
% 2.08/1.30  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 2.08/1.30  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 2.08/1.30  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.08/1.30  tff(c_38, plain, (![A_21]: (v1_relat_1(k1_wellord2(A_21)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.08/1.30  tff(c_66, plain, (![A_27]: ('#skF_2'(A_27)!='#skF_1'(A_27) | v4_relat_2(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.08/1.30  tff(c_40, plain, (~v4_relat_2(k1_wellord2('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.08/1.30  tff(c_69, plain, ('#skF_2'(k1_wellord2('#skF_5'))!='#skF_1'(k1_wellord2('#skF_5')) | ~v1_relat_1(k1_wellord2('#skF_5'))), inference(resolution, [status(thm)], [c_66, c_40])).
% 2.08/1.30  tff(c_72, plain, ('#skF_2'(k1_wellord2('#skF_5'))!='#skF_1'(k1_wellord2('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_69])).
% 2.08/1.30  tff(c_32, plain, (![A_13]: (k3_relat_1(k1_wellord2(A_13))=A_13 | ~v1_relat_1(k1_wellord2(A_13)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.08/1.30  tff(c_46, plain, (![A_13]: (k3_relat_1(k1_wellord2(A_13))=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32])).
% 2.08/1.30  tff(c_16, plain, (![A_6]: (r2_hidden(k4_tarski('#skF_2'(A_6), '#skF_1'(A_6)), A_6) | v4_relat_2(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.08/1.30  tff(c_75, plain, (![B_30, C_31, A_32]: (r2_hidden(B_30, k3_relat_1(C_31)) | ~r2_hidden(k4_tarski(A_32, B_30), C_31) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.08/1.30  tff(c_91, plain, (![A_35]: (r2_hidden('#skF_1'(A_35), k3_relat_1(A_35)) | v4_relat_2(A_35) | ~v1_relat_1(A_35))), inference(resolution, [status(thm)], [c_16, c_75])).
% 2.08/1.30  tff(c_94, plain, (![A_13]: (r2_hidden('#skF_1'(k1_wellord2(A_13)), A_13) | v4_relat_2(k1_wellord2(A_13)) | ~v1_relat_1(k1_wellord2(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_91])).
% 2.08/1.30  tff(c_96, plain, (![A_13]: (r2_hidden('#skF_1'(k1_wellord2(A_13)), A_13) | v4_relat_2(k1_wellord2(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_94])).
% 2.08/1.30  tff(c_18, plain, (![A_6]: (r2_hidden(k4_tarski('#skF_1'(A_6), '#skF_2'(A_6)), A_6) | v4_relat_2(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.08/1.30  tff(c_84, plain, (![A_33]: (r2_hidden('#skF_2'(A_33), k3_relat_1(A_33)) | v4_relat_2(A_33) | ~v1_relat_1(A_33))), inference(resolution, [status(thm)], [c_18, c_75])).
% 2.08/1.30  tff(c_87, plain, (![A_13]: (r2_hidden('#skF_2'(k1_wellord2(A_13)), A_13) | v4_relat_2(k1_wellord2(A_13)) | ~v1_relat_1(k1_wellord2(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_84])).
% 2.08/1.30  tff(c_89, plain, (![A_13]: (r2_hidden('#skF_2'(k1_wellord2(A_13)), A_13) | v4_relat_2(k1_wellord2(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_87])).
% 2.08/1.30  tff(c_36, plain, (![C_19, D_20, A_13]: (r1_tarski(C_19, D_20) | ~r2_hidden(k4_tarski(C_19, D_20), k1_wellord2(A_13)) | ~r2_hidden(D_20, A_13) | ~r2_hidden(C_19, A_13) | ~v1_relat_1(k1_wellord2(A_13)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.08/1.30  tff(c_142, plain, (![C_45, D_46, A_47]: (r1_tarski(C_45, D_46) | ~r2_hidden(k4_tarski(C_45, D_46), k1_wellord2(A_47)) | ~r2_hidden(D_46, A_47) | ~r2_hidden(C_45, A_47))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36])).
% 2.08/1.30  tff(c_149, plain, (![A_47]: (r1_tarski('#skF_1'(k1_wellord2(A_47)), '#skF_2'(k1_wellord2(A_47))) | ~r2_hidden('#skF_2'(k1_wellord2(A_47)), A_47) | ~r2_hidden('#skF_1'(k1_wellord2(A_47)), A_47) | v4_relat_2(k1_wellord2(A_47)) | ~v1_relat_1(k1_wellord2(A_47)))), inference(resolution, [status(thm)], [c_18, c_142])).
% 2.08/1.30  tff(c_157, plain, (![A_47]: (r1_tarski('#skF_1'(k1_wellord2(A_47)), '#skF_2'(k1_wellord2(A_47))) | ~r2_hidden('#skF_2'(k1_wellord2(A_47)), A_47) | ~r2_hidden('#skF_1'(k1_wellord2(A_47)), A_47) | v4_relat_2(k1_wellord2(A_47)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_149])).
% 2.08/1.30  tff(c_153, plain, (![A_47]: (r1_tarski('#skF_2'(k1_wellord2(A_47)), '#skF_1'(k1_wellord2(A_47))) | ~r2_hidden('#skF_1'(k1_wellord2(A_47)), A_47) | ~r2_hidden('#skF_2'(k1_wellord2(A_47)), A_47) | v4_relat_2(k1_wellord2(A_47)) | ~v1_relat_1(k1_wellord2(A_47)))), inference(resolution, [status(thm)], [c_16, c_142])).
% 2.08/1.30  tff(c_196, plain, (![A_55]: (r1_tarski('#skF_2'(k1_wellord2(A_55)), '#skF_1'(k1_wellord2(A_55))) | ~r2_hidden('#skF_1'(k1_wellord2(A_55)), A_55) | ~r2_hidden('#skF_2'(k1_wellord2(A_55)), A_55) | v4_relat_2(k1_wellord2(A_55)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_153])).
% 2.08/1.30  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.08/1.30  tff(c_276, plain, (![A_59]: ('#skF_2'(k1_wellord2(A_59))='#skF_1'(k1_wellord2(A_59)) | ~r1_tarski('#skF_1'(k1_wellord2(A_59)), '#skF_2'(k1_wellord2(A_59))) | ~r2_hidden('#skF_1'(k1_wellord2(A_59)), A_59) | ~r2_hidden('#skF_2'(k1_wellord2(A_59)), A_59) | v4_relat_2(k1_wellord2(A_59)))), inference(resolution, [status(thm)], [c_196, c_2])).
% 2.08/1.30  tff(c_281, plain, (![A_60]: ('#skF_2'(k1_wellord2(A_60))='#skF_1'(k1_wellord2(A_60)) | ~r2_hidden('#skF_2'(k1_wellord2(A_60)), A_60) | ~r2_hidden('#skF_1'(k1_wellord2(A_60)), A_60) | v4_relat_2(k1_wellord2(A_60)))), inference(resolution, [status(thm)], [c_157, c_276])).
% 2.08/1.30  tff(c_286, plain, (![A_61]: ('#skF_2'(k1_wellord2(A_61))='#skF_1'(k1_wellord2(A_61)) | ~r2_hidden('#skF_1'(k1_wellord2(A_61)), A_61) | v4_relat_2(k1_wellord2(A_61)))), inference(resolution, [status(thm)], [c_89, c_281])).
% 2.08/1.30  tff(c_291, plain, (![A_62]: ('#skF_2'(k1_wellord2(A_62))='#skF_1'(k1_wellord2(A_62)) | v4_relat_2(k1_wellord2(A_62)))), inference(resolution, [status(thm)], [c_96, c_286])).
% 2.08/1.30  tff(c_294, plain, ('#skF_2'(k1_wellord2('#skF_5'))='#skF_1'(k1_wellord2('#skF_5'))), inference(resolution, [status(thm)], [c_291, c_40])).
% 2.08/1.30  tff(c_298, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_294])).
% 2.08/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.30  
% 2.08/1.30  Inference rules
% 2.08/1.30  ----------------------
% 2.08/1.30  #Ref     : 0
% 2.08/1.30  #Sup     : 45
% 2.08/1.30  #Fact    : 0
% 2.08/1.30  #Define  : 0
% 2.08/1.30  #Split   : 0
% 2.08/1.30  #Chain   : 0
% 2.08/1.30  #Close   : 0
% 2.08/1.30  
% 2.08/1.30  Ordering : KBO
% 2.08/1.30  
% 2.08/1.30  Simplification rules
% 2.08/1.30  ----------------------
% 2.08/1.30  #Subsume      : 9
% 2.08/1.30  #Demod        : 95
% 2.08/1.30  #Tautology    : 28
% 2.08/1.30  #SimpNegUnit  : 1
% 2.08/1.30  #BackRed      : 0
% 2.08/1.30  
% 2.08/1.31  #Partial instantiations: 0
% 2.08/1.31  #Strategies tried      : 1
% 2.08/1.31  
% 2.08/1.31  Timing (in seconds)
% 2.08/1.31  ----------------------
% 2.08/1.31  Preprocessing        : 0.30
% 2.08/1.31  Parsing              : 0.15
% 2.08/1.31  CNF conversion       : 0.02
% 2.08/1.31  Main loop            : 0.23
% 2.08/1.31  Inferencing          : 0.09
% 2.08/1.31  Reduction            : 0.07
% 2.08/1.31  Demodulation         : 0.05
% 2.08/1.31  BG Simplification    : 0.02
% 2.08/1.31  Subsumption          : 0.05
% 2.08/1.31  Abstraction          : 0.02
% 2.08/1.31  MUC search           : 0.00
% 2.08/1.31  Cooper               : 0.00
% 2.08/1.31  Total                : 0.56
% 2.08/1.31  Index Insertion      : 0.00
% 2.08/1.31  Index Deletion       : 0.00
% 2.08/1.31  Index Matching       : 0.00
% 2.08/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
