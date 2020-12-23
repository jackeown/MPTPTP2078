%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:36 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   47 (  90 expanded)
%              Number of leaves         :   19 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :   85 ( 258 expanded)
%              Number of equality atoms :   10 (  34 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_wellord1 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ~ ( v2_wellord1(A)
            & k3_relat_1(A) != k1_xboole_0
            & ! [B] :
                ~ ( r2_hidden(B,k3_relat_1(A))
                  & ! [C] :
                      ( r2_hidden(C,k3_relat_1(A))
                     => r2_hidden(k4_tarski(B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ~ ( r1_tarski(B,k3_relat_1(A))
              & B != k1_xboole_0
              & ! [C] :
                  ~ ( r2_hidden(C,B)
                    & ! [D] :
                        ( r2_hidden(D,B)
                       => r2_hidden(k4_tarski(C,D),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord1)).

tff(c_18,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6,plain,(
    ! [A_1,B_11] :
      ( r2_hidden(k4_tarski('#skF_1'(A_1,B_11),'#skF_2'(A_1,B_11)),A_1)
      | r1_tarski(A_1,B_11)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_27,plain,(
    ! [A_46,B_47] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_46,B_47),'#skF_2'(A_46,B_47)),B_47)
      | r1_tarski(A_46,B_47)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(resolution,[status(thm)],[c_6,c_27])).

tff(c_8,plain,(
    ! [A_18,B_20] :
      ( r1_tarski(k3_relat_1(A_18),k3_relat_1(B_20))
      | ~ r1_tarski(A_18,B_20)
      | ~ v1_relat_1(B_20)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14,plain,(
    k3_relat_1('#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_16,plain,(
    v2_wellord1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_12,plain,(
    ! [A_21,B_29] :
      ( r2_hidden('#skF_3'(A_21,B_29),B_29)
      | k1_xboole_0 = B_29
      | ~ r1_tarski(B_29,k3_relat_1(A_21))
      | ~ v2_wellord1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    ! [B_38] :
      ( r2_hidden('#skF_5'(B_38),k3_relat_1('#skF_4'))
      | ~ r2_hidden(B_38,k3_relat_1('#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_48,plain,(
    ! [A_58,B_59,D_60] :
      ( r2_hidden(k4_tarski('#skF_3'(A_58,B_59),D_60),A_58)
      | ~ r2_hidden(D_60,B_59)
      | k1_xboole_0 = B_59
      | ~ r1_tarski(B_59,k3_relat_1(A_58))
      | ~ v2_wellord1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    ! [B_38] :
      ( ~ r2_hidden(k4_tarski(B_38,'#skF_5'(B_38)),'#skF_4')
      | ~ r2_hidden(B_38,k3_relat_1('#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_54,plain,(
    ! [B_59] :
      ( ~ r2_hidden('#skF_3'('#skF_4',B_59),k3_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_5'('#skF_3'('#skF_4',B_59)),B_59)
      | k1_xboole_0 = B_59
      | ~ r1_tarski(B_59,k3_relat_1('#skF_4'))
      | ~ v2_wellord1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_20])).

tff(c_59,plain,(
    ! [B_61] :
      ( ~ r2_hidden('#skF_3'('#skF_4',B_61),k3_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_5'('#skF_3'('#skF_4',B_61)),B_61)
      | k1_xboole_0 = B_61
      | ~ r1_tarski(B_61,k3_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_54])).

tff(c_63,plain,
    ( k3_relat_1('#skF_4') = k1_xboole_0
    | ~ r1_tarski(k3_relat_1('#skF_4'),k3_relat_1('#skF_4'))
    | ~ r2_hidden('#skF_3'('#skF_4',k3_relat_1('#skF_4')),k3_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_22,c_59])).

tff(c_66,plain,
    ( ~ r1_tarski(k3_relat_1('#skF_4'),k3_relat_1('#skF_4'))
    | ~ r2_hidden('#skF_3'('#skF_4',k3_relat_1('#skF_4')),k3_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_63])).

tff(c_67,plain,(
    ~ r2_hidden('#skF_3'('#skF_4',k3_relat_1('#skF_4')),k3_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_79,plain,
    ( k3_relat_1('#skF_4') = k1_xboole_0
    | ~ r1_tarski(k3_relat_1('#skF_4'),k3_relat_1('#skF_4'))
    | ~ v2_wellord1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_67])).

tff(c_82,plain,
    ( k3_relat_1('#skF_4') = k1_xboole_0
    | ~ r1_tarski(k3_relat_1('#skF_4'),k3_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_79])).

tff(c_83,plain,(
    ~ r1_tarski(k3_relat_1('#skF_4'),k3_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_82])).

tff(c_89,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_83])).

tff(c_93,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_89])).

tff(c_104,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_93])).

tff(c_108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_104])).

tff(c_109,plain,(
    ~ r1_tarski(k3_relat_1('#skF_4'),k3_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_116,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_109])).

tff(c_120,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_116])).

tff(c_123,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_120])).

tff(c_127,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_123])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:22:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.23  
% 1.82/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.23  %$ r2_hidden > r1_tarski > v2_wellord1 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.82/1.23  
% 1.82/1.23  %Foreground sorts:
% 1.82/1.23  
% 1.82/1.23  
% 1.82/1.23  %Background operators:
% 1.82/1.23  
% 1.82/1.23  
% 1.82/1.23  %Foreground operators:
% 1.82/1.23  tff('#skF_5', type, '#skF_5': $i > $i).
% 1.82/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.82/1.23  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.82/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.82/1.23  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.82/1.23  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.82/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.82/1.23  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 1.82/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.82/1.23  tff('#skF_4', type, '#skF_4': $i).
% 1.82/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.82/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.82/1.23  
% 1.82/1.24  tff(f_82, negated_conjecture, ~(![A]: (v1_relat_1(A) => ~((v2_wellord1(A) & ~(k3_relat_1(A) = k1_xboole_0)) & (![B]: ~(r2_hidden(B, k3_relat_1(A)) & (![C]: (r2_hidden(C, k3_relat_1(A)) => r2_hidden(k4_tarski(B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_wellord1)).
% 1.82/1.24  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 1.82/1.24  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 1.82/1.24  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) => (![B]: ~((r1_tarski(B, k3_relat_1(A)) & ~(B = k1_xboole_0)) & (![C]: ~(r2_hidden(C, B) & (![D]: (r2_hidden(D, B) => r2_hidden(k4_tarski(C, D), A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_wellord1)).
% 1.82/1.24  tff(c_18, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.82/1.24  tff(c_6, plain, (![A_1, B_11]: (r2_hidden(k4_tarski('#skF_1'(A_1, B_11), '#skF_2'(A_1, B_11)), A_1) | r1_tarski(A_1, B_11) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.82/1.24  tff(c_27, plain, (![A_46, B_47]: (~r2_hidden(k4_tarski('#skF_1'(A_46, B_47), '#skF_2'(A_46, B_47)), B_47) | r1_tarski(A_46, B_47) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.82/1.24  tff(c_32, plain, (![A_1]: (r1_tarski(A_1, A_1) | ~v1_relat_1(A_1))), inference(resolution, [status(thm)], [c_6, c_27])).
% 1.82/1.24  tff(c_8, plain, (![A_18, B_20]: (r1_tarski(k3_relat_1(A_18), k3_relat_1(B_20)) | ~r1_tarski(A_18, B_20) | ~v1_relat_1(B_20) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.82/1.24  tff(c_14, plain, (k3_relat_1('#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.82/1.24  tff(c_16, plain, (v2_wellord1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.82/1.24  tff(c_12, plain, (![A_21, B_29]: (r2_hidden('#skF_3'(A_21, B_29), B_29) | k1_xboole_0=B_29 | ~r1_tarski(B_29, k3_relat_1(A_21)) | ~v2_wellord1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.82/1.24  tff(c_22, plain, (![B_38]: (r2_hidden('#skF_5'(B_38), k3_relat_1('#skF_4')) | ~r2_hidden(B_38, k3_relat_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.82/1.24  tff(c_48, plain, (![A_58, B_59, D_60]: (r2_hidden(k4_tarski('#skF_3'(A_58, B_59), D_60), A_58) | ~r2_hidden(D_60, B_59) | k1_xboole_0=B_59 | ~r1_tarski(B_59, k3_relat_1(A_58)) | ~v2_wellord1(A_58) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.82/1.24  tff(c_20, plain, (![B_38]: (~r2_hidden(k4_tarski(B_38, '#skF_5'(B_38)), '#skF_4') | ~r2_hidden(B_38, k3_relat_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.82/1.24  tff(c_54, plain, (![B_59]: (~r2_hidden('#skF_3'('#skF_4', B_59), k3_relat_1('#skF_4')) | ~r2_hidden('#skF_5'('#skF_3'('#skF_4', B_59)), B_59) | k1_xboole_0=B_59 | ~r1_tarski(B_59, k3_relat_1('#skF_4')) | ~v2_wellord1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_20])).
% 1.82/1.24  tff(c_59, plain, (![B_61]: (~r2_hidden('#skF_3'('#skF_4', B_61), k3_relat_1('#skF_4')) | ~r2_hidden('#skF_5'('#skF_3'('#skF_4', B_61)), B_61) | k1_xboole_0=B_61 | ~r1_tarski(B_61, k3_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_54])).
% 1.82/1.24  tff(c_63, plain, (k3_relat_1('#skF_4')=k1_xboole_0 | ~r1_tarski(k3_relat_1('#skF_4'), k3_relat_1('#skF_4')) | ~r2_hidden('#skF_3'('#skF_4', k3_relat_1('#skF_4')), k3_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_22, c_59])).
% 1.82/1.24  tff(c_66, plain, (~r1_tarski(k3_relat_1('#skF_4'), k3_relat_1('#skF_4')) | ~r2_hidden('#skF_3'('#skF_4', k3_relat_1('#skF_4')), k3_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_14, c_63])).
% 1.82/1.24  tff(c_67, plain, (~r2_hidden('#skF_3'('#skF_4', k3_relat_1('#skF_4')), k3_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_66])).
% 1.82/1.24  tff(c_79, plain, (k3_relat_1('#skF_4')=k1_xboole_0 | ~r1_tarski(k3_relat_1('#skF_4'), k3_relat_1('#skF_4')) | ~v2_wellord1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_67])).
% 1.82/1.24  tff(c_82, plain, (k3_relat_1('#skF_4')=k1_xboole_0 | ~r1_tarski(k3_relat_1('#skF_4'), k3_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_79])).
% 1.82/1.24  tff(c_83, plain, (~r1_tarski(k3_relat_1('#skF_4'), k3_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_14, c_82])).
% 1.82/1.24  tff(c_89, plain, (~r1_tarski('#skF_4', '#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_83])).
% 1.82/1.24  tff(c_93, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_89])).
% 1.82/1.24  tff(c_104, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_93])).
% 1.82/1.24  tff(c_108, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_104])).
% 1.82/1.24  tff(c_109, plain, (~r1_tarski(k3_relat_1('#skF_4'), k3_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_66])).
% 1.82/1.24  tff(c_116, plain, (~r1_tarski('#skF_4', '#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_109])).
% 1.82/1.24  tff(c_120, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_116])).
% 1.82/1.24  tff(c_123, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_120])).
% 1.82/1.24  tff(c_127, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_123])).
% 1.82/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.24  
% 1.82/1.24  Inference rules
% 1.82/1.24  ----------------------
% 1.82/1.24  #Ref     : 0
% 1.82/1.24  #Sup     : 17
% 1.82/1.24  #Fact    : 0
% 1.82/1.24  #Define  : 0
% 1.82/1.24  #Split   : 1
% 1.82/1.24  #Chain   : 0
% 1.82/1.24  #Close   : 0
% 1.82/1.24  
% 1.82/1.24  Ordering : KBO
% 1.82/1.24  
% 1.82/1.24  Simplification rules
% 1.82/1.24  ----------------------
% 1.82/1.24  #Subsume      : 0
% 1.82/1.24  #Demod        : 8
% 1.82/1.24  #Tautology    : 1
% 1.82/1.24  #SimpNegUnit  : 3
% 1.82/1.24  #BackRed      : 0
% 1.82/1.24  
% 1.82/1.24  #Partial instantiations: 0
% 1.82/1.24  #Strategies tried      : 1
% 1.82/1.24  
% 1.82/1.24  Timing (in seconds)
% 1.82/1.24  ----------------------
% 1.82/1.25  Preprocessing        : 0.29
% 1.82/1.25  Parsing              : 0.16
% 1.82/1.25  CNF conversion       : 0.02
% 1.82/1.25  Main loop            : 0.17
% 1.82/1.25  Inferencing          : 0.08
% 1.82/1.25  Reduction            : 0.04
% 1.82/1.25  Demodulation         : 0.03
% 1.82/1.25  BG Simplification    : 0.01
% 1.82/1.25  Subsumption          : 0.03
% 1.82/1.25  Abstraction          : 0.01
% 1.82/1.25  MUC search           : 0.00
% 1.82/1.25  Cooper               : 0.00
% 1.82/1.25  Total                : 0.49
% 1.82/1.25  Index Insertion      : 0.00
% 1.82/1.25  Index Deletion       : 0.00
% 1.82/1.25  Index Matching       : 0.00
% 1.82/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
