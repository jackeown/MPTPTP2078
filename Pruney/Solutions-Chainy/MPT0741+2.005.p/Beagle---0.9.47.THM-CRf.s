%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:06 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   50 (  96 expanded)
%              Number of leaves         :   17 (  39 expanded)
%              Depth                    :    6
%              Number of atoms          :   84 ( 229 expanded)
%              Number of equality atoms :    9 (  17 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_2 > #skF_1 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_55,axiom,(
    ! [A] :
      ( v2_ordinal1(A)
    <=> ! [B,C] :
          ~ ( r2_hidden(B,A)
            & r2_hidden(C,A)
            & ~ r2_hidden(B,C)
            & B != C
            & ~ r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_ordinal1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( ! [B] :
            ( r2_hidden(B,A)
           => ( v3_ordinal1(B)
              & r1_tarski(B,A) ) )
       => v3_ordinal1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_ordinal1)).

tff(f_31,axiom,(
    ! [A] :
      ( ( v1_ordinal1(A)
        & v2_ordinal1(A) )
     => v3_ordinal1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_ordinal1)).

tff(f_70,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(c_14,plain,(
    ! [A_6] :
      ( '#skF_2'(A_6) != '#skF_3'(A_6)
      | v2_ordinal1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_43,plain,(
    ! [A_22] :
      ( r2_hidden('#skF_1'(A_22),A_22)
      | v1_ordinal1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_28,plain,(
    ! [B_17] :
      ( v3_ordinal1(B_17)
      | ~ r2_hidden(B_17,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_53,plain,
    ( v3_ordinal1('#skF_1'('#skF_4'))
    | v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_43,c_28])).

tff(c_55,plain,(
    v1_ordinal1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_53])).

tff(c_32,plain,(
    ! [A_21] :
      ( r2_hidden('#skF_2'(A_21),A_21)
      | v2_ordinal1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_42,plain,
    ( v3_ordinal1('#skF_2'('#skF_4'))
    | v2_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_28])).

tff(c_54,plain,(
    v2_ordinal1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_59,plain,(
    ! [A_24] :
      ( v3_ordinal1(A_24)
      | ~ v2_ordinal1(A_24)
      | ~ v1_ordinal1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_62,plain,
    ( ~ v2_ordinal1('#skF_4')
    | ~ v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_59,c_24])).

tff(c_66,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_54,c_62])).

tff(c_68,plain,(
    ~ v1_ordinal1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_26,plain,(
    ! [B_17] :
      ( r1_tarski(B_17,'#skF_4')
      | ~ r2_hidden(B_17,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_52,plain,
    ( r1_tarski('#skF_1'('#skF_4'),'#skF_4')
    | v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_43,c_26])).

tff(c_91,plain,(
    r1_tarski('#skF_1'('#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_52])).

tff(c_6,plain,(
    ! [A_2] :
      ( ~ r1_tarski('#skF_1'(A_2),A_2)
      | v1_ordinal1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_94,plain,(
    v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_91,c_6])).

tff(c_98,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_94])).

tff(c_100,plain,(
    ~ v2_ordinal1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_104,plain,(
    '#skF_2'('#skF_4') != '#skF_3'('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_100])).

tff(c_107,plain,(
    ! [A_29] :
      ( r2_hidden('#skF_3'(A_29),A_29)
      | v2_ordinal1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_115,plain,
    ( v3_ordinal1('#skF_3'('#skF_4'))
    | v2_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_107,c_28])).

tff(c_121,plain,(
    v3_ordinal1('#skF_3'('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_115])).

tff(c_99,plain,(
    v3_ordinal1('#skF_2'('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_164,plain,(
    ! [B_37,A_38] :
      ( r2_hidden(B_37,A_38)
      | B_37 = A_38
      | r2_hidden(A_38,B_37)
      | ~ v3_ordinal1(B_37)
      | ~ v3_ordinal1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_16,plain,(
    ! [A_6] :
      ( ~ r2_hidden('#skF_2'(A_6),'#skF_3'(A_6))
      | v2_ordinal1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_272,plain,(
    ! [A_46] :
      ( v2_ordinal1(A_46)
      | '#skF_2'(A_46) = '#skF_3'(A_46)
      | r2_hidden('#skF_3'(A_46),'#skF_2'(A_46))
      | ~ v3_ordinal1('#skF_2'(A_46))
      | ~ v3_ordinal1('#skF_3'(A_46)) ) ),
    inference(resolution,[status(thm)],[c_164,c_16])).

tff(c_12,plain,(
    ! [A_6] :
      ( ~ r2_hidden('#skF_3'(A_6),'#skF_2'(A_6))
      | v2_ordinal1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_284,plain,(
    ! [A_47] :
      ( v2_ordinal1(A_47)
      | '#skF_2'(A_47) = '#skF_3'(A_47)
      | ~ v3_ordinal1('#skF_2'(A_47))
      | ~ v3_ordinal1('#skF_3'(A_47)) ) ),
    inference(resolution,[status(thm)],[c_272,c_12])).

tff(c_290,plain,
    ( v2_ordinal1('#skF_4')
    | '#skF_2'('#skF_4') = '#skF_3'('#skF_4')
    | ~ v3_ordinal1('#skF_3'('#skF_4')) ),
    inference(resolution,[status(thm)],[c_99,c_284])).

tff(c_294,plain,
    ( v2_ordinal1('#skF_4')
    | '#skF_2'('#skF_4') = '#skF_3'('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_290])).

tff(c_296,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_100,c_294])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:42:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.25  
% 2.11/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.25  %$ r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_2 > #skF_1 > #skF_4 > #skF_3
% 2.11/1.25  
% 2.11/1.25  %Foreground sorts:
% 2.11/1.25  
% 2.11/1.25  
% 2.11/1.25  %Background operators:
% 2.11/1.25  
% 2.11/1.25  
% 2.11/1.25  %Foreground operators:
% 2.11/1.25  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.11/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.25  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 2.11/1.25  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.11/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.25  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.11/1.25  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 2.11/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.11/1.25  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.11/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.25  
% 2.11/1.26  tff(f_55, axiom, (![A]: (v2_ordinal1(A) <=> (![B, C]: ~((((r2_hidden(B, A) & r2_hidden(C, A)) & ~r2_hidden(B, C)) & ~(B = C)) & ~r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_ordinal1)).
% 2.11/1.26  tff(f_38, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 2.11/1.26  tff(f_80, negated_conjecture, ~(![A]: ((![B]: (r2_hidden(B, A) => (v3_ordinal1(B) & r1_tarski(B, A)))) => v3_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_ordinal1)).
% 2.11/1.26  tff(f_31, axiom, (![A]: ((v1_ordinal1(A) & v2_ordinal1(A)) => v3_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_ordinal1)).
% 2.11/1.26  tff(f_70, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 2.11/1.26  tff(c_14, plain, (![A_6]: ('#skF_2'(A_6)!='#skF_3'(A_6) | v2_ordinal1(A_6))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.11/1.26  tff(c_43, plain, (![A_22]: (r2_hidden('#skF_1'(A_22), A_22) | v1_ordinal1(A_22))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.11/1.26  tff(c_28, plain, (![B_17]: (v3_ordinal1(B_17) | ~r2_hidden(B_17, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.11/1.26  tff(c_53, plain, (v3_ordinal1('#skF_1'('#skF_4')) | v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_43, c_28])).
% 2.11/1.26  tff(c_55, plain, (v1_ordinal1('#skF_4')), inference(splitLeft, [status(thm)], [c_53])).
% 2.11/1.26  tff(c_32, plain, (![A_21]: (r2_hidden('#skF_2'(A_21), A_21) | v2_ordinal1(A_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.11/1.26  tff(c_42, plain, (v3_ordinal1('#skF_2'('#skF_4')) | v2_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_28])).
% 2.11/1.26  tff(c_54, plain, (v2_ordinal1('#skF_4')), inference(splitLeft, [status(thm)], [c_42])).
% 2.11/1.26  tff(c_59, plain, (![A_24]: (v3_ordinal1(A_24) | ~v2_ordinal1(A_24) | ~v1_ordinal1(A_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.11/1.26  tff(c_24, plain, (~v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.11/1.26  tff(c_62, plain, (~v2_ordinal1('#skF_4') | ~v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_59, c_24])).
% 2.11/1.26  tff(c_66, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_54, c_62])).
% 2.11/1.26  tff(c_68, plain, (~v1_ordinal1('#skF_4')), inference(splitRight, [status(thm)], [c_53])).
% 2.11/1.26  tff(c_26, plain, (![B_17]: (r1_tarski(B_17, '#skF_4') | ~r2_hidden(B_17, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.11/1.26  tff(c_52, plain, (r1_tarski('#skF_1'('#skF_4'), '#skF_4') | v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_43, c_26])).
% 2.11/1.26  tff(c_91, plain, (r1_tarski('#skF_1'('#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_68, c_52])).
% 2.11/1.26  tff(c_6, plain, (![A_2]: (~r1_tarski('#skF_1'(A_2), A_2) | v1_ordinal1(A_2))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.11/1.26  tff(c_94, plain, (v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_91, c_6])).
% 2.11/1.26  tff(c_98, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_94])).
% 2.11/1.26  tff(c_100, plain, (~v2_ordinal1('#skF_4')), inference(splitRight, [status(thm)], [c_42])).
% 2.11/1.26  tff(c_104, plain, ('#skF_2'('#skF_4')!='#skF_3'('#skF_4')), inference(resolution, [status(thm)], [c_14, c_100])).
% 2.11/1.26  tff(c_107, plain, (![A_29]: (r2_hidden('#skF_3'(A_29), A_29) | v2_ordinal1(A_29))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.11/1.26  tff(c_115, plain, (v3_ordinal1('#skF_3'('#skF_4')) | v2_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_107, c_28])).
% 2.11/1.26  tff(c_121, plain, (v3_ordinal1('#skF_3'('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_100, c_115])).
% 2.11/1.26  tff(c_99, plain, (v3_ordinal1('#skF_2'('#skF_4'))), inference(splitRight, [status(thm)], [c_42])).
% 2.11/1.26  tff(c_164, plain, (![B_37, A_38]: (r2_hidden(B_37, A_38) | B_37=A_38 | r2_hidden(A_38, B_37) | ~v3_ordinal1(B_37) | ~v3_ordinal1(A_38))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.11/1.26  tff(c_16, plain, (![A_6]: (~r2_hidden('#skF_2'(A_6), '#skF_3'(A_6)) | v2_ordinal1(A_6))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.11/1.26  tff(c_272, plain, (![A_46]: (v2_ordinal1(A_46) | '#skF_2'(A_46)='#skF_3'(A_46) | r2_hidden('#skF_3'(A_46), '#skF_2'(A_46)) | ~v3_ordinal1('#skF_2'(A_46)) | ~v3_ordinal1('#skF_3'(A_46)))), inference(resolution, [status(thm)], [c_164, c_16])).
% 2.11/1.26  tff(c_12, plain, (![A_6]: (~r2_hidden('#skF_3'(A_6), '#skF_2'(A_6)) | v2_ordinal1(A_6))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.11/1.26  tff(c_284, plain, (![A_47]: (v2_ordinal1(A_47) | '#skF_2'(A_47)='#skF_3'(A_47) | ~v3_ordinal1('#skF_2'(A_47)) | ~v3_ordinal1('#skF_3'(A_47)))), inference(resolution, [status(thm)], [c_272, c_12])).
% 2.11/1.26  tff(c_290, plain, (v2_ordinal1('#skF_4') | '#skF_2'('#skF_4')='#skF_3'('#skF_4') | ~v3_ordinal1('#skF_3'('#skF_4'))), inference(resolution, [status(thm)], [c_99, c_284])).
% 2.11/1.26  tff(c_294, plain, (v2_ordinal1('#skF_4') | '#skF_2'('#skF_4')='#skF_3'('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_290])).
% 2.11/1.26  tff(c_296, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_100, c_294])).
% 2.11/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.26  
% 2.11/1.26  Inference rules
% 2.11/1.26  ----------------------
% 2.11/1.26  #Ref     : 0
% 2.11/1.26  #Sup     : 42
% 2.11/1.26  #Fact    : 4
% 2.11/1.26  #Define  : 0
% 2.11/1.26  #Split   : 4
% 2.11/1.26  #Chain   : 0
% 2.11/1.26  #Close   : 0
% 2.11/1.26  
% 2.11/1.26  Ordering : KBO
% 2.11/1.26  
% 2.11/1.26  Simplification rules
% 2.11/1.26  ----------------------
% 2.11/1.26  #Subsume      : 10
% 2.11/1.26  #Demod        : 10
% 2.11/1.26  #Tautology    : 14
% 2.11/1.26  #SimpNegUnit  : 6
% 2.11/1.26  #BackRed      : 0
% 2.11/1.26  
% 2.11/1.26  #Partial instantiations: 0
% 2.11/1.26  #Strategies tried      : 1
% 2.11/1.26  
% 2.11/1.26  Timing (in seconds)
% 2.11/1.26  ----------------------
% 2.11/1.26  Preprocessing        : 0.29
% 2.11/1.26  Parsing              : 0.15
% 2.11/1.26  CNF conversion       : 0.02
% 2.11/1.26  Main loop            : 0.21
% 2.11/1.26  Inferencing          : 0.09
% 2.11/1.26  Reduction            : 0.05
% 2.11/1.26  Demodulation         : 0.03
% 2.11/1.26  BG Simplification    : 0.02
% 2.11/1.26  Subsumption          : 0.04
% 2.11/1.26  Abstraction          : 0.01
% 2.11/1.26  MUC search           : 0.00
% 2.11/1.26  Cooper               : 0.00
% 2.11/1.26  Total                : 0.53
% 2.11/1.26  Index Insertion      : 0.00
% 2.11/1.26  Index Deletion       : 0.00
% 2.11/1.26  Index Matching       : 0.00
% 2.11/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
