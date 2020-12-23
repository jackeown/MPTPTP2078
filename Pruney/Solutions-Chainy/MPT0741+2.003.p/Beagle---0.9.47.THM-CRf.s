%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:06 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 103 expanded)
%              Number of leaves         :   20 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :  114 ( 264 expanded)
%              Number of equality atoms :   11 (  20 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_2 > #skF_1 > #skF_4 > #skF_3

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

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

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

tff(f_61,axiom,(
    ! [A] :
      ( v2_ordinal1(A)
    <=> ! [B,C] :
          ~ ( r2_hidden(B,A)
            & r2_hidden(C,A)
            & ~ r2_hidden(B,C)
            & B != C
            & ~ r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_ordinal1)).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( ! [B] :
            ( r2_hidden(B,A)
           => ( v3_ordinal1(B)
              & r1_tarski(B,A) ) )
       => v3_ordinal1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_ordinal1)).

tff(f_37,axiom,(
    ! [A] :
      ( ( v1_ordinal1(A)
        & v2_ordinal1(A) )
     => v3_ordinal1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_ordinal1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_78,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_43,plain,(
    ! [A_25] :
      ( r2_hidden('#skF_3'(A_25),A_25)
      | v2_ordinal1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_38,plain,(
    ! [B_21] :
      ( v3_ordinal1(B_21)
      | ~ r2_hidden(B_21,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_53,plain,
    ( v3_ordinal1('#skF_3'('#skF_4'))
    | v2_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_43,c_38])).

tff(c_65,plain,(
    v2_ordinal1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_53])).

tff(c_70,plain,(
    ! [A_29] :
      ( v3_ordinal1(A_29)
      | ~ v2_ordinal1(A_29)
      | ~ v1_ordinal1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_34,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_73,plain,
    ( ~ v2_ordinal1('#skF_4')
    | ~ v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_34])).

tff(c_76,plain,(
    ~ v1_ordinal1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_73])).

tff(c_77,plain,(
    ! [A_30] :
      ( r2_hidden('#skF_1'(A_30),A_30)
      | v1_ordinal1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_36,plain,(
    ! [B_21] :
      ( r1_tarski(B_21,'#skF_4')
      | ~ r2_hidden(B_21,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_81,plain,
    ( r1_tarski('#skF_1'('#skF_4'),'#skF_4')
    | v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_77,c_36])).

tff(c_88,plain,(
    r1_tarski('#skF_1'('#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_81])).

tff(c_12,plain,(
    ! [A_4] :
      ( ~ r1_tarski('#skF_1'(A_4),A_4)
      | v1_ordinal1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_95,plain,(
    v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_12])).

tff(c_99,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_95])).

tff(c_101,plain,(
    ~ v2_ordinal1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_104,plain,(
    ! [A_33] :
      ( '#skF_2'(A_33) != '#skF_3'(A_33)
      | v2_ordinal1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_108,plain,(
    '#skF_2'('#skF_4') != '#skF_3'('#skF_4') ),
    inference(resolution,[status(thm)],[c_104,c_101])).

tff(c_100,plain,(
    v3_ordinal1('#skF_3'('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_54,plain,(
    ! [A_26] :
      ( r2_hidden('#skF_2'(A_26),A_26)
      | v2_ordinal1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_64,plain,
    ( v3_ordinal1('#skF_2'('#skF_4'))
    | v2_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_38])).

tff(c_102,plain,(
    v3_ordinal1('#skF_2'('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_64])).

tff(c_193,plain,(
    ! [B_47,A_48] :
      ( r2_hidden(B_47,A_48)
      | r1_ordinal1(A_48,B_47)
      | ~ v3_ordinal1(B_47)
      | ~ v3_ordinal1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_18,plain,(
    ! [A_8] :
      ( ~ r2_hidden('#skF_3'(A_8),'#skF_2'(A_8))
      | v2_ordinal1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_213,plain,(
    ! [A_8] :
      ( v2_ordinal1(A_8)
      | r1_ordinal1('#skF_2'(A_8),'#skF_3'(A_8))
      | ~ v3_ordinal1('#skF_3'(A_8))
      | ~ v3_ordinal1('#skF_2'(A_8)) ) ),
    inference(resolution,[status(thm)],[c_193,c_18])).

tff(c_22,plain,(
    ! [A_8] :
      ( ~ r2_hidden('#skF_2'(A_8),'#skF_3'(A_8))
      | v2_ordinal1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_376,plain,(
    ! [A_66] :
      ( v2_ordinal1(A_66)
      | r1_ordinal1('#skF_3'(A_66),'#skF_2'(A_66))
      | ~ v3_ordinal1('#skF_2'(A_66))
      | ~ v3_ordinal1('#skF_3'(A_66)) ) ),
    inference(resolution,[status(thm)],[c_193,c_22])).

tff(c_30,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ r1_ordinal1(A_15,B_16)
      | ~ v3_ordinal1(B_16)
      | ~ v3_ordinal1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_216,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ r1_ordinal1(A_49,B_50)
      | ~ v3_ordinal1(B_50)
      | ~ v3_ordinal1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_302,plain,(
    ! [B_59,A_60] :
      ( B_59 = A_60
      | ~ r1_tarski(B_59,A_60)
      | ~ r1_ordinal1(A_60,B_59)
      | ~ v3_ordinal1(B_59)
      | ~ v3_ordinal1(A_60) ) ),
    inference(resolution,[status(thm)],[c_216,c_2])).

tff(c_325,plain,(
    ! [B_16,A_15] :
      ( B_16 = A_15
      | ~ r1_ordinal1(B_16,A_15)
      | ~ r1_ordinal1(A_15,B_16)
      | ~ v3_ordinal1(B_16)
      | ~ v3_ordinal1(A_15) ) ),
    inference(resolution,[status(thm)],[c_30,c_302])).

tff(c_473,plain,(
    ! [A_78] :
      ( '#skF_2'(A_78) = '#skF_3'(A_78)
      | ~ r1_ordinal1('#skF_2'(A_78),'#skF_3'(A_78))
      | v2_ordinal1(A_78)
      | ~ v3_ordinal1('#skF_2'(A_78))
      | ~ v3_ordinal1('#skF_3'(A_78)) ) ),
    inference(resolution,[status(thm)],[c_376,c_325])).

tff(c_486,plain,(
    ! [A_79] :
      ( '#skF_2'(A_79) = '#skF_3'(A_79)
      | v2_ordinal1(A_79)
      | ~ v3_ordinal1('#skF_3'(A_79))
      | ~ v3_ordinal1('#skF_2'(A_79)) ) ),
    inference(resolution,[status(thm)],[c_213,c_473])).

tff(c_492,plain,
    ( '#skF_2'('#skF_4') = '#skF_3'('#skF_4')
    | v2_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3'('#skF_4')) ),
    inference(resolution,[status(thm)],[c_102,c_486])).

tff(c_496,plain,
    ( '#skF_2'('#skF_4') = '#skF_3'('#skF_4')
    | v2_ordinal1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_492])).

tff(c_498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_108,c_496])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:32:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.32  
% 2.14/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.33  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_2 > #skF_1 > #skF_4 > #skF_3
% 2.14/1.33  
% 2.14/1.33  %Foreground sorts:
% 2.14/1.33  
% 2.14/1.33  
% 2.14/1.33  %Background operators:
% 2.14/1.33  
% 2.14/1.33  
% 2.14/1.33  %Foreground operators:
% 2.14/1.33  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.14/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.33  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 2.14/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.14/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.33  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 2.14/1.33  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.14/1.33  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 2.14/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.33  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.14/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.33  
% 2.61/1.34  tff(f_61, axiom, (![A]: (v2_ordinal1(A) <=> (![B, C]: ~((((r2_hidden(B, A) & r2_hidden(C, A)) & ~r2_hidden(B, C)) & ~(B = C)) & ~r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_ordinal1)).
% 2.61/1.34  tff(f_88, negated_conjecture, ~(![A]: ((![B]: (r2_hidden(B, A) => (v3_ordinal1(B) & r1_tarski(B, A)))) => v3_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_ordinal1)).
% 2.61/1.34  tff(f_37, axiom, (![A]: ((v1_ordinal1(A) & v2_ordinal1(A)) => v3_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_ordinal1)).
% 2.61/1.34  tff(f_44, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 2.61/1.34  tff(f_78, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 2.61/1.34  tff(f_69, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 2.61/1.34  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.61/1.34  tff(c_43, plain, (![A_25]: (r2_hidden('#skF_3'(A_25), A_25) | v2_ordinal1(A_25))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.61/1.34  tff(c_38, plain, (![B_21]: (v3_ordinal1(B_21) | ~r2_hidden(B_21, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.61/1.34  tff(c_53, plain, (v3_ordinal1('#skF_3'('#skF_4')) | v2_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_43, c_38])).
% 2.61/1.34  tff(c_65, plain, (v2_ordinal1('#skF_4')), inference(splitLeft, [status(thm)], [c_53])).
% 2.61/1.34  tff(c_70, plain, (![A_29]: (v3_ordinal1(A_29) | ~v2_ordinal1(A_29) | ~v1_ordinal1(A_29))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.61/1.34  tff(c_34, plain, (~v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.61/1.34  tff(c_73, plain, (~v2_ordinal1('#skF_4') | ~v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_34])).
% 2.61/1.34  tff(c_76, plain, (~v1_ordinal1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_73])).
% 2.61/1.34  tff(c_77, plain, (![A_30]: (r2_hidden('#skF_1'(A_30), A_30) | v1_ordinal1(A_30))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.61/1.34  tff(c_36, plain, (![B_21]: (r1_tarski(B_21, '#skF_4') | ~r2_hidden(B_21, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.61/1.34  tff(c_81, plain, (r1_tarski('#skF_1'('#skF_4'), '#skF_4') | v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_77, c_36])).
% 2.61/1.34  tff(c_88, plain, (r1_tarski('#skF_1'('#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_76, c_81])).
% 2.61/1.34  tff(c_12, plain, (![A_4]: (~r1_tarski('#skF_1'(A_4), A_4) | v1_ordinal1(A_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.61/1.34  tff(c_95, plain, (v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_88, c_12])).
% 2.61/1.34  tff(c_99, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_95])).
% 2.61/1.34  tff(c_101, plain, (~v2_ordinal1('#skF_4')), inference(splitRight, [status(thm)], [c_53])).
% 2.61/1.34  tff(c_104, plain, (![A_33]: ('#skF_2'(A_33)!='#skF_3'(A_33) | v2_ordinal1(A_33))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.61/1.34  tff(c_108, plain, ('#skF_2'('#skF_4')!='#skF_3'('#skF_4')), inference(resolution, [status(thm)], [c_104, c_101])).
% 2.61/1.34  tff(c_100, plain, (v3_ordinal1('#skF_3'('#skF_4'))), inference(splitRight, [status(thm)], [c_53])).
% 2.61/1.34  tff(c_54, plain, (![A_26]: (r2_hidden('#skF_2'(A_26), A_26) | v2_ordinal1(A_26))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.61/1.34  tff(c_64, plain, (v3_ordinal1('#skF_2'('#skF_4')) | v2_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_38])).
% 2.61/1.34  tff(c_102, plain, (v3_ordinal1('#skF_2'('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_101, c_64])).
% 2.61/1.34  tff(c_193, plain, (![B_47, A_48]: (r2_hidden(B_47, A_48) | r1_ordinal1(A_48, B_47) | ~v3_ordinal1(B_47) | ~v3_ordinal1(A_48))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.61/1.34  tff(c_18, plain, (![A_8]: (~r2_hidden('#skF_3'(A_8), '#skF_2'(A_8)) | v2_ordinal1(A_8))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.61/1.34  tff(c_213, plain, (![A_8]: (v2_ordinal1(A_8) | r1_ordinal1('#skF_2'(A_8), '#skF_3'(A_8)) | ~v3_ordinal1('#skF_3'(A_8)) | ~v3_ordinal1('#skF_2'(A_8)))), inference(resolution, [status(thm)], [c_193, c_18])).
% 2.61/1.34  tff(c_22, plain, (![A_8]: (~r2_hidden('#skF_2'(A_8), '#skF_3'(A_8)) | v2_ordinal1(A_8))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.61/1.34  tff(c_376, plain, (![A_66]: (v2_ordinal1(A_66) | r1_ordinal1('#skF_3'(A_66), '#skF_2'(A_66)) | ~v3_ordinal1('#skF_2'(A_66)) | ~v3_ordinal1('#skF_3'(A_66)))), inference(resolution, [status(thm)], [c_193, c_22])).
% 2.61/1.34  tff(c_30, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~r1_ordinal1(A_15, B_16) | ~v3_ordinal1(B_16) | ~v3_ordinal1(A_15))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.61/1.34  tff(c_216, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~r1_ordinal1(A_49, B_50) | ~v3_ordinal1(B_50) | ~v3_ordinal1(A_49))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.61/1.34  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.61/1.34  tff(c_302, plain, (![B_59, A_60]: (B_59=A_60 | ~r1_tarski(B_59, A_60) | ~r1_ordinal1(A_60, B_59) | ~v3_ordinal1(B_59) | ~v3_ordinal1(A_60))), inference(resolution, [status(thm)], [c_216, c_2])).
% 2.61/1.34  tff(c_325, plain, (![B_16, A_15]: (B_16=A_15 | ~r1_ordinal1(B_16, A_15) | ~r1_ordinal1(A_15, B_16) | ~v3_ordinal1(B_16) | ~v3_ordinal1(A_15))), inference(resolution, [status(thm)], [c_30, c_302])).
% 2.61/1.34  tff(c_473, plain, (![A_78]: ('#skF_2'(A_78)='#skF_3'(A_78) | ~r1_ordinal1('#skF_2'(A_78), '#skF_3'(A_78)) | v2_ordinal1(A_78) | ~v3_ordinal1('#skF_2'(A_78)) | ~v3_ordinal1('#skF_3'(A_78)))), inference(resolution, [status(thm)], [c_376, c_325])).
% 2.61/1.34  tff(c_486, plain, (![A_79]: ('#skF_2'(A_79)='#skF_3'(A_79) | v2_ordinal1(A_79) | ~v3_ordinal1('#skF_3'(A_79)) | ~v3_ordinal1('#skF_2'(A_79)))), inference(resolution, [status(thm)], [c_213, c_473])).
% 2.61/1.34  tff(c_492, plain, ('#skF_2'('#skF_4')='#skF_3'('#skF_4') | v2_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3'('#skF_4'))), inference(resolution, [status(thm)], [c_102, c_486])).
% 2.61/1.34  tff(c_496, plain, ('#skF_2'('#skF_4')='#skF_3'('#skF_4') | v2_ordinal1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_492])).
% 2.61/1.34  tff(c_498, plain, $false, inference(negUnitSimplification, [status(thm)], [c_101, c_108, c_496])).
% 2.61/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.34  
% 2.61/1.34  Inference rules
% 2.61/1.34  ----------------------
% 2.61/1.34  #Ref     : 0
% 2.61/1.34  #Sup     : 85
% 2.61/1.34  #Fact    : 4
% 2.61/1.34  #Define  : 0
% 2.61/1.34  #Split   : 4
% 2.61/1.34  #Chain   : 0
% 2.61/1.34  #Close   : 0
% 2.61/1.34  
% 2.61/1.34  Ordering : KBO
% 2.61/1.34  
% 2.61/1.34  Simplification rules
% 2.61/1.34  ----------------------
% 2.61/1.34  #Subsume      : 22
% 2.61/1.34  #Demod        : 15
% 2.61/1.34  #Tautology    : 21
% 2.61/1.34  #SimpNegUnit  : 7
% 2.61/1.34  #BackRed      : 0
% 2.61/1.34  
% 2.61/1.34  #Partial instantiations: 0
% 2.61/1.34  #Strategies tried      : 1
% 2.61/1.34  
% 2.61/1.34  Timing (in seconds)
% 2.61/1.34  ----------------------
% 2.61/1.34  Preprocessing        : 0.29
% 2.61/1.34  Parsing              : 0.15
% 2.61/1.34  CNF conversion       : 0.02
% 2.61/1.34  Main loop            : 0.30
% 2.61/1.34  Inferencing          : 0.12
% 2.61/1.34  Reduction            : 0.07
% 2.61/1.34  Demodulation         : 0.04
% 2.61/1.34  BG Simplification    : 0.02
% 2.61/1.34  Subsumption          : 0.07
% 2.61/1.34  Abstraction          : 0.02
% 2.61/1.34  MUC search           : 0.00
% 2.61/1.34  Cooper               : 0.00
% 2.61/1.34  Total                : 0.62
% 2.61/1.34  Index Insertion      : 0.00
% 2.61/1.34  Index Deletion       : 0.00
% 2.61/1.34  Index Matching       : 0.00
% 2.61/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
