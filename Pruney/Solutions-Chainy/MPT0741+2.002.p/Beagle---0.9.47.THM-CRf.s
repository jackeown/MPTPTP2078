%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:06 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 110 expanded)
%              Number of leaves         :   23 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :  122 ( 263 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_2 > #skF_1 > #skF_4 > #skF_3

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

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_44,axiom,(
    ! [A] :
      ( ( v1_ordinal1(A)
        & v2_ordinal1(A) )
     => v3_ordinal1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_ordinal1)).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( ! [B] :
            ( r2_hidden(B,A)
           => ( v3_ordinal1(B)
              & r1_tarski(B,A) ) )
       => v3_ordinal1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_ordinal1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_68,axiom,(
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
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_94,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

tff(c_49,plain,(
    ! [A_30] :
      ( v3_ordinal1(A_30)
      | ~ v2_ordinal1(A_30)
      | ~ v1_ordinal1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_40,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_61,plain,
    ( ~ v2_ordinal1('#skF_4')
    | ~ v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_49,c_40])).

tff(c_62,plain,(
    ~ v1_ordinal1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_18,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_1'(A_5),A_5)
      | v1_ordinal1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_71,plain,(
    ! [B_32] :
      ( r1_tarski(B_32,'#skF_4')
      | ~ r2_hidden(B_32,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_75,plain,
    ( r1_tarski('#skF_1'('#skF_4'),'#skF_4')
    | v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_71])).

tff(c_78,plain,(
    r1_tarski('#skF_1'('#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_75])).

tff(c_112,plain,(
    ! [A_35] :
      ( ~ r1_tarski('#skF_1'(A_35),A_35)
      | v1_ordinal1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_115,plain,(
    v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_112])).

tff(c_119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_115])).

tff(c_120,plain,(
    ~ v2_ordinal1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_159,plain,(
    ! [A_39] :
      ( '#skF_2'(A_39) != '#skF_3'(A_39)
      | v2_ordinal1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_163,plain,(
    '#skF_2'('#skF_4') != '#skF_3'('#skF_4') ),
    inference(resolution,[status(thm)],[c_159,c_120])).

tff(c_136,plain,(
    ! [A_38] :
      ( r2_hidden('#skF_3'(A_38),A_38)
      | v2_ordinal1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_44,plain,(
    ! [B_25] :
      ( v3_ordinal1(B_25)
      | ~ r2_hidden(B_25,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_144,plain,
    ( v3_ordinal1('#skF_3'('#skF_4'))
    | v2_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_136,c_44])).

tff(c_150,plain,(
    v3_ordinal1('#skF_3'('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_144])).

tff(c_10,plain,(
    ! [A_3] :
      ( v1_ordinal1(A_3)
      | ~ v3_ordinal1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_157,plain,(
    v1_ordinal1('#skF_3'('#skF_4')) ),
    inference(resolution,[status(thm)],[c_150,c_10])).

tff(c_165,plain,(
    ! [A_42] :
      ( r2_hidden('#skF_2'(A_42),A_42)
      | v2_ordinal1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_173,plain,
    ( v3_ordinal1('#skF_2'('#skF_4'))
    | v2_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_165,c_44])).

tff(c_179,plain,(
    v3_ordinal1('#skF_2'('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_173])).

tff(c_217,plain,(
    ! [B_52,A_53] :
      ( r2_hidden(B_52,A_53)
      | r1_ordinal1(A_53,B_52)
      | ~ v3_ordinal1(B_52)
      | ~ v3_ordinal1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_26,plain,(
    ! [A_9] :
      ( ~ r2_hidden('#skF_2'(A_9),'#skF_3'(A_9))
      | v2_ordinal1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_237,plain,(
    ! [A_9] :
      ( v2_ordinal1(A_9)
      | r1_ordinal1('#skF_3'(A_9),'#skF_2'(A_9))
      | ~ v3_ordinal1('#skF_2'(A_9))
      | ~ v3_ordinal1('#skF_3'(A_9)) ) ),
    inference(resolution,[status(thm)],[c_217,c_26])).

tff(c_34,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ r1_ordinal1(A_16,B_17)
      | ~ v3_ordinal1(B_17)
      | ~ v3_ordinal1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_246,plain,(
    ! [A_56,B_57] :
      ( r2_hidden(A_56,B_57)
      | ~ r2_xboole_0(A_56,B_57)
      | ~ v3_ordinal1(B_57)
      | ~ v1_ordinal1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_299,plain,(
    ! [A_65,B_66] :
      ( r2_hidden(A_65,B_66)
      | ~ v3_ordinal1(B_66)
      | ~ v1_ordinal1(A_65)
      | B_66 = A_65
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_2,c_246])).

tff(c_22,plain,(
    ! [A_9] :
      ( ~ r2_hidden('#skF_3'(A_9),'#skF_2'(A_9))
      | v2_ordinal1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_352,plain,(
    ! [A_73] :
      ( v2_ordinal1(A_73)
      | ~ v3_ordinal1('#skF_2'(A_73))
      | ~ v1_ordinal1('#skF_3'(A_73))
      | '#skF_2'(A_73) = '#skF_3'(A_73)
      | ~ r1_tarski('#skF_3'(A_73),'#skF_2'(A_73)) ) ),
    inference(resolution,[status(thm)],[c_299,c_22])).

tff(c_457,plain,(
    ! [A_83] :
      ( v2_ordinal1(A_83)
      | ~ v1_ordinal1('#skF_3'(A_83))
      | '#skF_2'(A_83) = '#skF_3'(A_83)
      | ~ r1_ordinal1('#skF_3'(A_83),'#skF_2'(A_83))
      | ~ v3_ordinal1('#skF_2'(A_83))
      | ~ v3_ordinal1('#skF_3'(A_83)) ) ),
    inference(resolution,[status(thm)],[c_34,c_352])).

tff(c_485,plain,(
    ! [A_86] :
      ( ~ v1_ordinal1('#skF_3'(A_86))
      | '#skF_2'(A_86) = '#skF_3'(A_86)
      | v2_ordinal1(A_86)
      | ~ v3_ordinal1('#skF_2'(A_86))
      | ~ v3_ordinal1('#skF_3'(A_86)) ) ),
    inference(resolution,[status(thm)],[c_237,c_457])).

tff(c_488,plain,
    ( ~ v1_ordinal1('#skF_3'('#skF_4'))
    | '#skF_2'('#skF_4') = '#skF_3'('#skF_4')
    | v2_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3'('#skF_4')) ),
    inference(resolution,[status(thm)],[c_179,c_485])).

tff(c_494,plain,
    ( '#skF_2'('#skF_4') = '#skF_3'('#skF_4')
    | v2_ordinal1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_157,c_488])).

tff(c_496,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_163,c_494])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:11:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.49  
% 2.80/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.49  %$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_2 > #skF_1 > #skF_4 > #skF_3
% 2.80/1.49  
% 2.80/1.49  %Foreground sorts:
% 2.80/1.49  
% 2.80/1.49  
% 2.80/1.49  %Background operators:
% 2.80/1.49  
% 2.80/1.49  
% 2.80/1.49  %Foreground operators:
% 2.80/1.49  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.80/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.80/1.49  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 2.80/1.49  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.80/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.80/1.49  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 2.80/1.49  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.80/1.49  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 2.80/1.49  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.80/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.49  tff('#skF_4', type, '#skF_4': $i).
% 2.80/1.49  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.80/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.49  
% 2.80/1.51  tff(f_44, axiom, (![A]: ((v1_ordinal1(A) & v2_ordinal1(A)) => v3_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_ordinal1)).
% 2.80/1.51  tff(f_104, negated_conjecture, ~(![A]: ((![B]: (r2_hidden(B, A) => (v3_ordinal1(B) & r1_tarski(B, A)))) => v3_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_ordinal1)).
% 2.80/1.51  tff(f_51, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 2.80/1.51  tff(f_68, axiom, (![A]: (v2_ordinal1(A) <=> (![B, C]: ~((((r2_hidden(B, A) & r2_hidden(C, A)) & ~r2_hidden(B, C)) & ~(B = C)) & ~r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_ordinal1)).
% 2.80/1.51  tff(f_38, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 2.80/1.51  tff(f_94, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 2.80/1.51  tff(f_76, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 2.80/1.51  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.80/1.51  tff(f_85, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_ordinal1)).
% 2.80/1.51  tff(c_49, plain, (![A_30]: (v3_ordinal1(A_30) | ~v2_ordinal1(A_30) | ~v1_ordinal1(A_30))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.80/1.51  tff(c_40, plain, (~v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.80/1.51  tff(c_61, plain, (~v2_ordinal1('#skF_4') | ~v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_49, c_40])).
% 2.80/1.51  tff(c_62, plain, (~v1_ordinal1('#skF_4')), inference(splitLeft, [status(thm)], [c_61])).
% 2.80/1.51  tff(c_18, plain, (![A_5]: (r2_hidden('#skF_1'(A_5), A_5) | v1_ordinal1(A_5))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.80/1.51  tff(c_71, plain, (![B_32]: (r1_tarski(B_32, '#skF_4') | ~r2_hidden(B_32, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.80/1.51  tff(c_75, plain, (r1_tarski('#skF_1'('#skF_4'), '#skF_4') | v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_71])).
% 2.80/1.51  tff(c_78, plain, (r1_tarski('#skF_1'('#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_62, c_75])).
% 2.80/1.51  tff(c_112, plain, (![A_35]: (~r1_tarski('#skF_1'(A_35), A_35) | v1_ordinal1(A_35))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.80/1.51  tff(c_115, plain, (v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_112])).
% 2.80/1.51  tff(c_119, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_115])).
% 2.80/1.51  tff(c_120, plain, (~v2_ordinal1('#skF_4')), inference(splitRight, [status(thm)], [c_61])).
% 2.80/1.51  tff(c_159, plain, (![A_39]: ('#skF_2'(A_39)!='#skF_3'(A_39) | v2_ordinal1(A_39))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.80/1.51  tff(c_163, plain, ('#skF_2'('#skF_4')!='#skF_3'('#skF_4')), inference(resolution, [status(thm)], [c_159, c_120])).
% 2.80/1.51  tff(c_136, plain, (![A_38]: (r2_hidden('#skF_3'(A_38), A_38) | v2_ordinal1(A_38))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.80/1.51  tff(c_44, plain, (![B_25]: (v3_ordinal1(B_25) | ~r2_hidden(B_25, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.80/1.51  tff(c_144, plain, (v3_ordinal1('#skF_3'('#skF_4')) | v2_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_136, c_44])).
% 2.80/1.51  tff(c_150, plain, (v3_ordinal1('#skF_3'('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_120, c_144])).
% 2.80/1.51  tff(c_10, plain, (![A_3]: (v1_ordinal1(A_3) | ~v3_ordinal1(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.80/1.51  tff(c_157, plain, (v1_ordinal1('#skF_3'('#skF_4'))), inference(resolution, [status(thm)], [c_150, c_10])).
% 2.80/1.51  tff(c_165, plain, (![A_42]: (r2_hidden('#skF_2'(A_42), A_42) | v2_ordinal1(A_42))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.80/1.51  tff(c_173, plain, (v3_ordinal1('#skF_2'('#skF_4')) | v2_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_165, c_44])).
% 2.80/1.51  tff(c_179, plain, (v3_ordinal1('#skF_2'('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_120, c_173])).
% 2.80/1.51  tff(c_217, plain, (![B_52, A_53]: (r2_hidden(B_52, A_53) | r1_ordinal1(A_53, B_52) | ~v3_ordinal1(B_52) | ~v3_ordinal1(A_53))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.80/1.51  tff(c_26, plain, (![A_9]: (~r2_hidden('#skF_2'(A_9), '#skF_3'(A_9)) | v2_ordinal1(A_9))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.80/1.51  tff(c_237, plain, (![A_9]: (v2_ordinal1(A_9) | r1_ordinal1('#skF_3'(A_9), '#skF_2'(A_9)) | ~v3_ordinal1('#skF_2'(A_9)) | ~v3_ordinal1('#skF_3'(A_9)))), inference(resolution, [status(thm)], [c_217, c_26])).
% 2.80/1.51  tff(c_34, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~r1_ordinal1(A_16, B_17) | ~v3_ordinal1(B_17) | ~v3_ordinal1(A_16))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.80/1.51  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.80/1.51  tff(c_246, plain, (![A_56, B_57]: (r2_hidden(A_56, B_57) | ~r2_xboole_0(A_56, B_57) | ~v3_ordinal1(B_57) | ~v1_ordinal1(A_56))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.80/1.51  tff(c_299, plain, (![A_65, B_66]: (r2_hidden(A_65, B_66) | ~v3_ordinal1(B_66) | ~v1_ordinal1(A_65) | B_66=A_65 | ~r1_tarski(A_65, B_66))), inference(resolution, [status(thm)], [c_2, c_246])).
% 2.80/1.51  tff(c_22, plain, (![A_9]: (~r2_hidden('#skF_3'(A_9), '#skF_2'(A_9)) | v2_ordinal1(A_9))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.80/1.51  tff(c_352, plain, (![A_73]: (v2_ordinal1(A_73) | ~v3_ordinal1('#skF_2'(A_73)) | ~v1_ordinal1('#skF_3'(A_73)) | '#skF_2'(A_73)='#skF_3'(A_73) | ~r1_tarski('#skF_3'(A_73), '#skF_2'(A_73)))), inference(resolution, [status(thm)], [c_299, c_22])).
% 2.80/1.51  tff(c_457, plain, (![A_83]: (v2_ordinal1(A_83) | ~v1_ordinal1('#skF_3'(A_83)) | '#skF_2'(A_83)='#skF_3'(A_83) | ~r1_ordinal1('#skF_3'(A_83), '#skF_2'(A_83)) | ~v3_ordinal1('#skF_2'(A_83)) | ~v3_ordinal1('#skF_3'(A_83)))), inference(resolution, [status(thm)], [c_34, c_352])).
% 2.80/1.51  tff(c_485, plain, (![A_86]: (~v1_ordinal1('#skF_3'(A_86)) | '#skF_2'(A_86)='#skF_3'(A_86) | v2_ordinal1(A_86) | ~v3_ordinal1('#skF_2'(A_86)) | ~v3_ordinal1('#skF_3'(A_86)))), inference(resolution, [status(thm)], [c_237, c_457])).
% 2.80/1.51  tff(c_488, plain, (~v1_ordinal1('#skF_3'('#skF_4')) | '#skF_2'('#skF_4')='#skF_3'('#skF_4') | v2_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3'('#skF_4'))), inference(resolution, [status(thm)], [c_179, c_485])).
% 2.80/1.51  tff(c_494, plain, ('#skF_2'('#skF_4')='#skF_3'('#skF_4') | v2_ordinal1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_150, c_157, c_488])).
% 2.80/1.51  tff(c_496, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_163, c_494])).
% 2.80/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.51  
% 2.80/1.51  Inference rules
% 2.80/1.51  ----------------------
% 2.80/1.51  #Ref     : 0
% 2.80/1.51  #Sup     : 86
% 2.80/1.51  #Fact    : 4
% 2.80/1.51  #Define  : 0
% 2.80/1.51  #Split   : 2
% 2.80/1.51  #Chain   : 0
% 2.80/1.51  #Close   : 0
% 2.80/1.51  
% 2.80/1.51  Ordering : KBO
% 2.80/1.51  
% 2.80/1.51  Simplification rules
% 2.80/1.51  ----------------------
% 2.80/1.51  #Subsume      : 17
% 2.80/1.51  #Demod        : 8
% 2.80/1.51  #Tautology    : 16
% 2.80/1.51  #SimpNegUnit  : 8
% 2.80/1.51  #BackRed      : 0
% 2.80/1.51  
% 2.80/1.51  #Partial instantiations: 0
% 2.80/1.51  #Strategies tried      : 1
% 2.80/1.51  
% 2.80/1.51  Timing (in seconds)
% 2.80/1.51  ----------------------
% 2.80/1.51  Preprocessing        : 0.38
% 2.80/1.51  Parsing              : 0.19
% 2.80/1.51  CNF conversion       : 0.03
% 2.80/1.51  Main loop            : 0.30
% 2.80/1.51  Inferencing          : 0.12
% 2.80/1.51  Reduction            : 0.07
% 2.80/1.51  Demodulation         : 0.04
% 2.80/1.51  BG Simplification    : 0.02
% 2.80/1.51  Subsumption          : 0.07
% 2.80/1.51  Abstraction          : 0.02
% 2.80/1.51  MUC search           : 0.00
% 2.80/1.51  Cooper               : 0.00
% 2.80/1.51  Total                : 0.71
% 2.80/1.51  Index Insertion      : 0.00
% 2.80/1.51  Index Deletion       : 0.00
% 2.80/1.51  Index Matching       : 0.00
% 2.80/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
