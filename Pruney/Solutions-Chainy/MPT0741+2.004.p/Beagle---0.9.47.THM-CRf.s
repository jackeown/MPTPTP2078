%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:06 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 101 expanded)
%              Number of leaves         :   22 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :  120 ( 242 expanded)
%              Number of equality atoms :   12 (  16 expanded)
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

tff(f_43,axiom,(
    ! [A] :
      ( ( v1_ordinal1(A)
        & v2_ordinal1(A) )
     => v3_ordinal1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_ordinal1)).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( ! [B] :
            ( r2_hidden(B,A)
           => ( v3_ordinal1(B)
              & r1_tarski(B,A) ) )
       => v3_ordinal1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_ordinal1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_67,axiom,(
    ! [A] :
      ( v2_ordinal1(A)
    <=> ! [B,C] :
          ~ ( r2_hidden(B,A)
            & r2_hidden(C,A)
            & ~ r2_hidden(B,C)
            & B != C
            & ~ r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_ordinal1)).

tff(f_84,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

tff(c_44,plain,(
    ! [A_27] :
      ( v3_ordinal1(A_27)
      | ~ v2_ordinal1(A_27)
      | ~ v1_ordinal1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_36,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_48,plain,
    ( ~ v2_ordinal1('#skF_4')
    | ~ v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_36])).

tff(c_50,plain,(
    ~ v1_ordinal1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_52,plain,(
    ! [A_31] :
      ( r2_hidden('#skF_1'(A_31),A_31)
      | v1_ordinal1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_38,plain,(
    ! [B_23] :
      ( r1_tarski(B_23,'#skF_4')
      | ~ r2_hidden(B_23,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_56,plain,
    ( r1_tarski('#skF_1'('#skF_4'),'#skF_4')
    | v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_38])).

tff(c_63,plain,(
    r1_tarski('#skF_1'('#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_56])).

tff(c_67,plain,(
    ! [A_32] :
      ( ~ r1_tarski('#skF_1'(A_32),A_32)
      | v1_ordinal1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_70,plain,(
    v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_63,c_67])).

tff(c_74,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_70])).

tff(c_75,plain,(
    ~ v2_ordinal1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_77,plain,(
    ! [A_33] :
      ( '#skF_2'(A_33) != '#skF_3'(A_33)
      | v2_ordinal1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_81,plain,(
    '#skF_2'('#skF_4') != '#skF_3'('#skF_4') ),
    inference(resolution,[status(thm)],[c_77,c_75])).

tff(c_83,plain,(
    ! [A_35] :
      ( r2_hidden('#skF_3'(A_35),A_35)
      | v2_ordinal1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_40,plain,(
    ! [B_23] :
      ( v3_ordinal1(B_23)
      | ~ r2_hidden(B_23,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_91,plain,
    ( v3_ordinal1('#skF_3'('#skF_4'))
    | v2_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_83,c_40])).

tff(c_97,plain,(
    v3_ordinal1('#skF_3'('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_91])).

tff(c_98,plain,(
    ! [A_36] :
      ( r2_hidden('#skF_2'(A_36),A_36)
      | v2_ordinal1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_106,plain,
    ( v3_ordinal1('#skF_2'('#skF_4'))
    | v2_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_98,c_40])).

tff(c_112,plain,(
    v3_ordinal1('#skF_2'('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_106])).

tff(c_170,plain,(
    ! [B_49,A_50] :
      ( r2_hidden(B_49,A_50)
      | r1_ordinal1(A_50,B_49)
      | ~ v3_ordinal1(B_49)
      | ~ v3_ordinal1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_20,plain,(
    ! [A_10] :
      ( ~ r2_hidden('#skF_3'(A_10),'#skF_2'(A_10))
      | v2_ordinal1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_189,plain,(
    ! [A_10] :
      ( v2_ordinal1(A_10)
      | r1_ordinal1('#skF_2'(A_10),'#skF_3'(A_10))
      | ~ v3_ordinal1('#skF_3'(A_10))
      | ~ v3_ordinal1('#skF_2'(A_10)) ) ),
    inference(resolution,[status(thm)],[c_170,c_20])).

tff(c_24,plain,(
    ! [A_10] :
      ( ~ r2_hidden('#skF_2'(A_10),'#skF_3'(A_10))
      | v2_ordinal1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_370,plain,(
    ! [A_71] :
      ( v2_ordinal1(A_71)
      | r1_ordinal1('#skF_3'(A_71),'#skF_2'(A_71))
      | ~ v3_ordinal1('#skF_2'(A_71))
      | ~ v3_ordinal1('#skF_3'(A_71)) ) ),
    inference(resolution,[status(thm)],[c_170,c_24])).

tff(c_32,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ r1_ordinal1(A_17,B_18)
      | ~ v3_ordinal1(B_18)
      | ~ v3_ordinal1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_218,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,B_55)
      | ~ r1_ordinal1(A_54,B_55)
      | ~ v3_ordinal1(B_55)
      | ~ v3_ordinal1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_142,plain,(
    ! [A_44,B_45] :
      ( r2_xboole_0(A_44,B_45)
      | B_45 = A_44
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( ~ r2_xboole_0(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_154,plain,(
    ! [B_45,A_44] :
      ( ~ r1_tarski(B_45,A_44)
      | B_45 = A_44
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_142,c_8])).

tff(c_291,plain,(
    ! [B_61,A_62] :
      ( B_61 = A_62
      | ~ r1_tarski(B_61,A_62)
      | ~ r1_ordinal1(A_62,B_61)
      | ~ v3_ordinal1(B_61)
      | ~ v3_ordinal1(A_62) ) ),
    inference(resolution,[status(thm)],[c_218,c_154])).

tff(c_311,plain,(
    ! [B_18,A_17] :
      ( B_18 = A_17
      | ~ r1_ordinal1(B_18,A_17)
      | ~ r1_ordinal1(A_17,B_18)
      | ~ v3_ordinal1(B_18)
      | ~ v3_ordinal1(A_17) ) ),
    inference(resolution,[status(thm)],[c_32,c_291])).

tff(c_449,plain,(
    ! [A_81] :
      ( '#skF_2'(A_81) = '#skF_3'(A_81)
      | ~ r1_ordinal1('#skF_2'(A_81),'#skF_3'(A_81))
      | v2_ordinal1(A_81)
      | ~ v3_ordinal1('#skF_2'(A_81))
      | ~ v3_ordinal1('#skF_3'(A_81)) ) ),
    inference(resolution,[status(thm)],[c_370,c_311])).

tff(c_462,plain,(
    ! [A_82] :
      ( '#skF_2'(A_82) = '#skF_3'(A_82)
      | v2_ordinal1(A_82)
      | ~ v3_ordinal1('#skF_3'(A_82))
      | ~ v3_ordinal1('#skF_2'(A_82)) ) ),
    inference(resolution,[status(thm)],[c_189,c_449])).

tff(c_465,plain,
    ( '#skF_2'('#skF_4') = '#skF_3'('#skF_4')
    | v2_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3'('#skF_4')) ),
    inference(resolution,[status(thm)],[c_112,c_462])).

tff(c_471,plain,
    ( '#skF_2'('#skF_4') = '#skF_3'('#skF_4')
    | v2_ordinal1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_465])).

tff(c_473,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_81,c_471])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:22:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.32  
% 2.53/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.32  %$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_2 > #skF_1 > #skF_4 > #skF_3
% 2.53/1.32  
% 2.53/1.32  %Foreground sorts:
% 2.53/1.32  
% 2.53/1.32  
% 2.53/1.32  %Background operators:
% 2.53/1.32  
% 2.53/1.32  
% 2.53/1.32  %Foreground operators:
% 2.53/1.32  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.53/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.53/1.32  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 2.53/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.53/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.32  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 2.53/1.32  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.53/1.32  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 2.53/1.32  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.53/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.53/1.32  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.53/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.32  
% 2.53/1.34  tff(f_43, axiom, (![A]: ((v1_ordinal1(A) & v2_ordinal1(A)) => v3_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_ordinal1)).
% 2.53/1.34  tff(f_94, negated_conjecture, ~(![A]: ((![B]: (r2_hidden(B, A) => (v3_ordinal1(B) & r1_tarski(B, A)))) => v3_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_ordinal1)).
% 2.53/1.34  tff(f_50, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 2.53/1.34  tff(f_67, axiom, (![A]: (v2_ordinal1(A) <=> (![B, C]: ~((((r2_hidden(B, A) & r2_hidden(C, A)) & ~r2_hidden(B, C)) & ~(B = C)) & ~r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_ordinal1)).
% 2.53/1.34  tff(f_84, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 2.53/1.34  tff(f_75, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 2.53/1.34  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.53/1.34  tff(f_37, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_xboole_1)).
% 2.53/1.34  tff(c_44, plain, (![A_27]: (v3_ordinal1(A_27) | ~v2_ordinal1(A_27) | ~v1_ordinal1(A_27))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.53/1.34  tff(c_36, plain, (~v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.53/1.34  tff(c_48, plain, (~v2_ordinal1('#skF_4') | ~v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_36])).
% 2.53/1.34  tff(c_50, plain, (~v1_ordinal1('#skF_4')), inference(splitLeft, [status(thm)], [c_48])).
% 2.53/1.34  tff(c_52, plain, (![A_31]: (r2_hidden('#skF_1'(A_31), A_31) | v1_ordinal1(A_31))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.53/1.34  tff(c_38, plain, (![B_23]: (r1_tarski(B_23, '#skF_4') | ~r2_hidden(B_23, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.53/1.34  tff(c_56, plain, (r1_tarski('#skF_1'('#skF_4'), '#skF_4') | v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_38])).
% 2.53/1.34  tff(c_63, plain, (r1_tarski('#skF_1'('#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_50, c_56])).
% 2.53/1.34  tff(c_67, plain, (![A_32]: (~r1_tarski('#skF_1'(A_32), A_32) | v1_ordinal1(A_32))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.53/1.34  tff(c_70, plain, (v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_63, c_67])).
% 2.53/1.34  tff(c_74, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_70])).
% 2.53/1.34  tff(c_75, plain, (~v2_ordinal1('#skF_4')), inference(splitRight, [status(thm)], [c_48])).
% 2.53/1.34  tff(c_77, plain, (![A_33]: ('#skF_2'(A_33)!='#skF_3'(A_33) | v2_ordinal1(A_33))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.53/1.34  tff(c_81, plain, ('#skF_2'('#skF_4')!='#skF_3'('#skF_4')), inference(resolution, [status(thm)], [c_77, c_75])).
% 2.53/1.34  tff(c_83, plain, (![A_35]: (r2_hidden('#skF_3'(A_35), A_35) | v2_ordinal1(A_35))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.53/1.34  tff(c_40, plain, (![B_23]: (v3_ordinal1(B_23) | ~r2_hidden(B_23, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.53/1.34  tff(c_91, plain, (v3_ordinal1('#skF_3'('#skF_4')) | v2_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_83, c_40])).
% 2.53/1.34  tff(c_97, plain, (v3_ordinal1('#skF_3'('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_75, c_91])).
% 2.53/1.34  tff(c_98, plain, (![A_36]: (r2_hidden('#skF_2'(A_36), A_36) | v2_ordinal1(A_36))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.53/1.34  tff(c_106, plain, (v3_ordinal1('#skF_2'('#skF_4')) | v2_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_98, c_40])).
% 2.53/1.34  tff(c_112, plain, (v3_ordinal1('#skF_2'('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_75, c_106])).
% 2.53/1.34  tff(c_170, plain, (![B_49, A_50]: (r2_hidden(B_49, A_50) | r1_ordinal1(A_50, B_49) | ~v3_ordinal1(B_49) | ~v3_ordinal1(A_50))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.53/1.34  tff(c_20, plain, (![A_10]: (~r2_hidden('#skF_3'(A_10), '#skF_2'(A_10)) | v2_ordinal1(A_10))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.53/1.34  tff(c_189, plain, (![A_10]: (v2_ordinal1(A_10) | r1_ordinal1('#skF_2'(A_10), '#skF_3'(A_10)) | ~v3_ordinal1('#skF_3'(A_10)) | ~v3_ordinal1('#skF_2'(A_10)))), inference(resolution, [status(thm)], [c_170, c_20])).
% 2.53/1.34  tff(c_24, plain, (![A_10]: (~r2_hidden('#skF_2'(A_10), '#skF_3'(A_10)) | v2_ordinal1(A_10))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.53/1.34  tff(c_370, plain, (![A_71]: (v2_ordinal1(A_71) | r1_ordinal1('#skF_3'(A_71), '#skF_2'(A_71)) | ~v3_ordinal1('#skF_2'(A_71)) | ~v3_ordinal1('#skF_3'(A_71)))), inference(resolution, [status(thm)], [c_170, c_24])).
% 2.53/1.34  tff(c_32, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~r1_ordinal1(A_17, B_18) | ~v3_ordinal1(B_18) | ~v3_ordinal1(A_17))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.53/1.34  tff(c_218, plain, (![A_54, B_55]: (r1_tarski(A_54, B_55) | ~r1_ordinal1(A_54, B_55) | ~v3_ordinal1(B_55) | ~v3_ordinal1(A_54))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.53/1.34  tff(c_142, plain, (![A_44, B_45]: (r2_xboole_0(A_44, B_45) | B_45=A_44 | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.53/1.34  tff(c_8, plain, (![B_4, A_3]: (~r2_xboole_0(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.53/1.34  tff(c_154, plain, (![B_45, A_44]: (~r1_tarski(B_45, A_44) | B_45=A_44 | ~r1_tarski(A_44, B_45))), inference(resolution, [status(thm)], [c_142, c_8])).
% 2.53/1.34  tff(c_291, plain, (![B_61, A_62]: (B_61=A_62 | ~r1_tarski(B_61, A_62) | ~r1_ordinal1(A_62, B_61) | ~v3_ordinal1(B_61) | ~v3_ordinal1(A_62))), inference(resolution, [status(thm)], [c_218, c_154])).
% 2.53/1.34  tff(c_311, plain, (![B_18, A_17]: (B_18=A_17 | ~r1_ordinal1(B_18, A_17) | ~r1_ordinal1(A_17, B_18) | ~v3_ordinal1(B_18) | ~v3_ordinal1(A_17))), inference(resolution, [status(thm)], [c_32, c_291])).
% 2.53/1.34  tff(c_449, plain, (![A_81]: ('#skF_2'(A_81)='#skF_3'(A_81) | ~r1_ordinal1('#skF_2'(A_81), '#skF_3'(A_81)) | v2_ordinal1(A_81) | ~v3_ordinal1('#skF_2'(A_81)) | ~v3_ordinal1('#skF_3'(A_81)))), inference(resolution, [status(thm)], [c_370, c_311])).
% 2.53/1.34  tff(c_462, plain, (![A_82]: ('#skF_2'(A_82)='#skF_3'(A_82) | v2_ordinal1(A_82) | ~v3_ordinal1('#skF_3'(A_82)) | ~v3_ordinal1('#skF_2'(A_82)))), inference(resolution, [status(thm)], [c_189, c_449])).
% 2.53/1.34  tff(c_465, plain, ('#skF_2'('#skF_4')='#skF_3'('#skF_4') | v2_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3'('#skF_4'))), inference(resolution, [status(thm)], [c_112, c_462])).
% 2.53/1.34  tff(c_471, plain, ('#skF_2'('#skF_4')='#skF_3'('#skF_4') | v2_ordinal1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_465])).
% 2.53/1.34  tff(c_473, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_81, c_471])).
% 2.53/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.34  
% 2.53/1.34  Inference rules
% 2.53/1.34  ----------------------
% 2.53/1.34  #Ref     : 0
% 2.53/1.34  #Sup     : 77
% 2.53/1.34  #Fact    : 4
% 2.53/1.34  #Define  : 0
% 2.53/1.34  #Split   : 3
% 2.53/1.34  #Chain   : 0
% 2.53/1.34  #Close   : 0
% 2.53/1.34  
% 2.53/1.34  Ordering : KBO
% 2.53/1.34  
% 2.53/1.34  Simplification rules
% 2.53/1.34  ----------------------
% 2.53/1.34  #Subsume      : 20
% 2.53/1.34  #Demod        : 11
% 2.53/1.34  #Tautology    : 16
% 2.53/1.34  #SimpNegUnit  : 8
% 2.53/1.34  #BackRed      : 0
% 2.53/1.34  
% 2.53/1.34  #Partial instantiations: 0
% 2.53/1.34  #Strategies tried      : 1
% 2.53/1.34  
% 2.53/1.34  Timing (in seconds)
% 2.53/1.34  ----------------------
% 2.53/1.34  Preprocessing        : 0.30
% 2.53/1.34  Parsing              : 0.15
% 2.53/1.34  CNF conversion       : 0.02
% 2.53/1.34  Main loop            : 0.29
% 2.53/1.34  Inferencing          : 0.12
% 2.53/1.34  Reduction            : 0.06
% 2.53/1.34  Demodulation         : 0.03
% 2.53/1.34  BG Simplification    : 0.02
% 2.53/1.34  Subsumption          : 0.06
% 2.53/1.34  Abstraction          : 0.02
% 2.53/1.34  MUC search           : 0.00
% 2.53/1.34  Cooper               : 0.00
% 2.53/1.34  Total                : 0.61
% 2.53/1.34  Index Insertion      : 0.00
% 2.53/1.34  Index Deletion       : 0.00
% 2.53/1.34  Index Matching       : 0.00
% 2.53/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
