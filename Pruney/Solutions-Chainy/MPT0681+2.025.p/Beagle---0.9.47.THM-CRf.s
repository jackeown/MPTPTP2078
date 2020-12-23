%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:28 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   49 (  64 expanded)
%              Number of leaves         :   23 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 ( 126 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_xboole_0(A,B)
            & v2_funct_1(C) )
         => r1_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_funct_1)).

tff(f_59,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).

tff(c_22,plain,(
    ~ r1_xboole_0(k9_relat_1('#skF_5','#skF_3'),k9_relat_1('#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_12,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_54,plain,(
    ! [A_22,B_23,C_24] :
      ( ~ r1_xboole_0(A_22,B_23)
      | ~ r2_hidden(C_24,k3_xboole_0(A_22,B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_61,plain,(
    ! [A_11,C_24] :
      ( ~ r1_xboole_0(A_11,k1_xboole_0)
      | ~ r2_hidden(C_24,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_54])).

tff(c_63,plain,(
    ! [C_24] : ~ r2_hidden(C_24,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_30,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_28,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_24,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_44,plain,(
    ! [A_19] :
      ( k9_relat_1(A_19,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_48,plain,(
    k9_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_44])).

tff(c_26,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_96,plain,(
    ! [A_30,B_31,B_32] :
      ( ~ r1_xboole_0(A_30,B_31)
      | r1_xboole_0(k3_xboole_0(A_30,B_31),B_32) ) ),
    inference(resolution,[status(thm)],[c_6,c_54])).

tff(c_16,plain,(
    ! [A_12] :
      ( ~ r1_xboole_0(A_12,A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_107,plain,(
    ! [A_33,B_34] :
      ( k3_xboole_0(A_33,B_34) = k1_xboole_0
      | ~ r1_xboole_0(A_33,B_34) ) ),
    inference(resolution,[status(thm)],[c_96,c_16])).

tff(c_124,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_107])).

tff(c_280,plain,(
    ! [C_47,A_48,B_49] :
      ( k3_xboole_0(k9_relat_1(C_47,A_48),k9_relat_1(C_47,B_49)) = k9_relat_1(C_47,k3_xboole_0(A_48,B_49))
      | ~ v2_funct_1(C_47)
      | ~ v1_funct_1(C_47)
      | ~ v1_relat_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),k3_xboole_0(A_6,B_7))
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_480,plain,(
    ! [C_68,A_69,B_70] :
      ( r2_hidden('#skF_2'(k9_relat_1(C_68,A_69),k9_relat_1(C_68,B_70)),k9_relat_1(C_68,k3_xboole_0(A_69,B_70)))
      | r1_xboole_0(k9_relat_1(C_68,A_69),k9_relat_1(C_68,B_70))
      | ~ v2_funct_1(C_68)
      | ~ v1_funct_1(C_68)
      | ~ v1_relat_1(C_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_8])).

tff(c_551,plain,(
    ! [C_81] :
      ( r2_hidden('#skF_2'(k9_relat_1(C_81,'#skF_3'),k9_relat_1(C_81,'#skF_4')),k9_relat_1(C_81,k1_xboole_0))
      | r1_xboole_0(k9_relat_1(C_81,'#skF_3'),k9_relat_1(C_81,'#skF_4'))
      | ~ v2_funct_1(C_81)
      | ~ v1_funct_1(C_81)
      | ~ v1_relat_1(C_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_480])).

tff(c_554,plain,
    ( r2_hidden('#skF_2'(k9_relat_1('#skF_5','#skF_3'),k9_relat_1('#skF_5','#skF_4')),k1_xboole_0)
    | r1_xboole_0(k9_relat_1('#skF_5','#skF_3'),k9_relat_1('#skF_5','#skF_4'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_551])).

tff(c_556,plain,
    ( r2_hidden('#skF_2'(k9_relat_1('#skF_5','#skF_3'),k9_relat_1('#skF_5','#skF_4')),k1_xboole_0)
    | r1_xboole_0(k9_relat_1('#skF_5','#skF_3'),k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_24,c_554])).

tff(c_558,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_63,c_556])).

tff(c_559,plain,(
    ! [A_11] : ~ r1_xboole_0(A_11,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_14,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_561,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_559,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n002.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 18:18:06 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.35  
% 2.37/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.35  %$ r2_hidden > r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.37/1.35  
% 2.37/1.35  %Foreground sorts:
% 2.37/1.35  
% 2.37/1.35  
% 2.37/1.35  %Background operators:
% 2.37/1.35  
% 2.37/1.35  
% 2.37/1.35  %Foreground operators:
% 2.37/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.37/1.35  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.37/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.37/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.37/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.37/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.37/1.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.37/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.37/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.37/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.37/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.37/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.37/1.35  
% 2.63/1.37  tff(f_94, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_xboole_0(A, B) & v2_funct_1(C)) => r1_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_funct_1)).
% 2.63/1.37  tff(f_59, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.63/1.37  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.63/1.37  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_relat_1)).
% 2.63/1.37  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.63/1.37  tff(f_71, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.63/1.37  tff(f_83, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_1)).
% 2.63/1.37  tff(c_22, plain, (~r1_xboole_0(k9_relat_1('#skF_5', '#skF_3'), k9_relat_1('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.63/1.37  tff(c_12, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.63/1.37  tff(c_54, plain, (![A_22, B_23, C_24]: (~r1_xboole_0(A_22, B_23) | ~r2_hidden(C_24, k3_xboole_0(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.63/1.37  tff(c_61, plain, (![A_11, C_24]: (~r1_xboole_0(A_11, k1_xboole_0) | ~r2_hidden(C_24, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_54])).
% 2.63/1.37  tff(c_63, plain, (![C_24]: (~r2_hidden(C_24, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_61])).
% 2.63/1.37  tff(c_30, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.63/1.37  tff(c_28, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.63/1.37  tff(c_24, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.63/1.37  tff(c_44, plain, (![A_19]: (k9_relat_1(A_19, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.63/1.37  tff(c_48, plain, (k9_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_44])).
% 2.63/1.37  tff(c_26, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.63/1.37  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.63/1.37  tff(c_96, plain, (![A_30, B_31, B_32]: (~r1_xboole_0(A_30, B_31) | r1_xboole_0(k3_xboole_0(A_30, B_31), B_32))), inference(resolution, [status(thm)], [c_6, c_54])).
% 2.63/1.37  tff(c_16, plain, (![A_12]: (~r1_xboole_0(A_12, A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.63/1.37  tff(c_107, plain, (![A_33, B_34]: (k3_xboole_0(A_33, B_34)=k1_xboole_0 | ~r1_xboole_0(A_33, B_34))), inference(resolution, [status(thm)], [c_96, c_16])).
% 2.63/1.37  tff(c_124, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_107])).
% 2.63/1.37  tff(c_280, plain, (![C_47, A_48, B_49]: (k3_xboole_0(k9_relat_1(C_47, A_48), k9_relat_1(C_47, B_49))=k9_relat_1(C_47, k3_xboole_0(A_48, B_49)) | ~v2_funct_1(C_47) | ~v1_funct_1(C_47) | ~v1_relat_1(C_47))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.63/1.37  tff(c_8, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), k3_xboole_0(A_6, B_7)) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.63/1.37  tff(c_480, plain, (![C_68, A_69, B_70]: (r2_hidden('#skF_2'(k9_relat_1(C_68, A_69), k9_relat_1(C_68, B_70)), k9_relat_1(C_68, k3_xboole_0(A_69, B_70))) | r1_xboole_0(k9_relat_1(C_68, A_69), k9_relat_1(C_68, B_70)) | ~v2_funct_1(C_68) | ~v1_funct_1(C_68) | ~v1_relat_1(C_68))), inference(superposition, [status(thm), theory('equality')], [c_280, c_8])).
% 2.63/1.37  tff(c_551, plain, (![C_81]: (r2_hidden('#skF_2'(k9_relat_1(C_81, '#skF_3'), k9_relat_1(C_81, '#skF_4')), k9_relat_1(C_81, k1_xboole_0)) | r1_xboole_0(k9_relat_1(C_81, '#skF_3'), k9_relat_1(C_81, '#skF_4')) | ~v2_funct_1(C_81) | ~v1_funct_1(C_81) | ~v1_relat_1(C_81))), inference(superposition, [status(thm), theory('equality')], [c_124, c_480])).
% 2.63/1.37  tff(c_554, plain, (r2_hidden('#skF_2'(k9_relat_1('#skF_5', '#skF_3'), k9_relat_1('#skF_5', '#skF_4')), k1_xboole_0) | r1_xboole_0(k9_relat_1('#skF_5', '#skF_3'), k9_relat_1('#skF_5', '#skF_4')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_48, c_551])).
% 2.63/1.37  tff(c_556, plain, (r2_hidden('#skF_2'(k9_relat_1('#skF_5', '#skF_3'), k9_relat_1('#skF_5', '#skF_4')), k1_xboole_0) | r1_xboole_0(k9_relat_1('#skF_5', '#skF_3'), k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_24, c_554])).
% 2.63/1.37  tff(c_558, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_63, c_556])).
% 2.63/1.37  tff(c_559, plain, (![A_11]: (~r1_xboole_0(A_11, k1_xboole_0))), inference(splitRight, [status(thm)], [c_61])).
% 2.63/1.37  tff(c_14, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.63/1.37  tff(c_561, plain, $false, inference(negUnitSimplification, [status(thm)], [c_559, c_14])).
% 2.63/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.37  
% 2.63/1.37  Inference rules
% 2.63/1.37  ----------------------
% 2.63/1.37  #Ref     : 0
% 2.63/1.37  #Sup     : 120
% 2.63/1.37  #Fact    : 0
% 2.63/1.37  #Define  : 0
% 2.63/1.37  #Split   : 1
% 2.63/1.37  #Chain   : 0
% 2.63/1.37  #Close   : 0
% 2.63/1.37  
% 2.63/1.37  Ordering : KBO
% 2.63/1.37  
% 2.63/1.37  Simplification rules
% 2.63/1.37  ----------------------
% 2.63/1.37  #Subsume      : 15
% 2.63/1.37  #Demod        : 169
% 2.63/1.37  #Tautology    : 76
% 2.63/1.37  #SimpNegUnit  : 13
% 2.63/1.37  #BackRed      : 1
% 2.63/1.37  
% 2.63/1.37  #Partial instantiations: 0
% 2.63/1.37  #Strategies tried      : 1
% 2.63/1.37  
% 2.63/1.37  Timing (in seconds)
% 2.63/1.37  ----------------------
% 2.63/1.38  Preprocessing        : 0.30
% 2.63/1.38  Parsing              : 0.17
% 2.63/1.38  CNF conversion       : 0.02
% 2.63/1.38  Main loop            : 0.31
% 2.63/1.38  Inferencing          : 0.12
% 2.63/1.38  Reduction            : 0.09
% 2.63/1.38  Demodulation         : 0.07
% 2.63/1.38  BG Simplification    : 0.01
% 2.63/1.38  Subsumption          : 0.06
% 2.63/1.38  Abstraction          : 0.01
% 2.63/1.38  MUC search           : 0.00
% 2.63/1.38  Cooper               : 0.00
% 2.63/1.38  Total                : 0.65
% 2.63/1.38  Index Insertion      : 0.00
% 2.63/1.38  Index Deletion       : 0.00
% 2.63/1.38  Index Matching       : 0.00
% 2.63/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
