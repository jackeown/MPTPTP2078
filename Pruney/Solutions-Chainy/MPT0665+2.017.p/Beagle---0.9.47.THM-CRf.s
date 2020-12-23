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
% DateTime   : Thu Dec  3 10:04:16 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 112 expanded)
%              Number of leaves         :   23 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :   84 ( 308 expanded)
%              Number of equality atoms :    7 (  21 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r2_hidden(A,k1_relat_1(C))
            & r2_hidden(A,B) )
         => r2_hidden(k1_funct_1(C,A),k2_relat_1(k7_relat_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_funct_1)).

tff(f_52,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_40,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_28,plain,(
    ! [A_46,B_47] :
      ( v1_funct_1(k7_relat_1(A_46,B_47))
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_36,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_38,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r2_hidden(A_3,k1_relat_1(k7_relat_1(C_5,B_4)))
      | ~ r2_hidden(A_3,k1_relat_1(C_5))
      | ~ r2_hidden(A_3,B_4)
      | ~ v1_relat_1(C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k7_relat_1(A_1,B_2))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_91,plain,(
    ! [C_72,B_73,A_74] :
      ( k1_funct_1(k7_relat_1(C_72,B_73),A_74) = k1_funct_1(C_72,A_74)
      | ~ r2_hidden(A_74,k1_relat_1(k7_relat_1(C_72,B_73)))
      | ~ v1_funct_1(C_72)
      | ~ v1_relat_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_137,plain,(
    ! [C_77,B_78,A_79] :
      ( k1_funct_1(k7_relat_1(C_77,B_78),A_79) = k1_funct_1(C_77,A_79)
      | ~ v1_funct_1(C_77)
      | ~ r2_hidden(A_79,k1_relat_1(C_77))
      | ~ r2_hidden(A_79,B_78)
      | ~ v1_relat_1(C_77) ) ),
    inference(resolution,[status(thm)],[c_4,c_91])).

tff(c_151,plain,(
    ! [B_78] :
      ( k1_funct_1(k7_relat_1('#skF_7',B_78),'#skF_5') = k1_funct_1('#skF_7','#skF_5')
      | ~ v1_funct_1('#skF_7')
      | ~ r2_hidden('#skF_5',B_78)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_38,c_137])).

tff(c_160,plain,(
    ! [B_80] :
      ( k1_funct_1(k7_relat_1('#skF_7',B_80),'#skF_5') = k1_funct_1('#skF_7','#skF_5')
      | ~ r2_hidden('#skF_5',B_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_151])).

tff(c_10,plain,(
    ! [A_6,D_45] :
      ( r2_hidden(k1_funct_1(A_6,D_45),k2_relat_1(A_6))
      | ~ r2_hidden(D_45,k1_relat_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_203,plain,(
    ! [B_83] :
      ( r2_hidden(k1_funct_1('#skF_7','#skF_5'),k2_relat_1(k7_relat_1('#skF_7',B_83)))
      | ~ r2_hidden('#skF_5',k1_relat_1(k7_relat_1('#skF_7',B_83)))
      | ~ v1_funct_1(k7_relat_1('#skF_7',B_83))
      | ~ v1_relat_1(k7_relat_1('#skF_7',B_83))
      | ~ r2_hidden('#skF_5',B_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_10])).

tff(c_34,plain,(
    ~ r2_hidden(k1_funct_1('#skF_7','#skF_5'),k2_relat_1(k7_relat_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_206,plain,
    ( ~ r2_hidden('#skF_5',k1_relat_1(k7_relat_1('#skF_7','#skF_6')))
    | ~ v1_funct_1(k7_relat_1('#skF_7','#skF_6'))
    | ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6'))
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_203,c_34])).

tff(c_209,plain,
    ( ~ r2_hidden('#skF_5',k1_relat_1(k7_relat_1('#skF_7','#skF_6')))
    | ~ v1_funct_1(k7_relat_1('#skF_7','#skF_6'))
    | ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_206])).

tff(c_210,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_213,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_2,c_210])).

tff(c_217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_213])).

tff(c_218,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_7','#skF_6'))
    | ~ r2_hidden('#skF_5',k1_relat_1(k7_relat_1('#skF_7','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_220,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1(k7_relat_1('#skF_7','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_223,plain,
    ( ~ r2_hidden('#skF_5',k1_relat_1('#skF_7'))
    | ~ r2_hidden('#skF_5','#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_4,c_220])).

tff(c_227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36,c_38,c_223])).

tff(c_228,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_7','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_237,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_228])).

tff(c_241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_237])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:23:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.25  
% 2.35/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.25  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 2.35/1.25  
% 2.35/1.25  %Foreground sorts:
% 2.35/1.25  
% 2.35/1.25  
% 2.35/1.25  %Background operators:
% 2.35/1.25  
% 2.35/1.25  
% 2.35/1.25  %Foreground operators:
% 2.35/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.35/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.35/1.25  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.35/1.25  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.35/1.25  tff('#skF_7', type, '#skF_7': $i).
% 2.35/1.25  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.35/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.35/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.35/1.25  tff('#skF_6', type, '#skF_6': $i).
% 2.35/1.25  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.35/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.35/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.35/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.35/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.35/1.25  
% 2.35/1.26  tff(f_79, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(A, B)) => r2_hidden(k1_funct_1(C, A), k2_relat_1(k7_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_funct_1)).
% 2.35/1.26  tff(f_60, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 2.35/1.26  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 2.35/1.26  tff(f_29, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.35/1.26  tff(f_68, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_funct_1)).
% 2.35/1.26  tff(f_52, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 2.35/1.26  tff(c_42, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.35/1.26  tff(c_40, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.35/1.26  tff(c_28, plain, (![A_46, B_47]: (v1_funct_1(k7_relat_1(A_46, B_47)) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.35/1.26  tff(c_36, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.35/1.26  tff(c_38, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.35/1.26  tff(c_4, plain, (![A_3, C_5, B_4]: (r2_hidden(A_3, k1_relat_1(k7_relat_1(C_5, B_4))) | ~r2_hidden(A_3, k1_relat_1(C_5)) | ~r2_hidden(A_3, B_4) | ~v1_relat_1(C_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.35/1.26  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k7_relat_1(A_1, B_2)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.35/1.26  tff(c_91, plain, (![C_72, B_73, A_74]: (k1_funct_1(k7_relat_1(C_72, B_73), A_74)=k1_funct_1(C_72, A_74) | ~r2_hidden(A_74, k1_relat_1(k7_relat_1(C_72, B_73))) | ~v1_funct_1(C_72) | ~v1_relat_1(C_72))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.35/1.26  tff(c_137, plain, (![C_77, B_78, A_79]: (k1_funct_1(k7_relat_1(C_77, B_78), A_79)=k1_funct_1(C_77, A_79) | ~v1_funct_1(C_77) | ~r2_hidden(A_79, k1_relat_1(C_77)) | ~r2_hidden(A_79, B_78) | ~v1_relat_1(C_77))), inference(resolution, [status(thm)], [c_4, c_91])).
% 2.35/1.26  tff(c_151, plain, (![B_78]: (k1_funct_1(k7_relat_1('#skF_7', B_78), '#skF_5')=k1_funct_1('#skF_7', '#skF_5') | ~v1_funct_1('#skF_7') | ~r2_hidden('#skF_5', B_78) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_38, c_137])).
% 2.35/1.26  tff(c_160, plain, (![B_80]: (k1_funct_1(k7_relat_1('#skF_7', B_80), '#skF_5')=k1_funct_1('#skF_7', '#skF_5') | ~r2_hidden('#skF_5', B_80))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_151])).
% 2.35/1.26  tff(c_10, plain, (![A_6, D_45]: (r2_hidden(k1_funct_1(A_6, D_45), k2_relat_1(A_6)) | ~r2_hidden(D_45, k1_relat_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.35/1.26  tff(c_203, plain, (![B_83]: (r2_hidden(k1_funct_1('#skF_7', '#skF_5'), k2_relat_1(k7_relat_1('#skF_7', B_83))) | ~r2_hidden('#skF_5', k1_relat_1(k7_relat_1('#skF_7', B_83))) | ~v1_funct_1(k7_relat_1('#skF_7', B_83)) | ~v1_relat_1(k7_relat_1('#skF_7', B_83)) | ~r2_hidden('#skF_5', B_83))), inference(superposition, [status(thm), theory('equality')], [c_160, c_10])).
% 2.35/1.26  tff(c_34, plain, (~r2_hidden(k1_funct_1('#skF_7', '#skF_5'), k2_relat_1(k7_relat_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.35/1.26  tff(c_206, plain, (~r2_hidden('#skF_5', k1_relat_1(k7_relat_1('#skF_7', '#skF_6'))) | ~v1_funct_1(k7_relat_1('#skF_7', '#skF_6')) | ~v1_relat_1(k7_relat_1('#skF_7', '#skF_6')) | ~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_203, c_34])).
% 2.35/1.26  tff(c_209, plain, (~r2_hidden('#skF_5', k1_relat_1(k7_relat_1('#skF_7', '#skF_6'))) | ~v1_funct_1(k7_relat_1('#skF_7', '#skF_6')) | ~v1_relat_1(k7_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_206])).
% 2.35/1.26  tff(c_210, plain, (~v1_relat_1(k7_relat_1('#skF_7', '#skF_6'))), inference(splitLeft, [status(thm)], [c_209])).
% 2.35/1.26  tff(c_213, plain, (~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_2, c_210])).
% 2.35/1.26  tff(c_217, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_213])).
% 2.35/1.26  tff(c_218, plain, (~v1_funct_1(k7_relat_1('#skF_7', '#skF_6')) | ~r2_hidden('#skF_5', k1_relat_1(k7_relat_1('#skF_7', '#skF_6')))), inference(splitRight, [status(thm)], [c_209])).
% 2.35/1.26  tff(c_220, plain, (~r2_hidden('#skF_5', k1_relat_1(k7_relat_1('#skF_7', '#skF_6')))), inference(splitLeft, [status(thm)], [c_218])).
% 2.35/1.26  tff(c_223, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_7')) | ~r2_hidden('#skF_5', '#skF_6') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_4, c_220])).
% 2.35/1.26  tff(c_227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_38, c_223])).
% 2.35/1.26  tff(c_228, plain, (~v1_funct_1(k7_relat_1('#skF_7', '#skF_6'))), inference(splitRight, [status(thm)], [c_218])).
% 2.35/1.26  tff(c_237, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_28, c_228])).
% 2.35/1.26  tff(c_241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_237])).
% 2.35/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.26  
% 2.35/1.26  Inference rules
% 2.35/1.26  ----------------------
% 2.35/1.26  #Ref     : 0
% 2.35/1.26  #Sup     : 39
% 2.35/1.26  #Fact    : 0
% 2.35/1.26  #Define  : 0
% 2.35/1.26  #Split   : 2
% 2.35/1.26  #Chain   : 0
% 2.35/1.26  #Close   : 0
% 2.35/1.26  
% 2.35/1.26  Ordering : KBO
% 2.35/1.26  
% 2.35/1.26  Simplification rules
% 2.35/1.26  ----------------------
% 2.35/1.26  #Subsume      : 1
% 2.35/1.26  #Demod        : 9
% 2.35/1.26  #Tautology    : 9
% 2.35/1.26  #SimpNegUnit  : 0
% 2.35/1.26  #BackRed      : 0
% 2.35/1.26  
% 2.35/1.26  #Partial instantiations: 0
% 2.35/1.26  #Strategies tried      : 1
% 2.35/1.26  
% 2.35/1.26  Timing (in seconds)
% 2.35/1.26  ----------------------
% 2.35/1.27  Preprocessing        : 0.30
% 2.35/1.27  Parsing              : 0.16
% 2.35/1.27  CNF conversion       : 0.03
% 2.35/1.27  Main loop            : 0.22
% 2.35/1.27  Inferencing          : 0.09
% 2.35/1.27  Reduction            : 0.06
% 2.35/1.27  Demodulation         : 0.04
% 2.35/1.27  BG Simplification    : 0.02
% 2.35/1.27  Subsumption          : 0.04
% 2.35/1.27  Abstraction          : 0.01
% 2.35/1.27  MUC search           : 0.00
% 2.35/1.27  Cooper               : 0.00
% 2.35/1.27  Total                : 0.55
% 2.35/1.27  Index Insertion      : 0.00
% 2.35/1.27  Index Deletion       : 0.00
% 2.35/1.27  Index Matching       : 0.00
% 2.35/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
