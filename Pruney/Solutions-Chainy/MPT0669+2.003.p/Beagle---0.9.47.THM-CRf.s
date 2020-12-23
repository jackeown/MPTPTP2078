%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:19 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 169 expanded)
%              Number of leaves         :   19 (  66 expanded)
%              Depth                    :    8
%              Number of atoms          :  110 ( 480 expanded)
%              Number of equality atoms :    2 (  12 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k8_relat_1 > k1_funct_1 > #nlpp > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k1_relat_1(k8_relat_1(B,C)))
        <=> ( r2_hidden(A,k1_relat_1(C))
            & r2_hidden(k1_funct_1(C,A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k8_relat_1(A,B))
        & v1_funct_1(k8_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( B = k8_relat_1(A,C)
          <=> ( ! [D] :
                  ( r2_hidden(D,k1_relat_1(B))
                <=> ( r2_hidden(D,k1_relat_1(C))
                    & r2_hidden(k1_funct_1(C,D),A) ) )
              & ! [D] :
                  ( r2_hidden(D,k1_relat_1(B))
                 => k1_funct_1(B,D) = k1_funct_1(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_40,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( v1_funct_1(k8_relat_1(A_3,B_4))
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k8_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_54,plain,
    ( r2_hidden('#skF_4',k1_relat_1(k8_relat_1('#skF_5','#skF_6')))
    | r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_57,plain,(
    r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_50,plain,
    ( r2_hidden('#skF_4',k1_relat_1(k8_relat_1('#skF_5','#skF_6')))
    | r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_58,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_64,plain,(
    ! [D_36,A_37,C_38] :
      ( r2_hidden(D_36,k1_relat_1(k8_relat_1(A_37,C_38)))
      | ~ r2_hidden(k1_funct_1(C_38,D_36),A_37)
      | ~ r2_hidden(D_36,k1_relat_1(C_38))
      | ~ v1_funct_1(C_38)
      | ~ v1_relat_1(C_38)
      | ~ v1_funct_1(k8_relat_1(A_37,C_38))
      | ~ v1_relat_1(k8_relat_1(A_37,C_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_44,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5')
    | ~ r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | ~ r2_hidden('#skF_4',k1_relat_1(k8_relat_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_60,plain,(
    ~ r2_hidden('#skF_4',k1_relat_1(k8_relat_1('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_58,c_44])).

tff(c_76,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5')
    | ~ r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_64,c_60])).

tff(c_82,plain,
    ( ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_57,c_58,c_76])).

tff(c_83,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_86,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_83])).

tff(c_90,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_86])).

tff(c_91,plain,(
    ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_126,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_91])).

tff(c_130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_126])).

tff(c_132,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_131,plain,(
    r2_hidden('#skF_4',k1_relat_1(k8_relat_1('#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_142,plain,(
    ! [C_45,D_46,A_47] :
      ( r2_hidden(k1_funct_1(C_45,D_46),A_47)
      | ~ r2_hidden(D_46,k1_relat_1(k8_relat_1(A_47,C_45)))
      | ~ v1_funct_1(C_45)
      | ~ v1_relat_1(C_45)
      | ~ v1_funct_1(k8_relat_1(A_47,C_45))
      | ~ v1_relat_1(k8_relat_1(A_47,C_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_145,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_131,c_142])).

tff(c_148,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5')
    | ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_145])).

tff(c_149,plain,
    ( ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_148])).

tff(c_150,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_149])).

tff(c_153,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_150])).

tff(c_157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_153])).

tff(c_158,plain,(
    ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_169,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_158])).

tff(c_173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_169])).

tff(c_175,plain,(
    ~ r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_174,plain,(
    r2_hidden('#skF_4',k1_relat_1(k8_relat_1('#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_179,plain,(
    ! [D_51,C_52,A_53] :
      ( r2_hidden(D_51,k1_relat_1(C_52))
      | ~ r2_hidden(D_51,k1_relat_1(k8_relat_1(A_53,C_52)))
      | ~ v1_funct_1(C_52)
      | ~ v1_relat_1(C_52)
      | ~ v1_funct_1(k8_relat_1(A_53,C_52))
      | ~ v1_relat_1(k8_relat_1(A_53,C_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_182,plain,
    ( r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_174,c_179])).

tff(c_185,plain,
    ( r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_182])).

tff(c_186,plain,
    ( ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_175,c_185])).

tff(c_187,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_197,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_187])).

tff(c_201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_197])).

tff(c_202,plain,(
    ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_206,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_202])).

tff(c_210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_206])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.32  % Computer   : n017.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % DateTime   : Tue Dec  1 09:56:46 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.23  
% 2.09/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.23  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k8_relat_1 > k1_funct_1 > #nlpp > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.09/1.23  
% 2.09/1.23  %Foreground sorts:
% 2.09/1.23  
% 2.09/1.23  
% 2.09/1.23  %Background operators:
% 2.09/1.23  
% 2.09/1.23  
% 2.09/1.23  %Foreground operators:
% 2.09/1.23  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.09/1.23  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.09/1.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.09/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.23  tff('#skF_5', type, '#skF_5': $i).
% 2.09/1.23  tff('#skF_6', type, '#skF_6': $i).
% 2.09/1.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.09/1.23  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.09/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.09/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.23  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.09/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.09/1.23  
% 2.32/1.24  tff(f_71, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k8_relat_1(B, C))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_funct_1)).
% 2.32/1.24  tff(f_37, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v1_relat_1(k8_relat_1(A, B)) & v1_funct_1(k8_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_funct_1)).
% 2.32/1.24  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 2.32/1.24  tff(f_60, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((B = k8_relat_1(A, C)) <=> ((![D]: (r2_hidden(D, k1_relat_1(B)) <=> (r2_hidden(D, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, D), A)))) & (![D]: (r2_hidden(D, k1_relat_1(B)) => (k1_funct_1(B, D) = k1_funct_1(C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_funct_1)).
% 2.32/1.24  tff(c_42, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.32/1.24  tff(c_40, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.32/1.24  tff(c_4, plain, (![A_3, B_4]: (v1_funct_1(k8_relat_1(A_3, B_4)) | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.32/1.24  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k8_relat_1(A_1, B_2)) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.32/1.24  tff(c_54, plain, (r2_hidden('#skF_4', k1_relat_1(k8_relat_1('#skF_5', '#skF_6'))) | r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.32/1.24  tff(c_57, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_54])).
% 2.32/1.24  tff(c_50, plain, (r2_hidden('#skF_4', k1_relat_1(k8_relat_1('#skF_5', '#skF_6'))) | r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.32/1.24  tff(c_58, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_50])).
% 2.32/1.24  tff(c_64, plain, (![D_36, A_37, C_38]: (r2_hidden(D_36, k1_relat_1(k8_relat_1(A_37, C_38))) | ~r2_hidden(k1_funct_1(C_38, D_36), A_37) | ~r2_hidden(D_36, k1_relat_1(C_38)) | ~v1_funct_1(C_38) | ~v1_relat_1(C_38) | ~v1_funct_1(k8_relat_1(A_37, C_38)) | ~v1_relat_1(k8_relat_1(A_37, C_38)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.32/1.24  tff(c_44, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5') | ~r2_hidden('#skF_4', k1_relat_1('#skF_6')) | ~r2_hidden('#skF_4', k1_relat_1(k8_relat_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.32/1.24  tff(c_60, plain, (~r2_hidden('#skF_4', k1_relat_1(k8_relat_1('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_58, c_44])).
% 2.32/1.24  tff(c_76, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5') | ~r2_hidden('#skF_4', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1(k8_relat_1('#skF_5', '#skF_6')) | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_64, c_60])).
% 2.32/1.24  tff(c_82, plain, (~v1_funct_1(k8_relat_1('#skF_5', '#skF_6')) | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_57, c_58, c_76])).
% 2.32/1.24  tff(c_83, plain, (~v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_82])).
% 2.32/1.24  tff(c_86, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2, c_83])).
% 2.32/1.24  tff(c_90, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_86])).
% 2.32/1.24  tff(c_91, plain, (~v1_funct_1(k8_relat_1('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_82])).
% 2.32/1.24  tff(c_126, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_4, c_91])).
% 2.32/1.24  tff(c_130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_126])).
% 2.32/1.24  tff(c_132, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_50])).
% 2.32/1.24  tff(c_131, plain, (r2_hidden('#skF_4', k1_relat_1(k8_relat_1('#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_50])).
% 2.32/1.24  tff(c_142, plain, (![C_45, D_46, A_47]: (r2_hidden(k1_funct_1(C_45, D_46), A_47) | ~r2_hidden(D_46, k1_relat_1(k8_relat_1(A_47, C_45))) | ~v1_funct_1(C_45) | ~v1_relat_1(C_45) | ~v1_funct_1(k8_relat_1(A_47, C_45)) | ~v1_relat_1(k8_relat_1(A_47, C_45)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.32/1.24  tff(c_145, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1(k8_relat_1('#skF_5', '#skF_6')) | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_131, c_142])).
% 2.32/1.24  tff(c_148, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5') | ~v1_funct_1(k8_relat_1('#skF_5', '#skF_6')) | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_145])).
% 2.32/1.24  tff(c_149, plain, (~v1_funct_1(k8_relat_1('#skF_5', '#skF_6')) | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_132, c_148])).
% 2.32/1.24  tff(c_150, plain, (~v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_149])).
% 2.32/1.24  tff(c_153, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2, c_150])).
% 2.32/1.24  tff(c_157, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_153])).
% 2.32/1.24  tff(c_158, plain, (~v1_funct_1(k8_relat_1('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_149])).
% 2.32/1.24  tff(c_169, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_4, c_158])).
% 2.32/1.24  tff(c_173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_169])).
% 2.32/1.24  tff(c_175, plain, (~r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_54])).
% 2.32/1.24  tff(c_174, plain, (r2_hidden('#skF_4', k1_relat_1(k8_relat_1('#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_54])).
% 2.32/1.24  tff(c_179, plain, (![D_51, C_52, A_53]: (r2_hidden(D_51, k1_relat_1(C_52)) | ~r2_hidden(D_51, k1_relat_1(k8_relat_1(A_53, C_52))) | ~v1_funct_1(C_52) | ~v1_relat_1(C_52) | ~v1_funct_1(k8_relat_1(A_53, C_52)) | ~v1_relat_1(k8_relat_1(A_53, C_52)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.32/1.24  tff(c_182, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1(k8_relat_1('#skF_5', '#skF_6')) | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_174, c_179])).
% 2.32/1.24  tff(c_185, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6')) | ~v1_funct_1(k8_relat_1('#skF_5', '#skF_6')) | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_182])).
% 2.32/1.24  tff(c_186, plain, (~v1_funct_1(k8_relat_1('#skF_5', '#skF_6')) | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_175, c_185])).
% 2.32/1.24  tff(c_187, plain, (~v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_186])).
% 2.32/1.24  tff(c_197, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2, c_187])).
% 2.32/1.24  tff(c_201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_197])).
% 2.32/1.24  tff(c_202, plain, (~v1_funct_1(k8_relat_1('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_186])).
% 2.32/1.24  tff(c_206, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_4, c_202])).
% 2.32/1.24  tff(c_210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_206])).
% 2.32/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.24  
% 2.32/1.24  Inference rules
% 2.32/1.24  ----------------------
% 2.32/1.24  #Ref     : 0
% 2.32/1.24  #Sup     : 21
% 2.32/1.24  #Fact    : 0
% 2.32/1.24  #Define  : 0
% 2.32/1.24  #Split   : 6
% 2.32/1.24  #Chain   : 0
% 2.32/1.24  #Close   : 0
% 2.32/1.24  
% 2.32/1.24  Ordering : KBO
% 2.32/1.24  
% 2.32/1.24  Simplification rules
% 2.32/1.24  ----------------------
% 2.32/1.24  #Subsume      : 3
% 2.32/1.24  #Demod        : 30
% 2.32/1.24  #Tautology    : 7
% 2.32/1.24  #SimpNegUnit  : 2
% 2.32/1.24  #BackRed      : 0
% 2.32/1.24  
% 2.32/1.24  #Partial instantiations: 0
% 2.32/1.24  #Strategies tried      : 1
% 2.32/1.24  
% 2.32/1.24  Timing (in seconds)
% 2.32/1.24  ----------------------
% 2.38/1.25  Preprocessing        : 0.30
% 2.38/1.25  Parsing              : 0.15
% 2.38/1.25  CNF conversion       : 0.03
% 2.38/1.25  Main loop            : 0.20
% 2.38/1.25  Inferencing          : 0.06
% 2.38/1.25  Reduction            : 0.05
% 2.38/1.25  Demodulation         : 0.04
% 2.38/1.25  BG Simplification    : 0.02
% 2.38/1.25  Subsumption          : 0.05
% 2.38/1.25  Abstraction          : 0.01
% 2.38/1.25  MUC search           : 0.00
% 2.38/1.25  Cooper               : 0.00
% 2.38/1.25  Total                : 0.53
% 2.38/1.25  Index Insertion      : 0.00
% 2.38/1.25  Index Deletion       : 0.00
% 2.38/1.25  Index Matching       : 0.00
% 2.38/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
