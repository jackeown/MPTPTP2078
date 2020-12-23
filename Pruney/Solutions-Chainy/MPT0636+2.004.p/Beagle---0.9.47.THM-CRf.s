%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:24 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   51 (  96 expanded)
%              Number of leaves         :   18 (  42 expanded)
%              Depth                    :    6
%              Number of atoms          :   97 ( 234 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,k6_relat_1(B))))
        <=> ( r2_hidden(A,k1_relat_1(C))
            & r2_hidden(k1_funct_1(C,A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
          <=> ( r2_hidden(A,k1_relat_1(C))
              & r2_hidden(k1_funct_1(C,A),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

tff(c_26,plain,
    ( r2_hidden('#skF_1',k1_relat_1(k5_relat_1('#skF_3',k6_relat_1('#skF_2'))))
    | r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_52,plain,(
    r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_30,plain,
    ( r2_hidden('#skF_1',k1_relat_1(k5_relat_1('#skF_3',k6_relat_1('#skF_2'))))
    | r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_51,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_6,plain,(
    ! [A_2] : v1_relat_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_2] : v1_funct_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1] : k1_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_74,plain,(
    ! [A_20,C_21,B_22] :
      ( r2_hidden(A_20,k1_relat_1(k5_relat_1(C_21,B_22)))
      | ~ r2_hidden(k1_funct_1(C_21,A_20),k1_relat_1(B_22))
      | ~ r2_hidden(A_20,k1_relat_1(C_21))
      | ~ v1_funct_1(C_21)
      | ~ v1_relat_1(C_21)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_80,plain,(
    ! [A_20,C_21,A_1] :
      ( r2_hidden(A_20,k1_relat_1(k5_relat_1(C_21,k6_relat_1(A_1))))
      | ~ r2_hidden(k1_funct_1(C_21,A_20),A_1)
      | ~ r2_hidden(A_20,k1_relat_1(C_21))
      | ~ v1_funct_1(C_21)
      | ~ v1_relat_1(C_21)
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_74])).

tff(c_84,plain,(
    ! [A_23,C_24,A_25] :
      ( r2_hidden(A_23,k1_relat_1(k5_relat_1(C_24,k6_relat_1(A_25))))
      | ~ r2_hidden(k1_funct_1(C_24,A_23),A_25)
      | ~ r2_hidden(A_23,k1_relat_1(C_24))
      | ~ v1_funct_1(C_24)
      | ~ v1_relat_1(C_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8,c_80])).

tff(c_20,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2')
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_3'))
    | ~ r2_hidden('#skF_1',k1_relat_1(k5_relat_1('#skF_3',k6_relat_1('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_54,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2')
    | ~ r2_hidden('#skF_1',k1_relat_1(k5_relat_1('#skF_3',k6_relat_1('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_20])).

tff(c_55,plain,(
    ~ r2_hidden('#skF_1',k1_relat_1(k5_relat_1('#skF_3',k6_relat_1('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_97,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2')
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_55])).

tff(c_106,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_51,c_52,c_97])).

tff(c_107,plain,(
    ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_107])).

tff(c_112,plain,(
    ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_111,plain,(
    r2_hidden('#skF_1',k1_relat_1(k5_relat_1('#skF_3',k6_relat_1('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_128,plain,(
    ! [C_29,A_30,B_31] :
      ( r2_hidden(k1_funct_1(C_29,A_30),k1_relat_1(B_31))
      | ~ r2_hidden(A_30,k1_relat_1(k5_relat_1(C_29,B_31)))
      | ~ v1_funct_1(C_29)
      | ~ v1_relat_1(C_29)
      | ~ v1_funct_1(B_31)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_135,plain,(
    ! [C_29,A_30,A_1] :
      ( r2_hidden(k1_funct_1(C_29,A_30),A_1)
      | ~ r2_hidden(A_30,k1_relat_1(k5_relat_1(C_29,k6_relat_1(A_1))))
      | ~ v1_funct_1(C_29)
      | ~ v1_relat_1(C_29)
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_128])).

tff(c_149,plain,(
    ! [C_35,A_36,A_37] :
      ( r2_hidden(k1_funct_1(C_35,A_36),A_37)
      | ~ r2_hidden(A_36,k1_relat_1(k5_relat_1(C_35,k6_relat_1(A_37))))
      | ~ v1_funct_1(C_35)
      | ~ v1_relat_1(C_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8,c_135])).

tff(c_156,plain,
    ( r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_111,c_149])).

tff(c_160,plain,(
    r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_156])).

tff(c_162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_160])).

tff(c_164,plain,(
    ~ r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_163,plain,(
    r2_hidden('#skF_1',k1_relat_1(k5_relat_1('#skF_3',k6_relat_1('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_168,plain,(
    ! [A_38,C_39,B_40] :
      ( r2_hidden(A_38,k1_relat_1(C_39))
      | ~ r2_hidden(A_38,k1_relat_1(k5_relat_1(C_39,B_40)))
      | ~ v1_funct_1(C_39)
      | ~ v1_relat_1(C_39)
      | ~ v1_funct_1(B_40)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_171,plain,
    ( r2_hidden('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1(k6_relat_1('#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_163,c_168])).

tff(c_174,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8,c_18,c_16,c_171])).

tff(c_176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_174])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:33:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.24  
% 2.00/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.25  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.00/1.25  
% 2.00/1.25  %Foreground sorts:
% 2.00/1.25  
% 2.00/1.25  
% 2.00/1.25  %Background operators:
% 2.00/1.25  
% 2.00/1.25  
% 2.00/1.25  %Foreground operators:
% 2.00/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.00/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.25  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.00/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.00/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.25  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.00/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.00/1.25  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.00/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.00/1.25  
% 2.16/1.27  tff(f_59, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, k6_relat_1(B)))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_funct_1)).
% 2.16/1.27  tff(f_33, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.16/1.27  tff(f_29, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.16/1.27  tff(f_48, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), k1_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_1)).
% 2.16/1.27  tff(c_26, plain, (r2_hidden('#skF_1', k1_relat_1(k5_relat_1('#skF_3', k6_relat_1('#skF_2')))) | r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.16/1.27  tff(c_52, plain, (r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_26])).
% 2.16/1.27  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.16/1.27  tff(c_16, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.16/1.27  tff(c_30, plain, (r2_hidden('#skF_1', k1_relat_1(k5_relat_1('#skF_3', k6_relat_1('#skF_2')))) | r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.16/1.27  tff(c_51, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_30])).
% 2.16/1.27  tff(c_6, plain, (![A_2]: (v1_relat_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.16/1.27  tff(c_8, plain, (![A_2]: (v1_funct_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.16/1.27  tff(c_2, plain, (![A_1]: (k1_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.16/1.27  tff(c_74, plain, (![A_20, C_21, B_22]: (r2_hidden(A_20, k1_relat_1(k5_relat_1(C_21, B_22))) | ~r2_hidden(k1_funct_1(C_21, A_20), k1_relat_1(B_22)) | ~r2_hidden(A_20, k1_relat_1(C_21)) | ~v1_funct_1(C_21) | ~v1_relat_1(C_21) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.16/1.27  tff(c_80, plain, (![A_20, C_21, A_1]: (r2_hidden(A_20, k1_relat_1(k5_relat_1(C_21, k6_relat_1(A_1)))) | ~r2_hidden(k1_funct_1(C_21, A_20), A_1) | ~r2_hidden(A_20, k1_relat_1(C_21)) | ~v1_funct_1(C_21) | ~v1_relat_1(C_21) | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_74])).
% 2.16/1.27  tff(c_84, plain, (![A_23, C_24, A_25]: (r2_hidden(A_23, k1_relat_1(k5_relat_1(C_24, k6_relat_1(A_25)))) | ~r2_hidden(k1_funct_1(C_24, A_23), A_25) | ~r2_hidden(A_23, k1_relat_1(C_24)) | ~v1_funct_1(C_24) | ~v1_relat_1(C_24))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8, c_80])).
% 2.16/1.27  tff(c_20, plain, (~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2') | ~r2_hidden('#skF_1', k1_relat_1('#skF_3')) | ~r2_hidden('#skF_1', k1_relat_1(k5_relat_1('#skF_3', k6_relat_1('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.16/1.27  tff(c_54, plain, (~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2') | ~r2_hidden('#skF_1', k1_relat_1(k5_relat_1('#skF_3', k6_relat_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_20])).
% 2.16/1.27  tff(c_55, plain, (~r2_hidden('#skF_1', k1_relat_1(k5_relat_1('#skF_3', k6_relat_1('#skF_2'))))), inference(splitLeft, [status(thm)], [c_54])).
% 2.16/1.27  tff(c_97, plain, (~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2') | ~r2_hidden('#skF_1', k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_55])).
% 2.16/1.27  tff(c_106, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_51, c_52, c_97])).
% 2.16/1.27  tff(c_107, plain, (~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 2.16/1.27  tff(c_110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_107])).
% 2.16/1.27  tff(c_112, plain, (~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_26])).
% 2.16/1.27  tff(c_111, plain, (r2_hidden('#skF_1', k1_relat_1(k5_relat_1('#skF_3', k6_relat_1('#skF_2'))))), inference(splitRight, [status(thm)], [c_26])).
% 2.16/1.27  tff(c_128, plain, (![C_29, A_30, B_31]: (r2_hidden(k1_funct_1(C_29, A_30), k1_relat_1(B_31)) | ~r2_hidden(A_30, k1_relat_1(k5_relat_1(C_29, B_31))) | ~v1_funct_1(C_29) | ~v1_relat_1(C_29) | ~v1_funct_1(B_31) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.16/1.27  tff(c_135, plain, (![C_29, A_30, A_1]: (r2_hidden(k1_funct_1(C_29, A_30), A_1) | ~r2_hidden(A_30, k1_relat_1(k5_relat_1(C_29, k6_relat_1(A_1)))) | ~v1_funct_1(C_29) | ~v1_relat_1(C_29) | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_128])).
% 2.16/1.27  tff(c_149, plain, (![C_35, A_36, A_37]: (r2_hidden(k1_funct_1(C_35, A_36), A_37) | ~r2_hidden(A_36, k1_relat_1(k5_relat_1(C_35, k6_relat_1(A_37)))) | ~v1_funct_1(C_35) | ~v1_relat_1(C_35))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8, c_135])).
% 2.16/1.27  tff(c_156, plain, (r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_111, c_149])).
% 2.16/1.27  tff(c_160, plain, (r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_156])).
% 2.16/1.27  tff(c_162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_160])).
% 2.16/1.27  tff(c_164, plain, (~r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_30])).
% 2.16/1.27  tff(c_163, plain, (r2_hidden('#skF_1', k1_relat_1(k5_relat_1('#skF_3', k6_relat_1('#skF_2'))))), inference(splitRight, [status(thm)], [c_30])).
% 2.16/1.27  tff(c_168, plain, (![A_38, C_39, B_40]: (r2_hidden(A_38, k1_relat_1(C_39)) | ~r2_hidden(A_38, k1_relat_1(k5_relat_1(C_39, B_40))) | ~v1_funct_1(C_39) | ~v1_relat_1(C_39) | ~v1_funct_1(B_40) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.16/1.27  tff(c_171, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1(k6_relat_1('#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_163, c_168])).
% 2.16/1.27  tff(c_174, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8, c_18, c_16, c_171])).
% 2.16/1.27  tff(c_176, plain, $false, inference(negUnitSimplification, [status(thm)], [c_164, c_174])).
% 2.16/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.27  
% 2.16/1.27  Inference rules
% 2.16/1.27  ----------------------
% 2.16/1.27  #Ref     : 0
% 2.16/1.27  #Sup     : 21
% 2.16/1.27  #Fact    : 0
% 2.16/1.27  #Define  : 0
% 2.16/1.27  #Split   : 4
% 2.16/1.27  #Chain   : 0
% 2.16/1.27  #Close   : 0
% 2.16/1.27  
% 2.16/1.27  Ordering : KBO
% 2.16/1.27  
% 2.16/1.27  Simplification rules
% 2.16/1.27  ----------------------
% 2.16/1.27  #Subsume      : 2
% 2.16/1.27  #Demod        : 32
% 2.16/1.27  #Tautology    : 14
% 2.16/1.27  #SimpNegUnit  : 2
% 2.16/1.27  #BackRed      : 0
% 2.16/1.27  
% 2.16/1.27  #Partial instantiations: 0
% 2.16/1.27  #Strategies tried      : 1
% 2.16/1.27  
% 2.16/1.27  Timing (in seconds)
% 2.16/1.27  ----------------------
% 2.16/1.27  Preprocessing        : 0.29
% 2.16/1.27  Parsing              : 0.16
% 2.16/1.27  CNF conversion       : 0.02
% 2.16/1.27  Main loop            : 0.19
% 2.16/1.27  Inferencing          : 0.07
% 2.16/1.27  Reduction            : 0.06
% 2.16/1.27  Demodulation         : 0.04
% 2.16/1.27  BG Simplification    : 0.01
% 2.16/1.27  Subsumption          : 0.04
% 2.16/1.27  Abstraction          : 0.01
% 2.16/1.27  MUC search           : 0.00
% 2.16/1.27  Cooper               : 0.00
% 2.16/1.27  Total                : 0.51
% 2.16/1.27  Index Insertion      : 0.00
% 2.16/1.27  Index Deletion       : 0.00
% 2.16/1.27  Index Matching       : 0.00
% 2.16/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
